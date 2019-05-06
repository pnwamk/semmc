{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
-- | Convert fragments of ASL code into Crucible CFGs
module SemMC.ASL.Crucible (
    functionToCrucible
  , Function(..)
  , procedureToCrucible
  , Procedure(..)
  , FunctionSignature
  , funcSigRepr
  , funcArgReprs
  , funcGlobalReprs
  , ProcedureSignature
  , procArgReprs
  , SomeSignature(..)
  , computeDefinitionSignature
  , computeInstructionSignature
  , Callable
  , asCallable
  , LabeledValue(..)
  , BaseGlobalVar(..)
  , Overrides(..)
  -- * Syntax extension
  , ASLExt
  , ASLApp(..)
  , ASLStmt
  , aslExtImpl
  -- * Exceptions
  , TranslationException(..)
  ) where

import qualified Control.Exception as X
import           Control.Monad.ST ( stToIO, RealWorld )
import qualified Data.Map as Map
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Text as T
import qualified Lang.Crucible.CFG.Core as CCC
import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.CFG.SSAConversion as CCS
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Types as CT
import qualified What4.BaseTypes as WT
import qualified What4.FunctionName as WFN
import qualified What4.ProgramLoc as WP

import qualified Language.ASL.Syntax as AS

import           SemMC.ASL.Extension ( ASLExt, ASLApp(..), ASLStmt(..), aslExtImpl )
import           SemMC.ASL.Exceptions ( TranslationException(..) )
import           SemMC.ASL.Signature
import           SemMC.ASL.Translation ( TranslationState(..), Overrides(..), translateStatement )

data Callable = Callable { callableName :: AS.QualifiedIdentifier
                         , callableArgs :: [AS.SymbolDecl]
                         , callableRets :: [AS.Type]
                         , callableStmts :: [AS.Stmt]
                         }

asCallable :: AS.Definition -> Maybe Callable
asCallable def =
  case def of
    AS.DefCallable { AS.callableName = name
                   , AS.callableArgs = args
                   , AS.callableRets = rets
                   , AS.callableStmts = stmts
                   } ->
      Just Callable { callableName = name
                    , callableArgs = args
                    , callableRets = rets
                    , callableStmts = stmts
                    }
    _ -> Nothing

-- | Compute the signature for a definition
--
-- FIXME: This may need to take all of the signatures of called functions to compute its own
-- signature (since they might be procedures updating state that isn't obvious)
--
-- We could avoid having to topologically sort functions and procedures by just
-- doing this in a state monad and computing signatures whenever we hit a call.
computeDefinitionSignature :: [(String, SomeSignature)] -> Callable -> IO SomeSignature
computeDefinitionSignature = undefined

computeInstructionSignature :: [(String, SomeSignature)] -> [AS.Stmt] -> IO SomeSignature
computeInstructionSignature = undefined

-- | Convert an ASL function (signature + list of statements) into a Crucible CFG
--
-- We currently assume that functions take arguments and return a single value,
-- while not accessing /any/ global state.
--
-- Note that there are a bunch of intermediate functions to set up the
-- 'CCG.Generator' monad; the real work is done in 'defineFunction'.
functionToCrucible :: (ret ~ CT.BaseToType tp)
                   => Overrides arch
                   -> FunctionSignature globals init tp
                   -> CFH.HandleAllocator RealWorld
                   -> [AS.Stmt]
                   -> IO (Function arch globals init tp)
functionToCrucible ov sig hdlAlloc stmts = do
  let argReprs = FC.fmapFC projectValue (funcArgReprs sig)
  let retRepr = CT.baseToType (funcSigRepr sig)
  hdl <- stToIO (CFH.mkHandle' hdlAlloc (WFN.functionNameFromText (funcName sig)) argReprs retRepr)
  globals <- FC.traverseFC allocateGlobal (funcGlobalReprs sig)
  let pos = WP.InternalPos
  (CCG.SomeCFG cfg0, _) <- stToIO $ CCG.defineFunction pos hdl (funcDef ov sig globals stmts)
  return Function { funcSig = sig
                  , funcCFG = CCS.toSSA cfg0
                  , funcGlobals = globals
                  }
  where
    allocateGlobal :: forall tp . LabeledValue T.Text WT.BaseTypeRepr tp -> IO (BaseGlobalVar tp)
    allocateGlobal (LabeledValue name rep) =
      stToIO (BaseGlobalVar <$> CCG.freshGlobalVar hdlAlloc name (CT.baseToType rep))

-- | A wrapper around translated functions to keep signatures with CFGs
data Function arch globals init tp =
  Function { funcSig :: FunctionSignature globals init tp
           , funcCFG :: CCC.SomeCFG (ASLExt arch) init (CT.BaseToType tp)
           , funcGlobals :: Ctx.Assignment BaseGlobalVar globals
           }

funcDef :: (ret ~ CT.BaseToType tp)
        => Overrides arch
        -> FunctionSignature globals init tp
        -> Ctx.Assignment BaseGlobalVar globals
        -> [AS.Stmt]
        -> Ctx.Assignment (CCG.Atom s) init
        -> (TranslationState s, CCG.Generator (ASLExt arch) h s TranslationState ret (CCG.Expr (ASLExt arch) s ret))
funcDef ov sig globals stmts args = (funcInitialState sig globals args, defineFunction ov sig stmts args)

funcInitialState :: forall init tp s globals
                  . FunctionSignature globals init tp
                 -> Ctx.Assignment BaseGlobalVar globals
                 -> Ctx.Assignment (CCG.Atom s) init
                 -> TranslationState s
funcInitialState sig globals args =
  TranslationState { tsArgAtoms = Ctx.forIndex (Ctx.size args) addArgumentAtom Map.empty
                   , tsVarRefs = Map.empty
                   , tsGlobals = FC.foldrFC addGlobal Map.empty globals
                   , tsFunctionSigs = error "func: tsFunctionSigs"
                   }
  where
    addArgumentAtom :: forall tp0
                     . Map.Map T.Text (Some (CCG.Atom s))
                    -> Ctx.Index init tp0
                    -> Map.Map T.Text (Some (CCG.Atom s))
    addArgumentAtom m idx =
      let atom = args Ctx.! idx
          LabeledValue argName _ = funcArgReprs sig Ctx.! idx
      in Map.insert argName (Some atom) m
    addGlobal (BaseGlobalVar gv) m =
      Map.insert (CCG.globalName gv) (Some gv) m


defineFunction :: forall ret tp init h s arch globals
                . (ret ~ CT.BaseToType tp)
               => Overrides arch
               -> FunctionSignature globals init tp
               -> [AS.Stmt]
               -> Ctx.Assignment (CCG.Atom s) init
               -> CCG.Generator (ASLExt arch) h s TranslationState ret (CCG.Expr (ASLExt arch) s ret)
defineFunction ov sig stmts args = do
  -- FIXME: Put args into the environment as locals (that can be read from)
  --
  -- We have the assignment of atoms available, but the arguments will be
  -- referenced by /name/ by ASL statements.
  mapM_ (translateStatement ov (CT.baseToType (funcSigRepr sig))) stmts
  -- Note: we shouldn't actually get here, as we should have called returnFromFunction while
  -- translating.
  X.throw (NoReturnInFunction (SomeFunctionSignature sig))

data Procedure arch globals init =
  Procedure { procSig :: ProcedureSignature globals init
            , procCFG :: CCC.SomeCFG (ASLExt arch) init (CT.SymbolicStructType globals)
            , procGlobals :: Ctx.Assignment BaseGlobalVar globals
            }

-- | This type alias is a constraint relating the 'globals' (base types) to the
-- actual return type in terms of Crucible types
--
-- The constraint is simple but a bit annoying to write
type ReturnsGlobals ret globals = (ret ~ CT.SymbolicStructType globals)

-- | Translate an ASL procedure (signature plus statements) into a Crucible procedure
--
-- We bundle up the signature, CFG, and allocated globals.  We need to keep the
-- globals around for re-use during simulation.
--
-- The overall strategy is to allocate a Crucible global variable for each part
-- of the CPU state (i.e., machine register) that could be read or written by
-- the procedure.  We'll use symbolic simulation to determine the effect of the
-- procedure on each register.
--
-- Every procedure takes its natural argument list plus one extra argument: the
-- register file (a struct of all of the register values).  When the procedure
-- starts, we'll copy all of the values from the register struct into the globals.
--
-- We assume that all procedures have void type in ASL.  We translate all
-- procedures to return a single argument: a struct with the updated register
-- values.
--
-- NOTE: The signature computation MUST account for the UNPREDICTABLE and
-- UNDEFINED globals.  They may be accessed during the translation and must be
-- available in the 'TranslationState'
procedureToCrucible :: forall arch init globals ret
                     . (ReturnsGlobals ret globals)
                    => Overrides arch
                    -> ProcedureSignature globals init
                    -> CFH.HandleAllocator RealWorld
                    -> [AS.Stmt]
                    -> IO (Procedure arch globals init)
procedureToCrucible ov sig hdlAlloc stmts = do
  let argReprs = FC.fmapFC projectValue (procArgReprs sig)
  let retRepr = procSigRepr sig
  hdl <- stToIO (CFH.mkHandle' hdlAlloc (WFN.functionNameFromText (procName sig)) argReprs retRepr)
  globals <- FC.traverseFC allocateGlobal (procGlobalReprs sig)
  let pos = WP.InternalPos
  (CCG.SomeCFG cfg0, _) <- stToIO $ CCG.defineFunction pos hdl (procDef ov sig globals stmts)
  return Procedure { procSig = sig
                   , procCFG = CCS.toSSA cfg0
                   , procGlobals = globals
                   }
  where
    allocateGlobal :: forall tp . LabeledValue T.Text WT.BaseTypeRepr tp -> IO (BaseGlobalVar tp)
    allocateGlobal (LabeledValue name rep) =
      stToIO (BaseGlobalVar <$> CCG.freshGlobalVar hdlAlloc name (CT.baseToType rep))

procDef :: (ReturnsGlobals ret globals)
        => Overrides arch
        -> ProcedureSignature globals init
        -> Ctx.Assignment BaseGlobalVar globals
        -> [AS.Stmt]
        -> Ctx.Assignment (CCG.Atom s) init
        -> (TranslationState s, CCG.Generator (ASLExt arch) h s TranslationState ret (CCG.Expr (ASLExt arch) s ret))
procDef ov sig globals stmts args =
  (procInitialState sig globals args, defineProcedure ov sig globals stmts args)

procInitialState :: forall init globals s
                  . ProcedureSignature globals init
                 -> Ctx.Assignment BaseGlobalVar globals
                 -> Ctx.Assignment (CCG.Atom s) init
                 -> TranslationState s
procInitialState sig globals args =
  TranslationState { tsArgAtoms = Ctx.forIndex (Ctx.size args) addArgument Map.empty
                   , tsVarRefs = Map.empty
                   , tsGlobals = FC.foldrFC addGlobal Map.empty globals
                   , tsFunctionSigs = error "proc: tsFunctionSigs"
                   }
  where
    addArgument :: forall tp
                 . Map.Map T.Text (Some (CCG.Atom s))
                -> Ctx.Index init tp
                -> Map.Map T.Text (Some (CCG.Atom s))
    addArgument m idx =
      Map.insert (projectLabel (procArgReprs sig Ctx.! idx)) (Some (args Ctx.! idx)) m
    addGlobal (BaseGlobalVar gv) m =
      Map.insert (CCG.globalName gv) (Some gv) m

defineProcedure :: (ReturnsGlobals ret globals)
                => Overrides arch
                -> ProcedureSignature globals init
                -> Ctx.Assignment BaseGlobalVar globals
                -> [AS.Stmt]
                -> Ctx.Assignment (CCG.Atom s) init
                -> CCG.Generator (ASLExt arch) h s TranslationState ret (CCG.Expr (ASLExt arch) s ret)
defineProcedure ov sig baseGlobals stmts args = do
  mapM_ (translateStatement ov (procSigRepr sig)) stmts
  retExpr <- CCG.extensionStmt (GetRegState (FC.fmapFC projectValue (procGlobalReprs sig)) baseGlobals)
  if | Just Refl <- testEquality (CCG.exprType retExpr) (procSigRepr sig) ->
       return retExpr
     | otherwise -> X.throw (UnexpectedProcedureReturn (procSigRepr sig) (CCG.exprType retExpr))

{- Note [Call Translation]

There are two types of calls in ASL: functions and procedures.

Functions are simple and are already purely functional, and thus need no additional support.

Procedures are more complicated, as they return no values but instead update processor state through
side effects.  Our challenge in this code is to turn these imperative procedures into pure
functions.  The strategy will be to arrange it so that, in addition to its natural set of
parameters, each procedure takes an entire machine state as a BaseStruct.  It will also return an
entire BaseStruct register state.

At procedure initialization time, the procedure will copy all of its input machine state into a set
of locals (Crucible or globals).  Before calling a procedure, the caller takes a snapshot of the current
machine state (from the refs) to construct the BaseStruct to pass to the callee.  After a procedure
call returns, the caller will assign the contents of the register state back to its locals (refs).

Question: do we need any additional components to the return value of procedures?  Anything that
isn't a global is local, and local modifications can't be reflected to callers.

Note that we have an additional unusual constraint: we need to represent calls
in any context as uninterpreted functions, since we don't want to eagerly expand
definitions of functions.  Doing so produces an enormous code explosion that we
can't handle.  Crucible can support uninterpreted functions via what4; however,
they aren't exactly first class.  Uninterpreted functions can only take as
arguments and return base types.  Crucible doesn't have great support for
working with base types.

Beyond the normal machine registers, we introduce two extra state variables:
- Undefined
- Unpredictable

Each is a boolean that starts as False and is switched to True if an instruction
has undefined or unpredictable behavior, respectively.

-}
