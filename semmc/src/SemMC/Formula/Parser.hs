{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | A parser for an s-expression representation of formulas
module SemMC.Formula.Parser
  ( operandVarPrefix
  , literalVarPrefix
  , argumentVarPrefix
  , readFormula
  , readFormulaFromFile
  , readDefinedFunction
  , readDefinedFunctionFromFile
  ) where

import qualified Control.Monad.Except as E
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Control.Monad.Reader as MR
import           Control.Monad ( when )
import           Data.Foldable ( foldrM )
import           Data.Kind
import qualified Data.Map as Map
import qualified Data.SCargot.Repr as SC
import           Data.Semigroup
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Text.Printf ( printf )
import qualified Data.Set as Set
import           GHC.TypeLits ( Symbol )
import           Data.Proxy ( Proxy(..) )

import qualified Data.Parameterized.Ctx as Ctx
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some ( Some(..), mapSome, viewSome )
import qualified Data.Parameterized.List as SL
import           Data.Parameterized.TraversableFC ( traverseFC, allFC )
import qualified Data.Parameterized.Map as MapF
import           What4.BaseTypes
import qualified Lang.Crucible.Backend as S
import qualified What4.Interface as S
import           What4.Symbol ( userSymbol )
import qualified What4.Serialize.Parser as WSP
import           What4.Serialize.SETokens

import qualified Data.Type.List as TL -- in this package
import qualified SemMC.Architecture as A
import qualified SemMC.Architecture.Location as L
import qualified SemMC.BoundVar as BV
import           SemMC.Formula.Env ( FormulaEnv(..), SomeSome(..) )
import           SemMC.Formula.Formula
import qualified SemMC.Util as U

import           Prelude

data OperandTypeWrapper (arch :: Type) :: TL.TyFun Symbol BaseType -> Type
type instance TL.Apply (OperandTypeWrapper arch) s = A.OperandType arch s
type OperandTypes arch sh = TL.Map (OperandTypeWrapper arch) sh

-- | A counterpart to 'SemMC.Formula.Parameter' for use in the parser, where we
-- might know only a parameter's base type (such as when parsing a defined
-- function).
data ParsedParameter arch (tps :: [BaseType]) (tp :: BaseType) where
  ParsedOperandParameter :: BaseTypeRepr tp -> SL.Index tps tp
                         -> ParsedParameter arch tps tp
  ParsedLiteralParameter :: L.Location arch tp -> ParsedParameter arch tps tp

-- Translating from 'SL.Index'   on 'BaseType' to 'SL.Index' on 'Symbol' is
-- tricky.  Need this view to show that when we translate some @SL.Index tps tp@
-- to an @SL.Index sh s@, the symbol @s@ maps to the base type @tp@ (assuming
-- that @tps ~ OperandTypes arch sh@).
data IndexByArchType arch sh tp where
  IndexByArchType :: A.OperandType arch s ~ tp => SL.Index sh s -> IndexByArchType arch sh tp

-- TODO This is all very silly. It's an expensive identity function.
indexByArchType :: proxy arch
                -> A.ShapeRepr arch sh
                -> SL.Index (OperandTypes arch sh) tp
                -> IndexByArchType arch sh tp
indexByArchType _ SL.Nil _ = error "impossible"
indexByArchType _ (_ SL.:< _) SL.IndexHere = IndexByArchType SL.IndexHere
indexByArchType p (_ SL.:< shapeRepr) (SL.IndexThere ix) =
  case indexByArchType p shapeRepr ix of
    IndexByArchType ix' -> IndexByArchType (SL.IndexThere ix')

toParameter :: forall arch sh tp
             . A.ShapeRepr arch sh
            -> ParsedParameter arch (OperandTypes arch sh) tp
            -> Parameter arch sh tp
toParameter shapeRepr (ParsedOperandParameter tpRepr ix) =
  case indexByArchType (Proxy @arch) shapeRepr ix of
    IndexByArchType ix' -> OperandParameter tpRepr ix'
toParameter _ (ParsedLiteralParameter loc) =
  LiteralParameter loc

-- * First pass of parsing turns the raw text into s-expressions.
--   This pass is handled by the code in SemMC.Formula.SELang

-- * Second pass of parsing: turning the s-expressions into symbolic expressions
-- and the overall templated formula

-- ** Utility functions

-- | Utility function for contextualizing errors. Prepends the given prefix
-- whenever an error is thrown.
prefixError :: (Monoid e, E.MonadError e m) => e -> m a -> m a
prefixError prefix act = E.catchError act (E.throwError . mappend prefix)

-- | Utility function for lifting a 'Maybe' into a 'MonadError'
fromMaybeError :: (E.MonadError e m) => e -> Maybe a -> m a
fromMaybeError err = maybe (E.throwError err) return

-- ** Parsing operands

-- | Data about the operands pertinent after parsing: their name and their type.
data OpData (tp :: BaseType) where
  OpData :: String -> BaseTypeRepr tp -> OpData tp

buildOperandList' :: forall m proxy arch tps
                   . (E.MonadError String m, A.Architecture arch)
                  => proxy arch
                  -> A.ShapeRepr arch tps
                  -> SC.SExpr FAtom
                  -> m (SL.List OpData (OperandTypes arch tps))
buildOperandList' proxy rep atm =
  case rep of
    SL.Nil ->
      case atm of
        SC.SNil -> return SL.Nil
        _ -> E.throwError $ "Expected Nil but got " ++ show atm
    r SL.:< rep' ->
      case atm of
        SC.SNil -> E.throwError $ "Expected entry but got Nil"
        SC.SAtom _ -> E.throwError $ "Expected SCons but got SAtom: " ++ show atm
        SC.SCons s rest -> do
          let SC.SCons (SC.SAtom (AIdent operand)) (SC.SAtom (AQuoted ty)) = s
          when (A.operandTypeReprSymbol proxy r /= ty) $
            E.throwError $ "unknown reference: " ++ show ty
          rest' <- buildOperandList' proxy rep' rest
          let tyRepr = A.shapeReprToTypeRepr proxy r
          return $ (OpData operand tyRepr) SL.:< rest'

buildArgumentList' :: forall m
                    . (E.MonadError String m)
                   => SC.SExpr FAtom
                   -> m (Some (SL.List OpData))
buildArgumentList' sexpr =
  case sexpr of
    SC.SNil -> return $ Some (SL.Nil)
    SC.SAtom _ -> E.throwError $ "Expected SNil or SCons but got SAtom: " ++ show sexpr
    SC.SCons s rest -> do
      (operand, tyRaw) <- case s of
        SC.SCons (SC.SAtom (AIdent operand)) (SC.SCons ty SC.SNil)
          -> return (operand, ty)
        _ -> E.throwError $ "Expected (operand . 'type) pair: " ++ show s
      Some tp <- readBaseType tyRaw
      Some rest' <- buildArgumentList' rest
      return $ Some ((OpData operand tp) SL.:< rest')

readBaseType :: forall m
              . (E.MonadError String m)
             => SC.SExpr FAtom
             -> m (Some BaseTypeRepr)
readBaseType sexpr =
  case sexpr of
    SC.SAtom (AQuoted atom) ->
      case atom of
        "bool" -> return $ Some BaseBoolRepr
        "nat" -> return $ Some BaseNatRepr
        "int" -> return $ Some BaseIntegerRepr
        "real" -> return $ Some BaseRealRepr
        "string" -> return $ Some (BaseStringRepr UnicodeRepr)
        "complex" -> return $ Some BaseComplexRepr
        _ -> panic
    SC.SCons (SC.SAtom (AQuoted "bv")) (SC.SCons (SC.SAtom (AInt w)) SC.SNil)
      | Just (Some wRepr) <- someNat w
      , Just LeqProof <- testLeq (knownNat @1) wRepr
        -> return $ Some (BaseBVRepr wRepr)
      | otherwise
        -> panic
    SC.SCons (SC.SAtom (AQuoted "struct")) (SC.SCons args SC.SNil) -> do
      Some tps <- readBaseTypes args
      return $ Some (BaseStructRepr tps)
    SC.SCons (SC.SAtom (AQuoted "array"))
             (SC.SCons ixArgs (SC.SCons tpArg SC.SNil)) -> do
      Some ixs <- readBaseTypes ixArgs
      Some tp <- readBaseType tpArg
      case Ctx.viewAssign ixs of
        Ctx.AssignEmpty -> E.throwError $ "array type has no indices: " ++ show sexpr
        Ctx.AssignExtend _ _ -> return $ Some (BaseArrayRepr ixs tp)
    _ -> panic
  where
    panic = E.throwError $ "unknown base type: " ++ show sexpr

readBaseTypes :: forall m
              . (E.MonadError String m)
              => SC.SExpr FAtom
              -> m (Some (Ctx.Assignment BaseTypeRepr))
readBaseTypes sexpr0 =
  go sexpr0 Ctx.empty
  where
    -- Be tail recursive to reverse list
    go :: SC.SExpr FAtom
       -> Ctx.Assignment BaseTypeRepr sh
       -> m (Some (Ctx.Assignment BaseTypeRepr))
    go sexpr acc =
      case sexpr of
        SC.SNil -> return (Some acc)
        SC.SCons s rest -> do
          Some tp <- readBaseType s
          go rest (Ctx.extend acc tp)
        SC.SAtom _ -> E.throwError $
          "expected list of base types: " ++ show sexpr

-- ** Parsing parameters
--
-- By which I mean, handling occurrences in expressions of either operands or
-- literals.

-- | Low-level representation of a parameter: no checking done yet on whether
-- they're valid yet or not.
data RawParameter = RawOperand String
                  | RawLiteral String
                  deriving (Show, Eq, Ord)

operandVarPrefix :: String
operandVarPrefix = "op_"

literalVarPrefix :: String
literalVarPrefix = "lit_"

argumentVarPrefix :: String
argumentVarPrefix = "arg_"

-- | Parses the name of a parameter and whether it's an operand or a literal.
readRawParameter :: (E.MonadError String m) => FAtom -> m RawParameter
readRawParameter (AIdent name)
  | Right _ <- userSymbol (operandVarPrefix ++ name) = return (RawOperand name)
  | otherwise = E.throwError $ printf "%s is not a valid parameter name" name
readRawParameter (AQuoted name)
  | Right _ <- userSymbol (literalVarPrefix ++ name) = return (RawLiteral name)
  | otherwise = E.throwError $ printf "%s is not a valid parameter name" name
readRawParameter a = E.throwError $ printf "expected parameter, found %s" (show a)

-- | Short-lived type that just stores an index with its corresponding type
-- representation, with the type parameter ensuring they correspond to one another.
data IndexWithType (sh :: [BaseType]) (tp :: BaseType) where
  IndexWithType :: BaseTypeRepr tp -> SL.Index sh tp -> IndexWithType sh tp

-- | Look up a name in the given operand list, returning its index and type if found.
findOpListIndex :: String -> SL.List OpData sh -> Maybe (Some (IndexWithType sh))
findOpListIndex _ SL.Nil = Nothing
findOpListIndex x ((OpData name tpRepr) SL.:< rest)
  | x == name = Just $ Some (IndexWithType tpRepr SL.IndexHere)
  | otherwise = mapSome incrIndex <$> findOpListIndex x rest
      where incrIndex (IndexWithType tpRepr' idx) = IndexWithType tpRepr' (SL.IndexThere idx)

-- | Parse a single parameter, given the list of operands to use as a lookup.
readParameter :: (E.MonadError String m, A.Architecture arch) => proxy arch -> SL.List OpData tps -> FAtom -> m (Some (ParsedParameter arch tps))
readParameter _ oplist atom =
  readRawParameter atom >>= \case
    RawOperand op ->
      maybe (E.throwError $ printf "couldn't find operand %s" op)
            (viewSome (\(IndexWithType tpRepr idx) -> return $ Some (ParsedOperandParameter tpRepr idx)))
            (findOpListIndex op oplist)
    RawLiteral lit ->
      maybe (E.throwError $ printf "%s is an invalid literal for this arch" lit)
            (return . viewSome (Some . ParsedLiteralParameter))
            (A.readLocation lit)

-- | Parses the input list, e.g., @(ra rb 'ca)@
readInputs :: forall m (arch :: Type) (tps :: [BaseType])
            . (E.MonadError String m,
               A.Architecture arch)
           => SL.List OpData tps
           -> SC.SExpr FAtom
           -> m [Some (ParsedParameter arch tps)]
readInputs _ SC.SNil = return []
readInputs oplist (SC.SCons (SC.SAtom p) rest) = do
  p' <- readParameter Proxy oplist p
  rest' <- readInputs oplist rest
  return $ p' : rest'
readInputs _ i = E.throwError $ "malformed input list: " <> show i

-- ** Parsing definitions

-- | "Global" data stored in the Reader monad throughout parsing the definitions.
data DefsInfo sym arch tps = DefsInfo
                             { getSym :: sym
                             -- ^ SymInterface/ExprBuilder used to build up symbolic
                             -- expressions while parsing the definitions.
                             , getEnv :: FormulaEnv sym arch
                             -- ^ Global formula environment
                             , getLitLookup :: forall tp. A.Location arch tp -> Maybe (S.SymExpr sym tp)
                             -- ^ Function used to retrieve the expression
                             -- corresponding to a given literal.
                             , getOpVarList :: SL.List (S.BoundVar sym) tps
                             -- ^ ShapedList used to retrieve the variable
                             -- corresponding to a given literal.
                             , getOpNameList :: SL.List OpData tps
                             -- ^ ShapedList used to look up the index given an
                             -- operand's name.
                             }


-- | Parse the whole definitions expression, e.g.:
--
-- > ((rt . (bvadd ra rb))
-- >  ('ca . #b1))
--
readDefs :: forall sym m arch sh
          . (S.IsSymExprBuilder sym,
             Monad m,
             E.MonadError String m,
             A.Architecture arch,
             MR.MonadReader (DefsInfo sym arch (OperandTypes arch sh)) m,
             MonadIO m,
             ShowF (S.SymExpr sym))
         => A.ShapeRepr arch sh
         -> SC.SExpr FAtom
         -> m (MapF.MapF (Parameter arch sh) (S.SymExpr sym))
readDefs _ SC.SNil = return MapF.empty
readDefs shapeRepr (SC.SCons
                    (SC.SCons
                      (SC.SAtom p)
                      (SC.SCons
                       (SC.SCons (SC.SAtom (AIdent "let"))
                        (SC.SCons bindings (SC.SCons body SC.SNil)))
                        SC.SNil))
                     rest) = do
  oplist <- MR.reader getOpNameList
  Some param <- mapSome (toParameter shapeRepr) <$> readParameter (Proxy @arch) oplist p
  Some def <- WSP.readLetExpr bindings body
  Refl <- fromMaybeError ("mismatching types of parameter and expression for " ++ showF param) $
            testEquality (paramType param) (S.exprType def)
  rest' <- prefixError (", defining " <> showF def <> " ... ") $ readDefs shapeRepr rest
  return $ MapF.insert param def rest'
readDefs shapeRepr (SC.SCons (SC.SCons (SC.SCons mUF (SC.SCons (SC.SAtom p) SC.SNil))
                              (SC.SCons
                               (SC.SCons (SC.SAtom (AIdent "let"))
                                (SC.SCons bindings (SC.SCons body SC.SNil)))
                               SC.SNil))
                     rest)
  | Just funcName <- matchUF mUF = prefixError (", processing uninterpreted function " <> show funcName <> " ... ") $ do
    oplist <- MR.reader getOpNameList
    Some param <- mapSome (toParameter shapeRepr) <$> readParameter (Proxy @arch) oplist p
    fns <- MR.reader (envFunctions . getEnv)
    case Map.lookup funcName fns of
      Just (_, Some rep) -> do
        Some def <- WSP.readLetExpr bindings body
        Refl <- fromMaybeError ("mismatching types of parameter and expression for " ++ showF param) $
                  testEquality rep (S.exprType def)
        rest' <- readDefs shapeRepr rest
        case param of
          LiteralParameter {} -> E.throwError "Literals are not allowed as arguments to parameter functions"
          FunctionParameter {} -> E.throwError "Nested parameter functions are not allowed"
          OperandParameter orep oix ->
            return $ MapF.insert (FunctionParameter funcName (WrappedOperand orep oix) rep) def rest'
      _ -> E.throwError ("Missing type repr for uninterpreted function " ++ show funcName)
readDefs _ _ = E.throwError "invalid defs structure"

matchUF :: SC.SExpr FAtom -> Maybe String
matchUF se =
  case se of
    SC.SCons (SC.SAtom (AIdent "_"))
             (SC.SCons (SC.SAtom (AIdent "call"))
                       (SC.SCons (SC.SAtom (AString fnName))
                                 SC.SNil)) -> Just fnName
    _ -> Nothing

-- | Parse the whole definition of a templated formula, inside an appropriate
-- monad.
readFormula' :: forall sym arch (sh :: [Symbol]) m.
                (S.IsSymExprBuilder sym,
                 E.MonadError String m,
                 MonadIO m,
                 A.Architecture arch,
                 ShowF (S.SymExpr sym),
                 U.HasLogCfg)
             => sym
             -> FormulaEnv sym arch
             -> A.ShapeRepr arch sh
             -> T.Text
             -> m (ParameterizedFormula sym arch sh)
readFormula' sym env repr text = do
  sexpr <- case parseLL text of
             Left err -> E.throwError err
             Right res -> return res
  let firstLine = show $ fmap T.unpack $ take 1 $ T.lines text
  liftIO $ U.logIO U.Info $ "readFormula' of " ++ (show $ T.length text) ++ " bytes " ++ firstLine
  liftIO $ U.logIO U.Debug $ "readFormula' shaperepr " ++ (A.showShapeRepr (Proxy @arch) repr)
  -- Extract the raw s-expressions for the three components.
  (opsRaw, inputsRaw, defsRaw) <- case sexpr of
    SC.SCons (SC.SCons (SC.SAtom (AIdent "operands")) (SC.SCons ops SC.SNil))
      (SC.SCons (SC.SCons (SC.SAtom (AIdent "in")) (SC.SCons inputs SC.SNil))
       (SC.SCons (SC.SCons (SC.SAtom (AIdent "defs")) (SC.SCons defs SC.SNil))
         SC.SNil))
      -> return (ops, inputs, defs)
    _ -> E.throwError "invalid top-level structure"

  -- Most of the following bindings have type annotations not because inference
  -- fails, but because with all the type-level hackery we have going on, it
  -- greatly helps human comprehension.

  -- Build the operand list from the given s-expression, validating that it
  -- matches the correct shape as we go.
  let strShape = A.showShapeRepr (Proxy @arch) repr
  operands :: SL.List OpData (OperandTypes arch sh)
    <- prefixError ("invalid operand structure (expected " ++ strShape ++
                    ") from " ++ show opsRaw) $
       buildOperandList' (Proxy @arch) repr opsRaw

  inputs :: [Some (ParsedParameter arch (OperandTypes arch sh))]
    <- readInputs @m @arch @(OperandTypes arch sh) operands inputsRaw

  let mkOperandVar :: forall tp. OpData tp -> m (S.BoundVar sym tp)
      mkOperandVar (OpData name tpRepr) =
        let symbol = U.makeSymbol (operandVarPrefix ++ name)
        in liftIO $ S.freshBoundVar sym symbol tpRepr

  opVarList :: SL.List (S.BoundVar sym) (OperandTypes arch sh)
    <- traverseFC mkOperandVar @(OperandTypes arch sh) operands

  -- NOTE: At the moment, we just trust that the semantics definition declares
  -- the correct input operands; instead of validating it, we generate BoundVars
  -- for *all* inputs (partially because it is unclear how to treat immediates
  -- -- do they count as inputs?).

  let mkLiteralVar :: forall tp. BaseTypeRepr tp -> A.Location arch tp -> m (S.BoundVar sym tp)
      mkLiteralVar tpRepr loc =
        let symbol = U.makeSymbol (literalVarPrefix ++ showF loc)
        in liftIO $ S.freshBoundVar sym symbol tpRepr

      buildLitVarMap :: Some (ParsedParameter arch (OperandTypes arch sh))
                     -> MapF.MapF (A.Location arch) (S.BoundVar sym)
                     -> m (MapF.MapF (A.Location arch) (S.BoundVar sym))
      buildLitVarMap (Some (ParsedLiteralParameter loc)) m = (\v -> MapF.insert loc v m) <$> mkLiteralVar (A.locationType loc) loc
      buildLitVarMap (Some (ParsedOperandParameter _ _))        m = return m

  litVars :: MapF.MapF (A.Location arch) (S.BoundVar sym)
    <- foldrM buildLitVarMap MapF.empty inputs

  defs <- MR.runReaderT (readDefs repr defsRaw) $
            (DefsInfo { getSym = sym
                      , getEnv = env
                      , getLitLookup = \loc -> S.varExpr sym <$> flip MapF.lookup litVars loc
                      , getOpVarList = opVarList
                      , getOpNameList = operands
                      })

  let finalInputs :: [Some (Parameter arch sh)]
      finalInputs = mapSome (toParameter repr) <$> inputs
      finalOpVarList :: SL.List (BV.BoundVar sym arch) sh
      finalOpVarList =
        -- Wrap each operand variable using 'BV.BoundVar'
        TL.mapFromMapped (Proxy @(OperandTypeWrapper arch)) BV.BoundVar repr opVarList

  return $
    ParameterizedFormula { pfUses = Set.fromList finalInputs
                         , pfOperandVars = finalOpVarList
                         , pfLiteralVars = litVars
                         , pfDefs = defs
                         }

-- | Parse the definition of a templated formula.
readFormula :: (S.IsSymExprBuilder sym,
                A.Architecture arch,
                ShowF (S.SymExpr sym),
                U.HasLogCfg)
            => sym
            -> FormulaEnv sym arch
            -> A.ShapeRepr arch sh
            -> T.Text
            -> IO (Either String (ParameterizedFormula sym arch sh))
readFormula sym env repr text = E.runExceptT $ readFormula' sym env repr text

-- | Read a templated formula definition from file, then parse it.
readFormulaFromFile :: (S.IsSymExprBuilder sym,
                        A.Architecture arch,
                        ShowF (S.SymExpr sym),
                        U.HasLogCfg)
                    => sym
                    -> FormulaEnv sym arch
                    -> A.ShapeRepr arch sh
                    -> FilePath
                    -> IO (Either String (ParameterizedFormula sym arch sh))
readFormulaFromFile sym env repr fp = do
  liftIO $ U.logIO U.Info $ "readFormulaFromFile " ++ fp
  readFormula sym env repr =<< T.readFile fp

-- | Parse the whole definition of a defined function, inside an appropriate
-- monad.
readDefinedFunction' :: forall sym arch m.
                        (S.IsExprBuilder sym,
                         S.IsSymInterface sym,
                         E.MonadError String m,
                         MonadIO m,
                         A.Architecture arch,
                         ShowF (S.SymExpr sym),
                         U.HasLogCfg)
                     => sym
                     -> FormulaEnv sym arch
                     -> T.Text
                     -> m (Some (FunctionFormula sym))
readDefinedFunction' sym env text = do
  sexpr <- case parseLL text of
             Left err -> E.throwError err
             Right res -> return res
  let firstLine = show $ fmap T.unpack $ take 1 $ T.lines text
  liftIO $ U.logIO U.Info $
    "readDefinedFunction' of " ++ (show $ T.length text) ++ " bytes " ++ firstLine
  -- Extract the raw s-expressions for the four components.
  (name, argsRaw, retTypeRaw, bodyRaw) <- case sexpr of
    SC.SCons (SC.SCons (SC.SAtom (AIdent "function"))
              (SC.SCons (SC.SAtom (AIdent name)) SC.SNil))
      (SC.SCons (SC.SCons (SC.SAtom (AIdent "arguments")) (SC.SCons args SC.SNil))
       (SC.SCons (SC.SCons (SC.SAtom (AIdent "return")) (SC.SCons retType SC.SNil))
         (SC.SCons (SC.SCons (SC.SAtom (AIdent "body"))
                    (SC.SCons (SC.SCons (SC.SAtom (AIdent "let"))
                               (SC.SCons bindings (SC.SCons bodyRaw SC.SNil)))
                      SC.SNil))
           SC.SNil)))
      -> return (name, args, retType, bodyRaw)
    _ -> E.throwError "invalid top-level structure"

  -- Most of the following bindings have type annotations not because inference
  -- fails, but because with all the type-level hackery we have going on, it
  -- greatly helps human comprehension.

  -- Build the argument list from the given s-expression. Unlike with a formula,
  -- we don't know the arguments' types beforehand.
  Some (arguments :: SL.List OpData sh)
    <- buildArgumentList' argsRaw

  Some (retTypeRepr :: BaseTypeRepr retType)
    <- readBaseType retTypeRaw

  let mkArgumentVar :: forall tp. OpData tp -> m (S.BoundVar sym tp)
      mkArgumentVar (OpData varName tpRepr) =
        let symbol = U.makeSymbol (argumentVarPrefix ++ varName)
        in liftIO $ S.freshBoundVar sym symbol tpRepr

  argVarList :: SL.List (S.BoundVar sym) sh
    <- traverseFC mkArgumentVar arguments

  argTypeReprs :: SL.List BaseTypeRepr sh
    <- traverseFC (\(OpData _ tpRepr) -> return tpRepr) arguments

  Some body <- MR.runReaderT (WSP.readLetExpr bindings bodyRaw) $
    DefsInfo { getSym = sym
             , getEnv = env
             , getLitLookup = const Nothing
             , getOpVarList = argVarList
             , getOpNameList = arguments
             }

  let actualTypeRepr = S.exprType body
  Refl <- case testEquality retTypeRepr actualTypeRepr of
    Just r -> return r
    Nothing -> E.throwError $
      "Body has wrong type: expected " ++ show retTypeRepr ++
      " but found " ++ show actualTypeRepr

  let symbol = U.makeSymbol name
      argVarAssignment = TL.toAssignmentFwd argVarList
      expand args = allFC S.baseIsConcrete args

  symFn <- liftIO $ S.definedFn sym symbol argVarAssignment body expand
  return $ Some (FunctionFormula { ffName = name
                                 , ffArgTypes = argTypeReprs
                                 , ffArgVars = argVarList
                                 , ffRetType = retTypeRepr
                                 , ffDef = symFn })

-- | Parse the definition of a templated formula.
readDefinedFunction :: (S.IsExprBuilder sym,
                        S.IsSymInterface sym,
                        A.Architecture arch,
                        ShowF (S.SymExpr sym),
                        U.HasLogCfg)
                    => sym
                    -> FormulaEnv sym arch
                    -> T.Text
                    -> IO (Either String (Some (FunctionFormula sym)))
readDefinedFunction sym env text = E.runExceptT $ readDefinedFunction' sym env text

-- | Read a defined function definition from a file, then parse it.
readDefinedFunctionFromFile :: (S.IsExprBuilder sym,
                                S.IsSymInterface sym,
                                A.Architecture arch,
                                ShowF (S.SymExpr sym),
                                U.HasLogCfg)
                    => sym
                    -> FormulaEnv sym arch
                    -> FilePath
                    -> IO (Either String (Some (FunctionFormula sym)))
readDefinedFunctionFromFile sym env fp = do
  liftIO $ U.logIO U.Info $ "readDefinedFunctionFromFile " ++ fp
  readDefinedFunction sym env =<< T.readFile fp
