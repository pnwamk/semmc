{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Definitions of formulas
module SemMC.Formula.Formula
  ( -- * Parameter
    Parameter(..)
  , paramType
    -- * ParameterizedFormula
  , ParameterizedFormula(..)
    -- * Formula
  , Formula(..)
  , formInputs
  , formOutputs
  , validFormula
  , emptyFormula
  , coerceFormula
  ) where

import qualified Data.Set as Set
import           GHC.TypeLits ( Symbol )
import           Text.Printf ( printf )

import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.ShapedList ( ShapedList, Index )
import qualified Lang.Crucible.Solver.Interface as S
import qualified Lang.Crucible.Solver.SimpleBuilder as S
import           Lang.Crucible.BaseTypes

import           SemMC.Architecture
import           SemMC.Util

-- | A parameter for use in the 'ParameterizedFormula' before.
data Parameter arch (sh :: [Symbol]) (tp :: BaseType) where
  -- | A parameter that will be filled in at instantiation time. For example, if
  -- you have the x86 opcode @call r32@, an 'Operand' would be used to represent
  -- the @r32@ hole. It could also represent an immediate.
  Operand :: BaseTypeRepr (OperandType arch s) -> Index sh s -> Parameter arch sh (OperandType arch s)
  -- | A parameter that always represents a particular machine location. For
  -- example, if you have the x86 opcode @call r32@, a 'Literal' would be used
  -- to represent the implicit @esp@ register used.
  Literal :: Location arch tp -> Parameter arch sh tp

instance ShowF (Location arch) => Show (Parameter arch sh tp) where
  show (Operand repr idx) = printf "Operand (%s) (%s)" (show repr) (show idx)
  show (Literal var) = unwords ["Literal", showF var]

instance (ShowF (Location arch)) => ShowF (Parameter arch sh)

instance TestEquality (Location arch) => TestEquality (Parameter arch sh) where
  Operand _ idx1 `testEquality` Operand _ idx2 = (\Refl -> Refl) <$> testEquality idx1 idx2
  Literal   var1 `testEquality` Literal   var2 = (\Refl -> Refl) <$> testEquality var1 var2
  _              `testEquality`              _ = Nothing

instance Eq (Location arch tp) => Eq (Parameter arch sh tp) where
  Operand _ idx1 == Operand _ idx2 = isJust $ testEquality idx1 idx2
  Literal   var1 == Literal   var2 = var1 == var2
  _              ==              _ = False

instance OrdF (Location arch) => OrdF (Parameter arch sh) where
  Operand _ _ `compareF` Literal   _ = LTF
  Literal   _ `compareF` Operand _ _ = GTF
  Operand _ idx1 `compareF` Operand _ idx2 =
    case idx1 `compareF` idx2 of
      LTF -> LTF
      EQF -> EQF
      GTF -> GTF
  Literal var1 `compareF` Literal var2 =
    case var1 `compareF` var2 of
      LTF -> LTF
      EQF -> EQF
      GTF -> GTF

-- | Get a representation of the 'BaseType' this formula parameter is
-- type-parameterized over.
paramType :: (Architecture arch) => Parameter arch sh tp -> BaseTypeRepr tp
paramType (Operand repr _) = repr
paramType (Literal loc) = locationType loc

-- | A "templated" or "parameterized" formula, i.e., a formula that has holes
-- that need to be filled in before it represents an actual concrete
-- instruction.
data ParameterizedFormula sym arch (sh :: [Symbol]) =
  ParameterizedFormula { pfUses :: Set.Set (Some (Parameter arch sh))
                       , pfOperandVars :: ShapedList (BoundVar sym arch) sh
                       , pfLiteralVars :: MapF.MapF (Location arch) (S.BoundVar sym)
                       , pfDefs :: MapF.MapF (Parameter arch sh) (S.SymExpr sym)
                       }

deriving instance (ShowF (Location arch), ShowF (S.SymExpr sym), ShowF (S.BoundVar sym)) => Show (ParameterizedFormula sym arch sh)

instance (ShowF (Location arch), ShowF (S.SymExpr sym), ShowF (S.BoundVar sym)) => ShowF (ParameterizedFormula sym arch)

-- | A formula representing a concrete instruction.
--
-- Invariants:
-- * All bound variables used in 'formDefs' should be in 'formParamVars'. This
--   is checkable using the 'validFormula' function.
-- * All bound variables in 'formParamVars' should not appear in any other
--   formula. Yes, this breaks the notion of referential transparency in many
--   ways, but it was the least bad solution.
data Formula sym arch =
  Formula { formParamVars :: MapF.MapF (Location arch) (S.BoundVar sym)
          , formDefs :: MapF.MapF (Location arch) (S.SymExpr sym)
          }
deriving instance (ShowF (S.SymExpr sym), ShowF (S.BoundVar sym), ShowF (Location arch)) => Show (Formula sym arch)

-- | Get the locations used by a formula.
formInputs :: (OrdF (Location arch)) => Formula sym arch -> Set.Set (Some (Location arch))
formInputs = Set.fromList . MapF.keys . formParamVars

-- | Get the locations modified by a formula.
formOutputs :: (OrdF (Location arch)) => Formula sym arch -> Set.Set (Some (Location arch))
formOutputs = Set.fromList . MapF.keys . formDefs

-- | Check if a given 'Formula' obeys the stated invariant.
validFormula :: Formula (S.SimpleBuilder t st) arch -> Bool
validFormula (Formula { formParamVars = paramVars, formDefs = defs }) =
  mconcat (map (viewSome allBoundVars) (MapF.elems defs))
  `Set.isSubsetOf` Set.fromList (MapF.elems paramVars)

-- | A formula that uses no variables and changes no variables.
emptyFormula :: Formula sym arch
emptyFormula = Formula { formParamVars = MapF.empty, formDefs = MapF.empty }

-- | Turn a formula from one architecture into that of another, assuming the
-- location types of the architectures are the same.
coerceFormula :: (Location arch1 ~ Location arch2) => Formula sym arch1 -> Formula sym arch2
coerceFormula f =
  Formula { formParamVars = formParamVars f
          , formDefs = formDefs f
          }
