{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module SemMC.Formula.Printer
  ( printParameterizedFormula
  , printFormula
  ) where

import qualified Data.Foldable as F
import qualified Data.Map as Map
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as SL
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Pair
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy ( Proxy(..) )
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Control.Monad.Writer as W

import           SemMC.Util ( fromJust' )

import qualified Data.SCargot.Repr.Rich as SE

import           What4.BaseTypes
import qualified What4.Expr as S
import qualified What4.Expr.BoolMap as BooM
import qualified What4.Expr.Builder as S
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Interface as S
import qualified What4.Symbol as S
import qualified What4.Serialize.Printer as WSP
import           What4.Serialize.SETokens

import qualified SemMC.Architecture as A
import qualified SemMC.BoundVar as BV
import           SemMC.Formula.Formula

-- This file is organized top-down, i.e., from high-level to low-level.

-- | Serialize a 'ParameterizedFormula' into its textual s-expression form.
printParameterizedFormula :: (A.Architecture arch)
                          => A.ShapeRepr arch sh
                          -> ParameterizedFormula (S.ExprBuilder t st fs) arch sh
                          -> T.Text
printParameterizedFormula rep =
  printTokens' mempty . sexprConvertParameterized rep

printFormula :: (ShowF (A.Location arch))
             => Formula (S.ExprBuilder t st fs) arch
             -> T.Text
printFormula = printTokens' mempty . sexprConvert

sexprConvert :: forall t st fs arch
              . (ShowF (A.Location arch))
             => Formula (S.ExprBuilder t st fs) arch
             -> SE.RichSExpr FAtom
sexprConvert f =
  SE.L $ (ident' "defs") : map (convertSimpleDef (Proxy @arch) (formParamVars f)) (MapF.toList (formDefs f))

convertSimpleDef :: forall arch proxy t
                  . (ShowF (A.Location arch))
                 => proxy arch
                 -> MapF.MapF (A.Location arch) (S.ExprBoundVar t)
                 -> MapF.Pair (A.Location arch) (S.Expr t)
                 -> SE.RichSExpr FAtom
convertSimpleDef _ paramVars (MapF.Pair loc e) =
  SE.L [ convertLocation loc, convertExprWithLet paramLookup e ]
  where
    tbl = Map.fromList [ (Some bv, convertLocation l) | MapF.Pair l bv <- MapF.toList paramVars ]
    paramLookup :: ParamLookup t
    paramLookup bv = Map.lookup (Some bv) tbl

convertExprWithLet :: ParamLookup t -> (S.Expr t tp) -> SE.RichSExpr FAtom
convertExprWithLet paramLookup e = fst $ W.runWriter $ WSP.convertExprWithLet paramLookup e

-- | Intermediate serialization.
sexprConvertParameterized :: (A.Architecture arch)
                          => A.ShapeRepr arch sh
                          -> ParameterizedFormula (S.ExprBuilder t st fs) arch sh
                          -> SE.RichSExpr FAtom
sexprConvertParameterized rep (ParameterizedFormula { pfUses = uses
                                                    , pfOperandVars = opVars
                                                    , pfLiteralVars = litVars
                                                    , pfDefs = defs
                                                    }) =
  SE.L [ SE.L [SE.A (AIdent "operands"), convertOperandVars rep opVars]
       , SE.L [SE.A (AIdent "in"),       convertUses opVars uses]
       , SE.L [SE.A (AIdent "defs"),     convertDefs opVars litVars defs]
       ]

convertUses :: (ShowF (A.Location arch))
            => SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
            -> Set.Set (Some (Parameter arch sh))
            -> SE.RichSExpr FAtom
convertUses oplist = SE.L . fmap (viewSome (convertParameter oplist)) . Set.toList

convertParameter :: (ShowF (A.Location arch))
                 => SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
                 -> Parameter arch sh tp
                 -> SE.RichSExpr FAtom
convertParameter opVars (OperandParameter _ idx) = ident' name
  where name = varName (opVars SL.!! idx)
convertParameter _ (LiteralParameter loc) = quoted' (showF loc)
convertParameter opVars (FunctionParameter fnName (WrappedOperand orep oix) _) =
  SE.L [uf, args]
  where
    uf = SE.L [ ident' "_", ident' "call", string' fnName ]
    args = SE.L [convertParameter opVars (OperandParameter orep oix) ]

-- | Used for substituting in the result expression when a variable is
-- encountered in a definition.
type ParamLookup t = forall tp. S.ExprBoundVar t tp -> Maybe (SE.RichSExpr FAtom)

convertDefs :: forall t st fs arch sh.
               (ShowF (A.Location arch))
            => SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
            -> MapF.MapF (A.Location arch) (S.ExprBoundVar t)
            -> MapF.MapF (Parameter arch sh) (S.Expr t)
            -> SE.RichSExpr FAtom
convertDefs opVars locVars = SE.L . fmap (convertDef opVars paramLookup) . MapF.toList
  where paramLookup :: ParamLookup t
        paramLookup = flip Map.lookup paramMapping . Some
        paramMapping = MapF.foldrWithKey insertLoc opMapping locVars
        insertLoc loc var = Map.insert (Some var) (convertLocation loc)
        opMapping = buildOpMapping opVars

convertLocation :: (ShowF loc) => loc tp -> SE.RichSExpr FAtom
convertLocation = quoted' . showF

-- | For use in the parameter lookup function.
buildOpMapping :: SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
               -> Map.Map (Some (S.ExprBoundVar t)) (SE.RichSExpr FAtom)
buildOpMapping SL.Nil = Map.empty
buildOpMapping (var SL.:< rest) =
  Map.insert (Some (BV.unBoundVar var)) (ident' name) $ buildOpMapping rest
  where name = varName var

convertDef :: (ShowF (A.Location arch))
           => SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
           -> ParamLookup t
           -> Pair (Parameter arch sh) (S.Expr t)
           -> SE.RichSExpr FAtom
convertDef opVars paramLookup (Pair param expr) =
  SE.L [ convertParameter opVars param
       , convertExprWithLet paramLookup expr ]

-- NOTE: There's probably some fancy caching we can do because of the nonces in
-- all the expressions. If the current implementation is at all slow, we can
-- implement that. However, I'm skipping it for now, since I imagine this won't
-- be a bottleneck.


-- | Extract the name, as a String, of a wrapped bound variable.
varName :: BV.BoundVar (S.ExprBuilder t st fs) arch op -> String
varName (BV.BoundVar var) = show (S.bvarName var)


convertOperandVars :: forall arch sh t st fs
                    . (A.Architecture arch)
                   => A.ShapeRepr arch sh
                   -> SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
                   -> SE.RichSExpr FAtom
convertOperandVars rep l =
  case (rep, l) of
    (SL.Nil, SL.Nil) -> SE.Nil
    (r SL.:< rep', var SL.:< rest) ->
      let nameExpr = ident' (varName var)
          typeExpr = AQuoted (A.operandTypeReprSymbol (Proxy @arch) r)
      in SE.cons (SE.DL [nameExpr] typeExpr) (convertOperandVars rep' rest)
