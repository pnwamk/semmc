{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SemMC.Stochastic.Classify (
  classify,
  chooseClass,
  chooseProgram,
  EquivalenceClasses,
  equivalenceClasses,
  countPrograms
  ) where

import qualified Data.Set as S

import SemMC.Architecture ( Instruction )
import SemMC.Stochastic.Monad

data EquivalenceClasses arch = EquivalenceClasses { unClasses :: S.Set (S.Set [Instruction arch]) }

data EquivalenceClass arch = EquivalenceClass { unClass :: S.Set [Instruction arch] }

equivalenceClasses :: [Instruction arch] -> EquivalenceClasses arch
equivalenceClasses p = EquivalenceClasses (S.singleton (S.singleton p))

countPrograms :: EquivalenceClasses arch -> Int
countPrograms s = sum (map S.size (S.toList (unClasses s)))

classify :: (Ord (Instruction arch))
         => [Instruction arch]
         -> EquivalenceClasses arch
         -> Syn sym arch (Maybe (EquivalenceClasses arch))
classify p eqclasses = do
  mclasses <- classifyByClass p S.empty (S.toList (unClasses eqclasses))
  case mclasses of
    Nothing -> return Nothing
    Just classes
      | S.null classes -> do
          -- Add a new equivalence class for this program, since it isn't
          -- equivalent to any existing class
          return (Just (EquivalenceClasses (S.singleton (S.singleton p) `S.union` unClasses eqclasses)))
      | otherwise -> do
          let eqclasses' = S.insert p (mergeClasses classes)
          return (Just (EquivalenceClasses (S.singleton eqclasses')))

classifyByClass :: [Instruction arch]
                -- ^ The program to classify
                -> S.Set (S.Set [Instruction arch])
                -- ^ The set of classes matching the input program
                -> [S.Set [Instruction arch]]
                -- ^ The existing equivalence classes
                -> Syn sym arch (Maybe (S.Set (S.Set [Instruction arch])))
classifyByClass = undefined

chooseClass :: EquivalenceClasses arch -> Syn sym arch (EquivalenceClass arch)
chooseClass = undefined

chooseProgram :: EquivalenceClass arch -> Syn sym arch [Instruction arch]
chooseProgram = undefined

mergeClasses :: (Ord (Instruction arch)) => S.Set (S.Set [Instruction arch]) -> S.Set [Instruction arch]
mergeClasses s = S.unions (S.toList s)
