{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module SemMC.Stochastic.IORelation.Implicit (
  findImplicitOperands
  ) where

import qualified GHC.Err.Located as L

import Control.Monad ( replicateM )
import Control.Monad.Trans ( liftIO )
import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import Data.Monoid
import Data.Proxy ( Proxy(..) )
import qualified Data.Set as S

import qualified Data.Set.NonEmpty as NES
import qualified Data.Parameterized.Classes as P
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Some ( Some(..) )
import Lang.Crucible.BaseTypes

import qualified Dismantle.Instruction as D
import qualified Dismantle.Instruction.Random as D

import SemMC.Architecture
import qualified SemMC.ConcreteState as CS

import SemMC.Stochastic.IORelation.Shared
import SemMC.Stochastic.IORelation.Types
import qualified SemMC.Stochastic.Remote as R

import Debug.Trace
import Text.Printf ( printf )
-- | Sweep through the parameter space to find locations not mentioned in
-- parameter lists that are modified by the instruction.
--
-- To do this, we generate a bunch of randomized operand lists to cycle through
-- possible registers.
--
-- For this, we will want to focus on generating values that trigger edge cases
-- to make sure we can deal with flags registers.
findImplicitOperands :: forall arch sh
                      . (CS.ConcreteArchitecture arch, D.ArbitraryOperands (Opcode arch) (Operand arch))
                     => Opcode arch (Operand arch) sh
                     -> Learning arch (IORelation arch sh)
findImplicitOperands op = do
  g <- askGen
  -- We generate 20 random instruction instances with this opcode (and for each
  -- random instruction instance, generate many test vectors).
  tests <- concat <$> replicateM 20 (genTestSet g)
  withTestResults op tests $ computeImplicitOperands op tests
  where
    genTestSet g = do
      t0 <- mkRandomTest
      insn <- liftIO $ D.randomInstruction g (NES.singleton (Some op))
      tb0 <- generateImplicitTests insn t0
      mapM (wrapTestBundle insn) tb0

-- | Interpret the results of the implicit operand search
--
-- The fact records all of the explicit locations.  We just need to look at all
-- of the *other* (unmentioned) locations to find any changes.  Any changed
-- locations are implicit outputs.
computeImplicitOperands :: (CS.ConcreteArchitecture arch)
                        => Opcode arch (Operand arch) sh
                        -> [TestBundle (TestCase arch) (ImplicitFact arch)]
                        -> [R.ResultOrError (CS.ConcreteState arch)]
                        -> Learning arch (IORelation arch sh)
computeImplicitOperands op tests results =
  F.foldlM (buildImplicitRelation op idx) mempty tests
  where
    idx = F.foldl' indexResults emptyResultIndex results

-- |
--
-- Note that the operand isn't used - it is acting like a proxy for the @sh@ parameter.
buildImplicitRelation :: (CS.ConcreteArchitecture arch)
                      => Opcode arch (Operand arch) sh
                      -> ResultIndex (CS.ConcreteState arch)
                      -> IORelation arch sh
                      -> TestBundle (TestCase arch) (ImplicitFact arch)
                      -> Learning arch (IORelation arch sh)
buildImplicitRelation op rix iorel tb = do
  implicitLocs <- mconcat <$> mapM (collectImplicitOutputLocations op rix (tbTestBase tb) baseRes (tbResult tb)) (tbTestCases tb)
  return (iorel <> implicitLocs)
  where
    Just baseRes = M.lookup (R.testNonce (tbTestBase tb)) (riSuccesses rix)

{-# NOINLINE traceStates #-}
traceStates baseCase tc baseRes res = do
              traceM $ printf "  Initial base:         %s" (show (R.testContext baseCase))
              traceM $ printf "  Initial Tweaked:      %s" (show (R.testContext tc))
              traceM $ printf "  Base result state:    %s" (show (R.resultContext baseRes))
              traceM $ printf "  Tweaked result state: %s" (show (R.resultContext res))

collectImplicitOutputLocations :: forall arch sh
                                . (CS.ConcreteArchitecture arch)
                               => Opcode arch (Operand arch) sh
                               -> ResultIndex (CS.ConcreteState arch)
                               -> R.TestCase (CS.ConcreteState arch) (Instruction arch)
                               -> R.TestResult (CS.ConcreteState arch)
                               -> ImplicitFact arch
                               -> TestCase arch
                               -> Learning arch (IORelation arch sh)
collectImplicitOutputLocations _op rix baseCase baseRes f tc =
  case M.lookup (R.testNonce tc) (riSuccesses rix) of
    Nothing -> return mempty
    Just res ->
      -- case M.lookup (R.testNonce baseCase) (riSuccesses rix) of
      --   Nothing -> trace (printf "Failed to execute base test case with nonce %d\n" (R.testNonce baseCase)) $ return mempty
      --   Just baseRes ->
          case f of
            ImplicitFact { ifExplicits = explicitOperands
                         , ifLocation = loc0
                         , ifInstruction = ii
                         } -> do
              traceM $ printf "\n\nTest nonce is %d, testing location %s" (R.testNonce tc) (show loc0)
              traceM $ printf "  Test instruction: %s" (show ii)
              traceM $ printf "  Test program bytes are: %s" (show (R.testProgram tc))
              traceM $ printf "  Explicit locations: %s" (show explicitOperands)
              traceStates baseCase tc baseRes res
              F.foldrM (addLocIfImplicitAndDifferent loc0 explicitOperands) mempty (MapF.toList (R.resultContext res))
  where
    addLocIfImplicitAndDifferent :: Some (CS.View arch)
                                 -> S.Set (Some (CS.View arch))
                                 -> MapF.Pair (Location arch) CS.Value
                                 -> IORelation arch sh
                                 -> Learning arch (IORelation arch sh)
    addLocIfImplicitAndDifferent loc0 explicitOperands (MapF.Pair loc postVal) s =
      let proxy = Proxy :: Proxy arch
      in case locationType loc of
        BaseBVRepr nr ->
          case withKnownNat nr (let tv = CS.trivialView proxy loc
                                in (CS.peekMS (R.testContext tc) tv, CS.peekMS (R.resultContext baseRes) tv,tv)) of
            (_preVal, baseResVal, tv) ->
              case () of
                () | Some baseResVal == Some postVal -> return s
                   | Some tv /= loc0 && not (S.member (Some tv) explicitOperands) && not (S.member loc0 explicitOperands) ->
                     trace (printf "  (1) Difference in values at location %s (loc0=%s): base=%s post=%s" (P.showF tv) (show loc0) (P.showF baseResVal) (P.showF postVal)) $
                     return s { inputs = S.insert (ImplicitOperand loc0) (inputs s)
                              , outputs = S.insert (ImplicitOperand (Some tv)) (outputs s)
                              }
                   | Some tv /= loc0 && not (S.member loc0 explicitOperands) && S.member (Some tv) explicitOperands ->
                       trace (printf "  (2) Difference in values at location %s (loc0=%s): base=%s post=%s" (P.showF tv) (show loc0) (P.showF baseResVal) (P.showF postVal)) $
                     return s { inputs = S.insert (ImplicitOperand loc0) (inputs s) }
                   | Some tv /= loc0 && S.member loc0 explicitOperands && not (S.member (Some tv) explicitOperands) ->
                       trace (printf "  (3) Difference in values at location %s (loc0=%s): base=%s post=%s" (P.showF tv) (show loc0) (P.showF baseResVal) (P.showF postVal)) $
                     return s { outputs = S.insert (ImplicitOperand (Some tv)) (outputs s) }
                   | otherwise -> return s
        lt -> L.error ("Unexpected location type: " ++ show lt)

-- | For an instruction instance, sweep across the parameter space of all of the
-- interesting values for the operands.  Examine all of the locations that do
-- not appear in the register list for changes.
--
-- Repeat for a number of random instructions
generateImplicitTests :: forall arch
                       . (CS.ConcreteArchitecture arch)
                      => Instruction arch
                      -> CS.ConcreteState arch
                      -> Learning arch [TestBundle (CS.ConcreteState arch) (ImplicitFact arch)]
generateImplicitTests i s0 = do
  let allLocs = testCaseLocations (Proxy :: Proxy arch) s0
  mapM (genTestForLoc i s0) allLocs

genTestForLoc :: forall arch
               . (CS.ConcreteArchitecture arch)
              => Instruction arch
              -> CS.ConcreteState arch
              -> Some (CS.View arch)
              -> Learning arch (TestBundle (CS.ConcreteState arch) (ImplicitFact arch))
genTestForLoc i s0 (Some loc0) = do
  testStates <- replicateM 20 (withGeneratedValueForLocation loc0 (CS.pokeMS s0 loc0))
  case i of
    D.Instruction _ ops -> do
      let explicits = [ Some v
                      | IndexedSemanticView _ (CS.SemanticView { CS.semvView = v })
                          <- instructionRegisterOperands (Proxy :: Proxy arch) ops
                      ]
      return TestBundle { tbTestCases = testStates
                        , tbTestBase = s0
                        , tbResult = ImplicitFact { ifExplicits = S.fromList explicits
                                                  , ifLocation = Some loc0
                                                  , ifInstruction = i
                                                  }
                        }

{- Note [Test Form]

In this module we are trying to learn the set of locations that are *implicit
operands* (i.e., operands not mentioned in operand lists) for each instruction.

Implicit operands can be both inputs and outputs (e.g., flags registers).

To find implicit operands, we generate test inputs where we tweak locations one
at a time.  Let the location to be tweaked be L_0.  Generate a number of test
cases that tweak L_0 with both random and interesting values.  We then compare
the inputs against the corresponding outputs from the test cases after they are
run.  In the output states, for each L_i, if L_i is changed:

 * If L_i is an explicit operand, then L_0 is an implicit input operand
   (unless i == 0, in which case L_0 is an explicit input and output)
 * If L_i is not an explicit operand, then L_0 is an implicit input operand and L_i is an implicit output operand
   (unless i == 0, in which case L_0 is an implicit input and output)

-}
