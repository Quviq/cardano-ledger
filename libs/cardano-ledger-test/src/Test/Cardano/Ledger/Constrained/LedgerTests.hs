{-# LANGUAGE GADTs #-}
module Test.Cardano.Ledger.Constrained.LedgerTests where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Lens.Micro ((^.))

import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Env

-- import Cardano.Ledger.Coin
-- import Cardano.Ledger.Era (Era)
-- import Cardano.Ledger.Shelley
import Cardano.Ledger.Shelley.LedgerState
import Test.Cardano.Ledger.Constrained.Monad
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.Tests (checkPredicates)

-- import Test.Cardano.Ledger.Constrained.Shrink

import Test.Cardano.Ledger.Constrained.Examples (newepochConstraints)
-- import Test.Cardano.Ledger.Constrained.Preds.Universes
-- import Test.Cardano.Ledger.Constrained.Preds.DPState
-- import Test.Cardano.Ledger.Constrained.Preds.PParams
import Test.Cardano.Ledger.Constrained.Solver
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Proof (Reflect (..), ConwayEra, Standard)
import Test.QuickCheck hiding (getSize, total)

newEpochStateToolChain :: Reflect era => ToolChain era
newEpochStateToolChain = [toolChainSub standardOrderInfo . newepochConstraints]
  -- [ const pure
  -- , pParamsStage
  -- , universeStage
  -- , vstateStage
  -- , pstateStage
  -- , dstateStage
  -- ]
  -- , utxostateStage
  -- , accountstateStage
  -- , epochstateStage
  -- , newepochstateStage
  -- ]

unTarget :: Rep era t -> Target era t -> t -> Env era
unTarget rep target v =
    Env $ Map.fromList [ (x, Payload repX (v ^. lens) acc)
                       | Name (V x repX acc@(Yes rep' lens)) <- names
                       , Just Refl <- [testEql rep rep']
                       ]
  where names = Set.toList $ varsOfTarget mempty target

genNewEpochState :: Reflect era => Proof era -> Gen (NewEpochState era)
genNewEpochState proof = do
  env <- toolChain proof newEpochStateToolChain
  monadTyped $ runTarget env $ newEpochStateT proof

type TestEra = ConwayEra Standard

testProof :: Proof TestEra
testProof = Conway Standard

prop_newEpochState :: Property
prop_newEpochState = forAll (genNewEpochState testProof) $ \ st ->
  let env = unTarget NewEpochStateR (newEpochStateT testProof) st in
  checkPredicates (newepochConstraints testProof) env

