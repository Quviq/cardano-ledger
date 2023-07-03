module Test.Cardano.Ledger.Conway.Rules where

import Test.Cardano.Ledger.Constrained.LedgerTests

import Test.QuickCheck

import Cardano.Ledger.Conway.Rules.Tickf

prop_tickf :: Property
prop_tickf =
  let env = genEnv (Proxy @Conway) defaultConstants in
  forAll (genNewEpochState proof $ geKeySpace env) (shrinkNewEpochState proof) \ nes ->
  forAll arbitrary shrink \ slot -> runShelleyBase $ do
    res <- applySTS @(ConwayTICKF @Conway) $ TRC ((), nes, slot)
    case res of
      Left pfailure -> False
      Right nes'    -> validEpochState nes'
