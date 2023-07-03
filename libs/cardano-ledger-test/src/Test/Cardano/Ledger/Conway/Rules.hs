{-# LANGUAGE TypeApplications #-}
module Test.Cardano.Ledger.Conway.Rules where

import Test.Cardano.Ledger.Constrained.LedgerTests

import Test.QuickCheck

import Data.Proxy

import Control.State.Transition.Extended

import Test.Cardano.Ledger.Shelley.Utils
import Test.Cardano.Ledger.Shelley.Generator.Presets
import Test.Cardano.Ledger.Shelley.Constants
import Test.Cardano.Ledger.Shelley.Generator.Core
import Test.Cardano.Ledger.Generic.Proof

import Cardano.Ledger.Conway
import Cardano.Ledger.Conway.Rules.Tickf

prop_tickf :: Property
prop_tickf =
  forAll (genNewEpochState proof $ geKeySpace env) (shrinkNewEpochState proof) $ \ nes ->
  forAll arbitrary shrink $ \ slot -> runShelleyBase $ do
    res <- applySTS @(ConwayTICKF Conway) $ TRC ((), nes, slot)
    case res of
      Left pfailure -> False
      Right nes'    -> validEpochState nes'
  where
    env = genEnv (Proxy @Conway) defaultConstants
    proof = Conway Mock
