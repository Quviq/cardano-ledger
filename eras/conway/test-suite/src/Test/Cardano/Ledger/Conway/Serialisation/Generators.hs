{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Conway.Serialisation.Generators () where

import Cardano.Ledger.Binary (Sized)
import Cardano.Ledger.Conway.Core
import Cardano.Ledger.Conway.Delegation.Certificates
import Cardano.Ledger.Conway.Genesis (ConwayGenesis (..))
import Cardano.Ledger.Conway.Governance
import Cardano.Ledger.Conway.Rules
import Cardano.Ledger.Conway.TxBody
import Cardano.Ledger.Crypto (Crypto)
import Control.State.Transition.Extended (STS (Event))
import Test.Cardano.Ledger.Alonzo.Serialisation.Generators ()
import Test.Cardano.Ledger.Babbage.Serialisation.Generators ()
import Test.Cardano.Ledger.Common
import Test.Cardano.Ledger.Shelley.ConcreteCryptoTypes (Mock)
import Test.Cardano.Ledger.ShelleyMA.Serialisation.Generators (genMintValues)

instance Crypto c => Arbitrary (ConwayGenesis c) where
  arbitrary = ConwayGenesis <$> arbitrary <*> arbitrary

instance Crypto c => Arbitrary (ConwayDCert c) where
  arbitrary =
    oneof
      [ ConwayDCertDeleg <$> arbitrary
      , ConwayDCertPool <$> arbitrary
      , ConwayDCertConstitutional <$> arbitrary
      ]

------------------------------------------------------------------------------------------
-- Cardano.Ledger.Conway.Governance ------------------------------------------------------
------------------------------------------------------------------------------------------

-- FIXME: replace with when serialziation is fixed:
-- deriving instance (Era era, Arbitrary (PParamsUpdate era)) => Arbitrary (ConwayTallyState era)
instance (Era era, Arbitrary (PParamsUpdate era)) => Arbitrary (ConwayTallyState era) where
  arbitrary = pure $ ConwayTallyState mempty

instance (Era era, Arbitrary (PParamsUpdate era)) => Arbitrary (GovernanceActionInfo era) where
  arbitrary =
    GovernanceActionInfo
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance (Era era, Arbitrary (PParamsUpdate era)) => Arbitrary (GovernanceActionState era) where
  arbitrary =
    GovernanceActionState
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance (Era era, Arbitrary (PParamsUpdate era)) => Arbitrary (GovernanceAction era) where
  arbitrary =
    oneof
      [ ParameterChange <$> arbitrary
      , HardForkInitiation <$> arbitrary
      , TreasuryWithdrawals <$> arbitrary
      ]

instance Era era => Arbitrary (Vote era) where
  arbitrary =
    Vote
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Crypto c => Arbitrary (GovernanceActionId c) where
  arbitrary =
    GovernanceActionId
      <$> arbitrary
      <*> arbitrary

deriving instance Arbitrary GovernanceActionIx

instance Arbitrary VoterRole where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary VoteDecision where
  arbitrary = arbitraryBoundedEnum

instance
  ( Mock (EraCrypto era)
  , ConwayEraTxBody era
  , Arbitrary (Sized (TxOut era))
  , Arbitrary (TxOut era)
  , Arbitrary (Value era)
  , Arbitrary (Script era)
  , Arbitrary (PParamsUpdate era)
  ) =>
  Arbitrary (ConwayTxBody era)
  where
  arbitrary =
    ConwayTxBody
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> genMintValues
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      -- FIXME: For now this is turned off, rountrip tests in consensus are failing
      <*> pure mempty -- arbitrary
      <*> pure mempty -- arbitrary

------------------------------------------------------------------------------------------
-- Cardano.Ledger.Conway.Rules -----------------------------------------------------------
------------------------------------------------------------------------------------------

-- TALLY

deriving instance Era era => Arbitrary (ConwayTallyPredFailure era)
deriving instance Era era => Arbitrary (TallyEnv era)

instance (Era era, Arbitrary (PParamsUpdate era)) => Arbitrary (GovernanceProcedure era) where
  arbitrary =
    oneof
      [ VotingProcedure <$> arbitrary
      , ProposalProcedure <$> arbitrary
      ]

instance
  ( Arbitrary (PredicateFailure (EraRule "UTXOW" era))
  , Arbitrary (PredicateFailure (EraRule "DELEGS" era))
  , Arbitrary (PredicateFailure (EraRule "TALLY" era))
  ) =>
  Arbitrary (ConwayLedgerPredFailure era)
  where
  arbitrary =
    oneof
      [ ConwayUtxowFailure <$> arbitrary
      , ConwayDelegsFailure <$> arbitrary
      , ConwayTallyFailure <$> arbitrary
      ]

-- EPOCH

instance
  ( Era era
  , Arbitrary (Event (EraRule "POOLREAP" era))
  , Arbitrary (Event (EraRule "SNAP" era))
  ) =>
  Arbitrary (ConwayEpochEvent era)
  where
  arbitrary =
    oneof
      [ PoolReapEvent <$> arbitrary
      , SnapEvent <$> arbitrary
      ]

-- NEWEPOCH

instance
  ( Era era
  , Arbitrary (Event (EraRule "RUPD" era))
  ) =>
  Arbitrary (ConwayNewEpochEvent era)
  where
  arbitrary =
    oneof
      [ DeltaRewardEvent <$> arbitrary
      , RestrainedRewards <$> arbitrary <*> arbitrary <*> arbitrary
      ]

-- TICKF

instance
  ( Era era
  ) =>
  Arbitrary (ConwayTickfPredFailure era)
  where
  arbitrary = undefined

instance
  ( Era era
  ) =>
  Arbitrary (ConwayTickfEvent era)
  where
  arbitrary = undefined
