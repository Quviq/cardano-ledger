{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Pretty.Conway (
  ppConwayTxBody,
) where

import Cardano.Ledger.Conway (ConwayEra)
import Cardano.Ledger.Conway.Core
import Cardano.Ledger.Conway.Delegation.Certificates (ConwayDCert (..), transDCert)
import Cardano.Ledger.Conway.Governance (
  ConwayTallyState (..),
  GovernanceAction (..),
  GovernanceActionId (..),
  GovernanceActionInfo (..),
  GovernanceActionIx (..),
  GovernanceActionState (..),
  Vote (..),
  VoteDecision (..),
  VoterRole (..),
 )
import Cardano.Ledger.Conway.Rules (ConwayLedgerPredFailure (..), ConwayTallyPredFailure (..), PredicateFailure)
import Cardano.Ledger.Conway.TxBody (ConwayTxBody (..))
import Cardano.Ledger.Crypto
import Cardano.Ledger.Pretty (
  PDoc,
  PrettyA (..),
  ppAuxiliaryDataHash,
  ppCoin,
  ppConstitutionalDelegCert,
  ppDelegCert,
  ppKeyHash,
  ppNetwork,
  ppPoolCert,
  ppRecord,
  ppSafeHash,
  ppSet,
  ppSexp,
  ppStrictMaybe,
  ppStrictSeq,
  ppString,
  ppTxId,
  ppTxIn,
  ppUrl,
  ppWithdrawals,
  ppWord64,
 )
import Cardano.Ledger.Pretty.Babbage (ppBabbagePParams, ppBabbagePParamsUpdate)
import Cardano.Ledger.Pretty.Mary (ppMultiAsset, ppValidityInterval)
import Lens.Micro ((^.))

instance
  ( ConwayEraTxBody era
  , PrettyA (TxOut era)
  , TxBody era ~ ConwayTxBody era
  , PrettyA (PParamsUpdate era)
  ) =>
  PrettyA (ConwayTxBody era)
  where
  prettyA = ppConwayTxBody

ppConwayDCert :: ConwayDCert c -> PDoc
ppConwayDCert (ConwayDCertDeleg dc) = ppSexp "ConwayDCertDeleg" [ppDelegCert dc]
ppConwayDCert (ConwayDCertPool pc) = ppSexp "ConwayDCertPool" [ppPoolCert pc]
ppConwayDCert (ConwayDCertConstitutional gdc) = ppSexp "ConwayDCertConstitutional" [ppConstitutionalDelegCert gdc]

ppConwayTxBody ::
  forall era.
  ( ConwayEraTxBody era
  , PrettyA (TxOut era)
  , TxBody era ~ ConwayTxBody era
  , PrettyA (GovernanceActionInfo era)
  ) =>
  ConwayTxBody era ->
  PDoc
ppConwayTxBody txb =
  ppRecord
    "TxBody (Conway)"
    [ ("spending inputs", ppSet ppTxIn $ txb ^. inputsTxBodyL)
    , ("collateral inputs", ppSet ppTxIn $ txb ^. collateralInputsTxBodyL)
    , ("reference inputs", ppSet ppTxIn $ txb ^. referenceInputsTxBodyL)
    , ("outputs", ppStrictSeq prettyA (txb ^. outputsTxBodyL))
    , ("collateral return", ppStrictMaybe prettyA (txb ^. collateralReturnTxBodyL))
    , ("total collateral", ppStrictMaybe ppCoin $ txb ^. totalCollateralTxBodyL)
    , ("certificates", ppStrictSeq ppConwayDCert $ txb ^. conwayCertsTxBodyL)
    , ("withdrawals", ppWithdrawals $ txb ^. withdrawalsTxBodyL)
    , ("transaction fee", ppCoin $ txb ^. feeTxBodyL)
    , ("validity interval", ppValidityInterval $ txb ^. vldtTxBodyL)
    , ("required signer hashes", ppSet ppKeyHash $ txb ^. reqSignerHashesTxBodyL)
    , ("mint", ppMultiAsset $ txb ^. mintTxBodyL)
    , ("script integrity hash", ppStrictMaybe ppSafeHash $ txb ^. scriptIntegrityHashTxBodyL)
    , ("auxiliary data hash", ppStrictMaybe ppAuxiliaryDataHash $ txb ^. auxDataHashTxBodyL)
    , ("network id", ppStrictMaybe ppNetwork $ txb ^. networkIdTxBodyL)
    , ("governance actions", ppStrictSeq prettyA $ txb ^. govActionsTxBodyL)
    , ("votes", ppStrictSeq prettyA $ txb ^. votesTxBodyL)
    ]

ppGovernanceActionIx :: GovernanceActionIx -> PDoc
ppGovernanceActionIx (GovernanceActionIx idx) = ppWord64 idx

ppGovernanceActionId :: GovernanceActionId era -> PDoc
ppGovernanceActionId GovernanceActionId {..} =
  ppRecord
    "GovernanceActionId"
    [ ("transaction id", ppTxId gaidTxId)
    , ("governance action index", ppGovernanceActionIx gaidGovActionIx)
    ]

ppVoterRole :: VoterRole -> PDoc
ppVoterRole ConstitutionalCommittee = "constitutional committee"
ppVoterRole DRep = "DRep"
ppVoterRole SPO = "SPO"

ppVoteDecision :: VoteDecision -> PDoc
ppVoteDecision No = "no"
ppVoteDecision Yes = "yes"
ppVoteDecision Abstain = "abstain"

instance PrettyA (Vote era) where
  prettyA Vote {..} =
    ppRecord
      "Vote"
      [ ("governance action ID", ppGovernanceActionId voteGovActionId)
      , ("voter role", ppVoterRole voteRole)
      , ("vote role key hash", ppKeyHash voteRoleKeyHash)
      , ("vote metadata URL", ppUrl voteMetadataURL)
      , ("vote metadata hash", ppSafeHash voteMetadataHash)
      , ("vote decision", ppVoteDecision voteDecision)
      ]

instance PrettyA (PParamsUpdate era) => PrettyA (GovernanceAction era) where
  prettyA (ParameterChange ppup) =
    ppRecord "ParameterChange" $
      [("protocol parameters update", prettyA ppup)]
  prettyA (HardForkInitiation pv) =
    ppRecord "HardForkInitiation" $
      [("protocol version", prettyA pv)]
  prettyA (TreasuryWithdrawals ws) =
    ppRecord "TreasuryWithdrawals" $
      [("withdrawals map", prettyA ws)]

instance PrettyA (PParamsUpdate era) => PrettyA (GovernanceActionInfo era) where
  prettyA GovernanceActionInfo {..} =
    ppRecord
      "GovernanceActionInfo"
      [ ("deposit amount", ppCoin gaiDepositAmount)
      , ("reward address", ppKeyHash gaiRewardAddress)
      , ("metadata URL", ppUrl gaiMetadataURL)
      , ("metadata hash", ppSafeHash gaiMetadataHash)
      , ("governance action", prettyA gaiAction)
      ]

instance forall c. PrettyA (ConwayDCert c) where
  prettyA = prettyA . transDCert

instance Crypto c => PrettyA (PParams (ConwayEra c)) where
  prettyA = ppBabbagePParams

instance Crypto c => PrettyA (PParamsUpdate (ConwayEra c)) where
  prettyA = ppBabbagePParamsUpdate

instance
  ( PrettyA (PredicateFailure (EraRule "UTXOW" era))
  , PrettyA (PredicateFailure (EraRule "DELEGS" era))
  , PrettyA (PredicateFailure (EraRule "TALLY" era))
  ) =>
  PrettyA (ConwayLedgerPredFailure era)
  where
  prettyA (ConwayUtxowFailure x) = prettyA x
  prettyA (ConwayDelegsFailure x) = prettyA x
  prettyA (ConwayTallyFailure x) = prettyA x

instance PrettyA (ConwayTallyPredFailure era) where
  prettyA (NoSuchGovernanceAction vote) =
    ppRecord
      "NoSuchGovernanceAction"
      [("Vote", prettyA vote)]

instance PrettyA (PParamsUpdate era) => PrettyA (ConwayTallyState era) where
  prettyA (ConwayTallyState x) = prettyA x

instance PrettyA (GovernanceActionId era) where
  prettyA GovernanceActionId {..} =
    ppRecord
      "GovernanceActionId"
      [ ("Transaction ID", prettyA gaidTxId)
      , ("Governance Action Index", prettyA gaidGovActionIx)
      ]

instance PrettyA GovernanceActionIx where
  prettyA (GovernanceActionIx x) = prettyA x

instance PrettyA VoterRole where
  prettyA = ppString . show

instance PrettyA (PParamsUpdate era) => PrettyA (GovernanceActionState era) where
  prettyA GovernanceActionState {..} =
    ppRecord
      "GovernanceActionState"
      [ ("Votes", prettyA gasVotes)
      , ("Deposit", prettyA gasDeposit)
      , ("Return Address", prettyA gasReturnAddr)
      , ("Action", prettyA gasAction)
      ]
