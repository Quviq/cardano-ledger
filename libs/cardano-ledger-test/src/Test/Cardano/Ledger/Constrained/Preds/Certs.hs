{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.Constrained.Preds.Certs where

import Cardano.Ledger.BaseTypes (EpochNo (..), maybeToStrictMaybe)
import Cardano.Ledger.Coin (Coin (..), DeltaCoin)
import Cardano.Ledger.Conway.TxCert (
  ConwayDelegCert (..),
  ConwayTxCert (..),
  Delegatee (..),
 )
import Cardano.Ledger.Core (ConstitutionalDelegCert (..))
import Cardano.Ledger.Credential (Credential (..), StakeCredential)
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.PoolParams (PoolParams (..))
import Cardano.Ledger.Pretty (ppList)
import Cardano.Ledger.Shelley.TxCert (
  MIRCert (..),
  MIRPot (..),
  MIRTarget (..),
  PoolCert (..),
  ShelleyDelegCert (..),
  ShelleyTxCert (..),
 )
import Data.Map (Map)
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Classes
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Monad (monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.DPState (dstateStage, pstateStage, vstateStage)
import Test.Cardano.Ledger.Constrained.Preds.PParams (pParamsStage)
import Test.Cardano.Ledger.Constrained.Preds.Repl (goRepl)
import Test.Cardano.Ledger.Constrained.Preds.Universes
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.Solver (toolChain, toolChainSub)
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.PrettyCore (pcTxCert)
import Test.Cardano.Ledger.Generic.Proof
import Test.QuickCheck

import Cardano.Crypto.Hash.Class (Hash)
import Cardano.Crypto.VRF.Class (VerKeyVRF)
import Cardano.Ledger.Crypto (HASH, VRF)

-- =============================================
-- Shelley Cert Targets

sRegKey :: Target era (StakeCredential (EraCrypto era) -> ShelleyTxCert era)
sRegKey = Constr "sRegKey" (\x -> ShelleyTxCertDelegCert (ShelleyRegCert x))

sUnRegKey :: Target era (StakeCredential (EraCrypto era) -> ShelleyTxCert era)
sUnRegKey = Constr "UnRegKey" (\x -> ShelleyTxCertDelegCert (ShelleyUnRegCert x))

sDelegStake :: Target era (StakeCredential (EraCrypto era) -> KeyHash 'StakePool (EraCrypto era) -> ShelleyTxCert era)
sDelegStake = Constr "sDelegStake" (\x y -> ShelleyTxCertDelegCert (ShelleyDelegCert x y))

sRegPool :: Target era (PoolParams (EraCrypto era) -> ShelleyTxCert era)
sRegPool = Constr "sRegPool" (\x -> ShelleyTxCertPool (RegPool x))

sRetirePool :: Target era (KeyHash 'StakePool (EraCrypto era) -> EpochNo -> ShelleyTxCert era)
sRetirePool = Constr "sRetirePool" (\x e -> ShelleyTxCertPool (RetirePool x e))

sMirDistribute :: Target era (MIRPot -> Map (Credential 'Staking (EraCrypto era)) DeltaCoin -> ShelleyTxCert era)
sMirDistribute = Constr "sMirDistribute" (\x m -> ShelleyTxCertMir (MIRCert x (StakeAddressesMIR m)))

sMirShift :: Target era (MIRPot -> Coin -> ShelleyTxCert era)
sMirShift = Constr "sMirShift" (\x c -> ShelleyTxCertMir (MIRCert x (SendToOppositePotMIR c)))

sGovern ::
  Target
    era
    ( KeyHash 'Genesis (EraCrypto era) ->
      KeyHash 'GenesisDelegate (EraCrypto era) ->
      Hash (HASH (EraCrypto era)) (VerKeyVRF (VRF (EraCrypto era))) ->
      ShelleyTxCert era
    )
sGovern = Constr "sGovern" (\a b c -> ShelleyTxCertGenesis (ConstitutionalDelegCert a b c))

-- ==========================================
-- Conway Cert Targets

cRegKey :: Target era (StakeCredential (EraCrypto era) -> Maybe Coin -> ConwayTxCert era)
cRegKey = Constr "cRegKey" (\x y -> ConwayTxCertDeleg (ConwayRegCert x (maybeToStrictMaybe y)))

cUnRegKey :: Target era (StakeCredential (EraCrypto era) -> Maybe Coin -> ConwayTxCert era)
cUnRegKey = Constr "cUnRegKey" (\x y -> ConwayTxCertDeleg (ConwayUnRegCert x (maybeToStrictMaybe y)))

cDelegStake :: Target era (StakeCredential (EraCrypto era) -> KeyHash 'StakePool (EraCrypto era) -> ConwayTxCert era)
cDelegStake = Constr "cDelegStake" (\x y -> ConwayTxCertDeleg (ConwayDelegCert x (DelegStake y)))

cDelegVote :: Target era (StakeCredential (EraCrypto era) -> Credential 'Voting (EraCrypto era) -> ConwayTxCert era)
cDelegVote = Constr "cDelegVote" (\x y -> ConwayTxCertDeleg (ConwayDelegCert x (DelegVote y)))

cDelegStakeVote ::
  Target
    era
    ( StakeCredential (EraCrypto era) ->
      KeyHash 'StakePool (EraCrypto era) ->
      Credential 'Voting (EraCrypto era) ->
      ConwayTxCert era
    )
cDelegStakeVote = Constr "cDelegStakeVote" (\x y z -> ConwayTxCertDeleg (ConwayDelegCert x (DelegStakeVote y z)))

cRegDelegStake :: Target era (StakeCredential (EraCrypto era) -> KeyHash 'StakePool (EraCrypto era) -> Coin -> ConwayTxCert era)
cRegDelegStake = Constr "cRegDelegStake" (\x y c -> ConwayTxCertDeleg (ConwayRegDelegCert x (DelegStake y) c))

cRegDelegVote :: Target era (StakeCredential (EraCrypto era) -> Credential 'Voting (EraCrypto era) -> Coin -> ConwayTxCert era)
cRegDelegVote = Constr "cRegDelegVote" (\x y c -> ConwayTxCertDeleg (ConwayRegDelegCert x (DelegVote y) c))

cRegDelegStakeVote ::
  Target
    era
    ( StakeCredential (EraCrypto era) ->
      KeyHash 'StakePool (EraCrypto era) ->
      Credential 'Voting (EraCrypto era) ->
      Coin ->
      ConwayTxCert era
    )
cRegDelegStakeVote = Constr "cRegDelegStakeVote" (\w x y c -> ConwayTxCertDeleg (ConwayRegDelegCert w (DelegStakeVote x y) c))

cRegPool :: Target era (PoolParams (EraCrypto era) -> ConwayTxCert era)
cRegPool = Constr "cRegPool" (\x -> ConwayTxCertPool (RegPool x))

cRetirePool :: Target era (KeyHash 'StakePool (EraCrypto era) -> EpochNo -> ConwayTxCert era)
cRetirePool = Constr "cRetirePool" (\x e -> ConwayTxCertPool (RetirePool x e))

cGovern ::
  Target
    era
    ( KeyHash 'Genesis (EraCrypto era) ->
      KeyHash 'GenesisDelegate (EraCrypto era) ->
      Hash (HASH (EraCrypto era)) (VerKeyVRF (VRF (EraCrypto era))) ->
      ConwayTxCert era
    )
cGovern = Constr "cGovernT" (\a b c -> ConwayTxCertConstitutional (ConstitutionalDelegCert a b c))

-- =====================================

certsPreds :: forall era. Reflect era => Proof era -> [Pred era]
certsPreds p = case whichTxCert p of
  TxCertShelleyToBabbage ->
    [ certs :<-: (Constr "TxCertF" (fmap (TxCertF p)) ^$ shelleycerts)
    , Sized (Range 1 6) epochDelta
    , Choose
        (Range 0 5)
        shelleycerts
        [ (sRegKey ^$ stakeCred, [NotMember stakeCred (Dom rewards)])
        , (sUnRegKey ^$ deregkey, [MapMember deregkey (Lit CoinR (Coin 0)) (Left rewards)])
        ,
          ( sDelegStake ^$ stakeCred ^$ poolHash
          , [Member (Left stakeCred) (Dom rewards), Member (Left poolHash) (Dom regPools)]
          )
        ,
          ( sRetirePool ^$ poolHash ^$ epoch
          , [Member (Left poolHash) (Dom regPools), epoch :<-: (Constr "+" (+) ^$ currentEpoch ^$ epochDelta)]
          )
        , (sRegPool ^$ poolParams, [Random poolParams])
        ,
          ( sMirDistribute ^$ pot ^$ mirdistr
          , [Random pot, Sized (Range 1 6) (Dom mirdistr), Random mirdistr] -- TODO Sum of the Distr must have some bounds
          )
        , (sMirShift ^$ pot ^$ mircoin, [Random pot, Random mircoin])
        ]
    ]
  TxCertConwayToConway ->
    [ certs :<-: (Constr "TxCertF" (fmap (TxCertF p)) ^$ conwaycerts)
    , Sized (Range 1 6) epochDelta
    , Choose
        (Range 4 6)
        conwaycerts
        [
          ( cRegKey ^$ stakeCred ^$ mkeydeposit
          ,
            [ NotMember stakeCred (Dom rewards)
            , Maybe mkeydeposit (idTarget kd) [kd :=: (keyDepAmt p)]
            ]
          )
        ,
          ( cUnRegKey ^$ stakeCred ^$ mkeydeposit
          ,
            [ MapMember stakeCred (Lit CoinR (Coin 0)) (Left rewards)
            , Maybe mkeydeposit (idTarget kd) [MapMember stakeCred kd (Left stakeDeposits)]
            ]
          )
        ,
          ( cDelegStake ^$ stakeCred ^$ poolHash
          , [Member (Left stakeCred) (Dom rewards), Member (Left poolHash) (Dom regPools)]
          )
        , (cDelegVote ^$ stakeCred ^$ vote, [Member (Left stakeCred) (Dom rewards), Member (Left vote) voteUniv])
        ,
          ( cRegDelegStake ^$ stakeCred ^$ poolHash ^$ kd
          , [Member (Left stakeCred) (Dom rewards), Member (Left poolHash) (Dom regPools), kd :=: (keyDepAmt p)]
          )
        ,
          ( cRegDelegVote ^$ stakeCred ^$ vote ^$ kd
          , [Member (Left stakeCred) (Dom rewards), Member (Left vote) voteUniv, kd :=: (keyDepAmt p)]
          )
        ,
          ( cRegDelegStakeVote ^$ stakeCred ^$ poolHash ^$ vote ^$ kd
          ,
            [ Member (Left stakeCred) (Dom rewards)
            , Member (Left vote) voteUniv
            , Member (Left poolHash) (Dom regPools)
            , kd :=: (keyDepAmt p)
            ]
          )
        , (cRegPool ^$ poolParams, [Random poolParams])
        ,
          ( cRetirePool ^$ poolHash ^$ epoch
          , [Member (Left poolHash) (Dom regPools), epoch :<-: (Constr "+" (+) ^$ currentEpoch ^$ epochDelta)]
          )
        ]
    ]
  where
    stakeCred = var "stakeCred" CredR
    deregkey = var "destakeCred" CredR
    poolHash = var "poolHash" PoolHashR
    epoch = var "epoch" EpochR
    shelleycerts = var "shelleycerts" (ListR ShelleyTxCertR)
    conwaycerts = var "conwaycerts" (ListR ConwayTxCertR)
    poolParams = var "poolParams" PoolParamsR
    pot = var "pot" MIRPotR
    mirdistr = var "mirdistr" (MapR CredR DeltaCoinR)
    mircoin = var "mircoin" CoinR
    mkeydeposit = var "mkeyDeposit" (MaybeR CoinR)
    kd = var "kd" CoinR
    vote = var "vote" VCredR
    epochDelta = var "epochDelta" EpochR

certsStage ::
  Reflect era =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
certsStage proof subst0 = do
  let preds = certsPreds proof
  toolChainSub standardOrderInfo preds subst0

main :: IO ()
main = do
  let proof = Conway Standard
  -- Babbage Standard
  env <-
    generate
      ( toolChain
          proof
          [ pParamsStage
          , universeStage
          , vstateStage
          , pstateStage
          , dstateStage
          , certsStage
          ]
      )
  -- rewritten <- snd <$> generate (rewriteGen (1,  certsPreds proof))
  -- putStrLn (show rewritten)
  certsv <- monadTyped (findVar (unVar certs) env)
  putStrLn (show (ppList (\(TxCertF _ x) -> pcTxCert proof x) certsv))
  _ <- goRepl proof env ""
  pure ()
