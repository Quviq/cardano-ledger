{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Cardano.Ledger.Constrained.Vars where

import Cardano.Ledger.Address (Addr (..), RewardAcnt (..), Withdrawals (..))
import Cardano.Ledger.Allegra.Scripts (ValidityInterval (..))
import Cardano.Ledger.Alonzo.Core (ppPricesL)
import Cardano.Ledger.BaseTypes (BlocksMade (..), EpochNo, Network (..), ProtVer (..), SlotNo (..), StrictMaybe (..))
import Cardano.Ledger.CertState (CertState (..), DState (..), FutureGenDeleg (..), PState (..), VState (..))
import qualified Cardano.Ledger.CertState as DPS (InstantaneousRewards (..))
import Cardano.Ledger.Coin (Coin (..), DeltaCoin)
import Cardano.Ledger.Core (
  EraPParams,
  PParams,
  TxBody,
  TxOut,
  Value,
  addrTxOutL,
  coinTxOutL,
  ppKeyDepositL,
  ppMaxBBSizeL,
  ppMaxBHSizeL,
  ppMaxTxSizeL,
  ppMinFeeAL,
  ppMinFeeBL,
  ppPoolDepositL,
  ppProtocolVersionL,
  valueTxOutL,
 )
import Cardano.Ledger.Credential (Credential, Ptr)
import Cardano.Ledger.EpochBoundary (SnapShot (..), SnapShots (..), Stake (..))
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Keys (GenDelegPair, GenDelegs (..), KeyHash, KeyRole (..))
import Cardano.Ledger.PoolDistr (IndividualPoolStake (..), PoolDistr (..))
import Cardano.Ledger.PoolParams (PoolParams)
import Cardano.Ledger.Shelley.LedgerState (
  AccountState (..),
  EpochState (..),
  LedgerState (..),
  NewEpochState (..),
  ShelleyPPUPState (..),
  UTxOState (..),
  smartUTxOState,
 )
import Cardano.Ledger.Shelley.TxCert (TxCert)

import Cardano.Ledger.Conway.Governance (ConwayTallyState (..))
import Cardano.Ledger.Core (PParamsHKD)
import Cardano.Ledger.Mary.Value (MultiAsset (..))
import Cardano.Ledger.Shelley.Governance (ShelleyPPUPState (..))
import qualified Cardano.Ledger.Shelley.Governance as Core (GovernanceState (..))
import Cardano.Ledger.Shelley.PParams (ProposedPPUpdates (..))
import qualified Cardano.Ledger.Shelley.PParams as Core (ProposedPPUpdates (..))
import Cardano.Ledger.Shelley.PoolRank (NonMyopic (..))
import Cardano.Ledger.Shelley.RewardUpdate (PulsingRewUpdate (Complete))
import qualified Cardano.Ledger.Shelley.RewardUpdate as RU
import Cardano.Ledger.Shelley.Rewards (Reward (..))
import Cardano.Ledger.TxIn (TxIn)
import Cardano.Ledger.UMap (compactCoinOrError, fromCompact)
import Cardano.Ledger.UTxO (UTxO (..))
import Cardano.Ledger.Val (Val (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.VMap as VMap
import Lens.Micro
import Numeric.Natural (Natural)
import Test.Cardano.Ledger.Babbage.Serialisation.Generators ()
import Test.Cardano.Ledger.Constrained.Ast (Target (..), Term (Var), constTarget, fieldToTerm, ppTarget, (^$))
import Test.Cardano.Ledger.Constrained.Classes (
  GovernanceState (..),
  PParamsF (..),
  PParamsUpdateF (..),
  ScriptF (..),
  TxCertF (..),
  TxOutF (..),
  ValueF (..),
  governanceProposedL,
  liftUTxO,
  pparamsWrapperL,
  unPParams,
  unPParamsUpdate,
  unTxOut,
  unValue,
 )
import Test.Cardano.Ledger.Constrained.Env (Access (..), AnyF (..), Field (..), Name (..), V (..))
import Test.Cardano.Ledger.Constrained.Lenses
import Test.Cardano.Ledger.Constrained.TypeRep (Rep (..), testEql, (:~:) (Refl))
import Test.Cardano.Ledger.Core.KeyPair (KeyPair (..))
import Test.Cardano.Ledger.Generic.Fields (TxBodyField (..))
import Test.Cardano.Ledger.Generic.Proof (Evidence (..), Proof (..), Reflect (..), ValueWit (..), whichValue)
import Test.Cardano.Ledger.Generic.Updaters (newTxBody)

import Cardano.Ledger.Alonzo.Scripts (ExUnits (..), Prices (..), Tag (..))
import Cardano.Ledger.Alonzo.Scripts.Data (Data (..), Datum (..))
import Cardano.Ledger.Alonzo.Tx (ScriptIntegrity (..))
import Cardano.Ledger.Alonzo.TxWits (RdmrPtr (..), Redeemers (..), TxDats (..))
import Cardano.Ledger.Hashes (DataHash, ScriptHash)
import Cardano.Ledger.Mary.Value (
  AssetName (..),
  MaryValue (..),
  MultiAsset (..),
  PolicyID (..),
  multiAssetFromList,
 )

-- ================================================================

-- | Used in Component constraints to turn a Var Term into a component (AnyF era s)
-- E.g.  (Component foo [ field fooRep fooPart1, field fooRep fooPart2])
-- Where fooPart1 :: Term era a, and fooPart2 :: Term era b
-- And fooPart1 has an (Access foo a)
-- And fooPart2 has an (Access foo b)
field :: Rep era s -> Term era t -> AnyF era s
field repS1 (Var (V name rept (Yes repS2 l))) = case testEql repS1 repS2 of
  Just Refl -> AnyF (Field name rept repS2 l)
  Nothing ->
    error
      ( unlines
          [ "Given rep and lens target do not match: "
          , "rep: " ++ show repS1
          , "lens target: " ++ show repS2
          ]
      )
field _ term = error ("field can only be applied to variable terms: " ++ show term)

getName :: Term era t -> Name era
getName (Var v) = Name v
getName x = error ("nameOf can't find the name in: " ++ show x)

-- ==============================================================
-- NewEpochState fields

type NELens era t = Lens' (NewEpochState era) t

currentEpoch :: Term era EpochNo
currentEpoch = Var (V "currentEpoch" EpochR (Yes NewEpochStateR nesELL))

prevBlocksMade :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) Natural)
prevBlocksMade = Var $ V "prevBlocksMade" (MapR PoolHashR NaturalR) (Yes NewEpochStateR nesBprevL)

currBlocksMade :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) Natural)
currBlocksMade = Var $ V "currBlocksMade" (MapR PoolHashR NaturalR) (Yes NewEpochStateR nesBcurL)

poolDistr :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) (IndividualPoolStake (EraCrypto era)))
poolDistr = Var $ V "poolDistr" (MapR PoolHashR IPoolStakeR) (Yes NewEpochStateR poolDistrL)

-- | For tests only, Like PoolDistr but has a Rational (rather than a IndividualPoolStake).
mockPoolDistr :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) Rational)
mockPoolDistr = Var $ V "mockPoolDistr" (MapR PoolHashR RationalR) No

poolDistrL :: NELens era (Map (KeyHash 'StakePool (EraCrypto era)) (IndividualPoolStake (EraCrypto era)))
poolDistrL = nesPdL . unPoolDistrL

unPoolDistrL :: Lens' (PoolDistr c) (Map (KeyHash 'StakePool c) (IndividualPoolStake c))
unPoolDistrL = lens unPoolDistr (\(PoolDistr _) x -> PoolDistr x)

-- CertState - DState

rewards :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
rewards = Var $ V "rewards" (MapR CredR CoinR) (Yes NewEpochStateR rewardsL)

rewardsL :: NELens era (Map (Credential 'Staking (EraCrypto era)) Coin)
rewardsL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsUnifiedL . rewardsUMapL

delegations :: Term era (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)))
delegations = Var $ V "delegations" (MapR CredR PoolHashR) (Yes NewEpochStateR delegationsL)

delegationsL :: NELens era (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)))
delegationsL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsUnifiedL . delegationsUMapL

stakeDeposits :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
stakeDeposits = Var $ V "stakeDeposits" (MapR CredR CoinR) (Yes NewEpochStateR stakeDepositsL)

stakeDepositsL :: NELens era (Map (Credential 'Staking (EraCrypto era)) Coin)
stakeDepositsL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsUnifiedL . stakeDepositsUMapL

ptrs :: Term era (Map Ptr (Credential 'Staking (EraCrypto era)))
ptrs = Var $ V "ptrs" (MapR PtrR CredR) (Yes NewEpochStateR ptrsL)

ptrsL :: NELens era (Map Ptr (Credential 'Staking (EraCrypto era)))
ptrsL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsUnifiedL . ptrsUMapL

futureGenDelegs :: Term era (Map (FutureGenDeleg (EraCrypto era)) (GenDelegPair (EraCrypto era)))
futureGenDelegs =
  Var $
    V
      "futureGenDelegs"
      (MapR FutureGenDelegR GenDelegPairR)
      (Yes NewEpochStateR futureGenDelegsL)

futureGenDelegsL :: NELens era (Map (FutureGenDeleg (EraCrypto era)) (GenDelegPair (EraCrypto era)))
futureGenDelegsL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsFutureGenDelegsL

genDelegs :: Term era (Map (KeyHash 'Genesis (EraCrypto era)) (GenDelegPair (EraCrypto era)))
genDelegs = Var $ V "genDelegs" (MapR GenHashR GenDelegPairR) (Yes NewEpochStateR genDelegsL)

genDelegsL :: NELens era (Map (KeyHash 'Genesis (EraCrypto era)) (GenDelegPair (EraCrypto era)))
genDelegsL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsGenDelegsL . unGenDelegsL

-- DState - InstantaneousRewards

instanReserves :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
instanReserves = Var $ V "instanReserves" (MapR CredR CoinR) (Yes NewEpochStateR instanReservesL)

instanReservesL :: NELens era (Map (Credential 'Staking (EraCrypto era)) Coin)
instanReservesL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsIRewardsL . iRReservesL

instanTreasury :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
instanTreasury = Var $ V "instanTreasury" (MapR CredR CoinR) (Yes NewEpochStateR instanTreasuryL)

instanTreasuryL :: NELens era (Map (Credential 'Staking (EraCrypto era)) Coin)
instanTreasuryL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsIRewardsL . iRTreasuryL

deltaReserves :: Term era DeltaCoin
deltaReserves = Var $ V "deltaReserves" DeltaCoinR (Yes NewEpochStateR deltaReservesNEL)

deltaReservesNEL :: NELens era DeltaCoin
deltaReservesNEL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsIRewardsL . deltaReservesL

deltaTreasury :: Term era DeltaCoin
deltaTreasury = Var $ V "deltaTreasury" DeltaCoinR (Yes NewEpochStateR deltaTreasuryNEL)

deltaTreasuryNEL :: NELens era DeltaCoin
deltaTreasuryNEL = nesEsL . esLStateL . lsCertStateL . certDStateL . dsIRewardsL . deltaTreasuryL

-- CertState - PState

regPools :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
regPools = Var $ V "regPools" (MapR PoolHashR PoolParamsR) (Yes NewEpochStateR regPoolsL)

regPoolsL :: NELens era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
regPoolsL = nesEsL . esLStateL . lsCertStateL . certPStateL . psStakePoolParamsL

futureRegPools :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
futureRegPools = Var $ V "futureRegPools" (MapR PoolHashR PoolParamsR) (Yes NewEpochStateR futureRegPoolsL)

futureRegPoolsL :: NELens era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
futureRegPoolsL = nesEsL . esLStateL . lsCertStateL . certPStateL . psFutureStakePoolParamsL

retiring :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) EpochNo)
retiring = Var $ V "retiring" (MapR PoolHashR EpochR) (Yes NewEpochStateR retiringL)

retiringL :: NELens era (Map (KeyHash 'StakePool (EraCrypto era)) EpochNo)
retiringL = nesEsL . esLStateL . lsCertStateL . certPStateL . psRetiringL

poolDeposits :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) Coin)
poolDeposits = Var $ V "poolDeposits" (MapR PoolHashR CoinR) (Yes NewEpochStateR poolDepositsL)

poolDepositsL :: NELens era (Map (KeyHash 'StakePool (EraCrypto era)) Coin)
poolDepositsL = nesEsL . esLStateL . lsCertStateL . certPStateL . psDepositsL

dreps :: Term era (Set (Credential 'Voting (EraCrypto era)))
dreps = Var $ V "dreps" (SetR VCredR) (Yes NewEpochStateR drepsL)

drepsL :: NELens era (Set (Credential 'Voting (EraCrypto era)))
drepsL = nesEsL . esLStateL . lsCertStateL . certVStateL . vsDRepsL

ccHotKeys :: Term era (Map (KeyHash 'Voting (EraCrypto era)) (KeyHash 'Voting (EraCrypto era)))
ccHotKeys = Var $ V "ccHotKeys" (MapR VHashR VHashR) (Yes NewEpochStateR ccHotKeysL)

ccHotKeysL :: NELens era (Map (KeyHash 'Voting (EraCrypto era)) (KeyHash 'Voting (EraCrypto era)))
ccHotKeysL = nesEsL . esLStateL . lsCertStateL . certVStateL . vsCCHotKeysL

-- UTxOState

utxo :: Proof era -> Term era (Map (TxIn (EraCrypto era)) (TxOutF era))
utxo p = Var $ V "utxo" (MapR TxInR (TxOutR p)) (Yes NewEpochStateR (utxoL p))

utxoL :: Proof era -> NELens era (Map (TxIn (EraCrypto era)) (TxOutF era))
utxoL proof = nesEsL . esLStateL . lsUTxOStateL . utxosUtxoL . unUtxoL proof

unUtxoL :: Proof era -> Lens' (UTxO era) (Map (TxIn (EraCrypto era)) (TxOutF era))
unUtxoL p = lens (Map.map (TxOutF p) . unUTxO) (\(UTxO _) new -> (liftUTxO new))

deposits :: Term era Coin
deposits = Var $ V "deposits" CoinR (Yes NewEpochStateR depositsL)

depositsL :: NELens era Coin
depositsL = nesEsL . esLStateL . lsUTxOStateL . utxosDepositedL

fees :: Term era Coin
fees = Var $ V "fees" CoinR (Yes NewEpochStateR feesL)

feesL :: NELens era Coin
feesL = nesEsL . esLStateL . lsUTxOStateL . utxosFeesL

ppup :: Proof era -> Term era (ShelleyPPUPState era)
ppup p = Var $ (V "ppup" (PPUPStateR p) (Yes NewEpochStateR (ppupsL p)))

ppupsL :: Proof era -> NELens era (ShelleyPPUPState era)
ppupsL (Shelley _) = nesEsL . esLStateL . lsUTxOStateL . utxosGovernanceL
ppupsL (Allegra _) = nesEsL . esLStateL . lsUTxOStateL . utxosGovernanceL
ppupsL (Mary _) = nesEsL . esLStateL . lsUTxOStateL . utxosGovernanceL
ppupsL (Alonzo _) = nesEsL . esLStateL . lsUTxOStateL . utxosGovernanceL
ppupsL (Babbage _) = nesEsL . esLStateL . lsUTxOStateL . utxosGovernanceL
ppupsL (Conway _) = error "Conway era does not have a PPUPState, in ppupsL"

-- nesEsL . esLStateL . lsUTxOStateL . utxosGovernanceL . ???

proposalsT :: Proof era -> Term era (Map (KeyHash 'Genesis (EraCrypto era)) (PParamsUpdateF era))
proposalsT p = Var (V "proposals" (MapR GenHashR (PParamsUpdateR p)) No)

futureProposalsT ::
  Proof era -> Term era (Map (KeyHash 'Genesis (EraCrypto era)) (PParamsUpdateF era))
futureProposalsT p = Var (V "futureProposals" (MapR GenHashR (PParamsUpdateR p)) No)

ppupStateT :: Proof era -> Target era (ShelleyPPUPState era)
ppupStateT p = Constr "PPUPState" ppupfun ^$ proposalsT p ^$ futureProposalsT p
  where
    ppupfun x y =
      ShelleyPPUPState
        (ProposedPPUpdates (Map.map unPParamsUpdate x))
        (ProposedPPUpdates (Map.map unPParamsUpdate y))

governanceStateT :: forall era. Proof era -> Target era (GovernanceState era)
governanceStateT p@(Shelley _) = Constr "GovernanceState" (GovernanceState p) :$ (ppupStateT p)
governanceStateT p@(Allegra _) = Constr "GovernanceState" (GovernanceState p) :$ (ppupStateT p)
governanceStateT p@(Mary _) = Constr "GovernanceState" (GovernanceState p) :$ (ppupStateT p)
governanceStateT p@(Alonzo _) = Constr "GovernanceState" (GovernanceState p) :$ (ppupStateT p)
governanceStateT p@(Babbage _) = Constr "GovernanceState" (GovernanceState p) :$ (ppupStateT p)
governanceStateT p@(Conway _) =
  Constr "GovernanceState" (GovernanceState p)
    :$ constTarget (Core.emptyGovernanceState @era)
individualPoolStakeL :: Lens' (IndividualPoolStake c) Rational
individualPoolStakeL = lens individualPoolStake (\ds u -> ds {individualPoolStake = u})

-- Incremental Stake

isPtrMapT :: Term era (Map Ptr Coin)
isPtrMapT = Var $ V "ptrMap" (MapR PtrR CoinR) (Yes NewEpochStateR ptrMapL)

ptrMapL :: Lens' (NewEpochState era) (Map Ptr Coin)
ptrMapL = nesEsL . esLStateL . lsUTxOStateL . utxosStakeDistrL . isPtrMapL

isCredMapT :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
isCredMapT = Var $ V "credMap" (MapR CredR CoinR) (Yes NewEpochStateR credMapL)

credMapL :: Lens' (NewEpochState era) (Map (Credential 'Staking (EraCrypto era)) Coin)
credMapL = nesEsL . esLStateL . lsUTxOStateL . utxosStakeDistrL . isCredMapL

-- AccountState

treasury :: Term era Coin
treasury = Var $ V "treasury" CoinR (Yes NewEpochStateR treasuryL)

treasuryL :: NELens era Coin
treasuryL = nesEsL . esAccountStateL . asTreasuryL

reserves :: Term era Coin
reserves = Var $ V "reserves" CoinR (Yes NewEpochStateR reservesL)

reservesL :: NELens era Coin
reservesL = nesEsL . esAccountStateL . asReservesL

-- EpochState

snapshots :: Term era (SnapShots (EraCrypto era))
snapshots = Var (V "snapshots" SnapShotsR (Yes NewEpochStateR snapshotsL))

snapshotsL :: NELens era (SnapShots (EraCrypto era))
snapshotsL = nesEsL . esSnapshotsL

-- | Lens' from the Core PParams to the Model PParamsF which embeds a (Proof era)
ppFL :: Proof era -> Lens' (PParams era) (PParamsF era)
ppFL p = lens (\pp -> PParamsF p pp) (\_ (PParamsF _ qq) -> qq)

prevpparams :: Proof era -> Term era (PParamsF era)
prevpparams p = Var (V "prevpparams" (PParamsR p) (Yes NewEpochStateR (nesEsL . esPrevPpL . ppFL p)))

pparams :: Proof era -> Term era (PParamsF era)
pparams p = Var (V "pparams" (PParamsR p) (Yes NewEpochStateR (nesEsL . esPpL . ppFL p)))

nmLikelihoodsT :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) [Float])
nmLikelihoodsT = Var (V "likelihoodsNM" (MapR PoolHashR (ListR FloatR)) (Yes NewEpochStateR (nesEsL . esNonMyopicL . nmLikelihoodsL)))

nmRewardPotT :: Term era Coin
nmRewardPotT = Var $ V "rewardPotNM" CoinR (Yes NewEpochStateR (nesEsL . esNonMyopicL . nmRewardPotL))

-- ===== SnapShots

-- | Helper lens that deals with the Stake newtype, and the shift from Map to VMap
stakeL :: Lens' (Stake c) (Map (Credential 'Staking c) Coin)
stakeL =
  lens
    (Map.map fromCompact . VMap.toMap . unStake)
    (\_ u -> Stake . VMap.fromMap . Map.map compactCoinOrError $ u)

-- | Helper lens that deals with the shift from Map to VMap
vmapL :: Lens' (VMap.VMap VMap.VB VMap.VB k v) (Map k v)
vmapL = lens VMap.toMap (\_ u -> VMap.fromMap u)

markStakeL :: NELens era (Map (Credential 'Staking (EraCrypto era)) Coin)
markStakeL = nesEsL . esSnapshotsL . ssStakeMarkL . ssStakeL . stakeL

markStake :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
markStake = Var (V "markStake" (MapR CredR CoinR) (Yes NewEpochStateR markStakeL))

markDelegs :: Term era (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)))
markDelegs = Var (V "markDelegs" (MapR CredR PoolHashR) (Yes NewEpochStateR markDelegsL))

markDelegsL :: NELens era (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)))
markDelegsL = nesEsL . esSnapshotsL . ssStakeMarkL . ssDelegationsL . vmapL

markPools :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
markPools = Var (V "markPools" (MapR PoolHashR PoolParamsR) (Yes NewEpochStateR markPoolsL))

markPoolsL :: NELens era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
markPoolsL = nesEsL . esSnapshotsL . ssStakeMarkL . ssPoolParamsL . vmapL

markSnapShotT :: Target era (SnapShot (EraCrypto era))
markSnapShotT = Constr "SnapShot" snapfun ^$ markStake ^$ markDelegs ^$ markPools
  where
    snapfun x y z =
      SnapShot
        (Stake (VMap.fromMap (Map.map compactCoinOrError x)))
        (VMap.fromMap y)
        (VMap.fromMap z)

setStake :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
setStake = Var (V "setStake" (MapR CredR CoinR) (Yes NewEpochStateR setStakeL))

setStakeL :: NELens era (Map (Credential 'Staking (EraCrypto era)) Coin)
setStakeL = nesEsL . esSnapshotsL . ssStakeSetL . ssStakeL . stakeL

setDelegs :: Term era (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)))
setDelegs = Var (V "setDelegs" (MapR CredR PoolHashR) (Yes NewEpochStateR setDelegsL))

setDelegsL :: NELens era (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)))
setDelegsL = nesEsL . esSnapshotsL . ssStakeSetL . ssDelegationsL . vmapL

setPools :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
setPools = Var (V "setPools" (MapR PoolHashR PoolParamsR) (Yes NewEpochStateR setPoolsL))

setPoolsL :: NELens era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
setPoolsL = nesEsL . esSnapshotsL . ssStakeSetL . ssPoolParamsL . vmapL

setSnapShotT :: Target era (SnapShot (EraCrypto era))
setSnapShotT = Constr "SnapShot" snapfun ^$ setStake ^$ setDelegs ^$ setPools
  where
    snapfun x y z =
      SnapShot
        (Stake (VMap.fromMap (Map.map compactCoinOrError x)))
        (VMap.fromMap y)
        (VMap.fromMap z)

goStake :: Term era (Map (Credential 'Staking (EraCrypto era)) Coin)
goStake = Var (V "goStake" (MapR CredR CoinR) (Yes NewEpochStateR goStakeL))

goStakeL :: NELens era (Map (Credential 'Staking (EraCrypto era)) Coin)
goStakeL = nesEsL . esSnapshotsL . ssStakeGoL . ssStakeL . stakeL

goDelegs :: Term era (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)))
goDelegs = Var (V "goDelegs" (MapR CredR PoolHashR) (Yes NewEpochStateR goDelegsL))

goDelegsL :: NELens era (Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)))
goDelegsL = nesEsL . esSnapshotsL . ssStakeGoL . ssDelegationsL . vmapL

goPools :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
goPools = Var (V "goPools" (MapR PoolHashR PoolParamsR) (Yes NewEpochStateR goPoolsL))

goPoolsL :: NELens era (Map (KeyHash 'StakePool (EraCrypto era)) (PoolParams (EraCrypto era)))
goPoolsL = nesEsL . esSnapshotsL . ssStakeGoL . ssPoolParamsL . vmapL

goSnapShotT :: Target era (SnapShot (EraCrypto era))
goSnapShotT = Constr "SnapShot" snapfun ^$ goStake ^$ goDelegs ^$ goPools
  where
    snapfun x y z =
      SnapShot
        (Stake (VMap.fromMap (Map.map compactCoinOrError x)))
        (VMap.fromMap y)
        (VMap.fromMap z)

markPoolDistr :: Term era (Map (KeyHash 'StakePool (EraCrypto era)) (IndividualPoolStake (EraCrypto era)))
markPoolDistr = Var (V "markPoolDistr" (MapR PoolHashR IPoolStakeR) No)

markPoolDistrL :: NELens era (Map (KeyHash 'StakePool (EraCrypto era)) (IndividualPoolStake (EraCrypto era)))
markPoolDistrL = nesEsL . esSnapshotsL . ssStakeMarkPoolDistrL . pooldistrHelpL

pooldistrHelpL :: Lens' (PoolDistr c) (Map (KeyHash 'StakePool c) (IndividualPoolStake c))
pooldistrHelpL = lens unPoolDistr (\_ u -> PoolDistr u)

snapShotFee :: Term era Coin
snapShotFee = Var (V "snapShotFee" CoinR No)

snapShotsT :: Target era (SnapShots (EraCrypto era))
snapShotsT =
  Constr "SnapShots" shotsfun
    :$ markSnapShotT
    :$ (Simple markPoolDistr)
    :$ setSnapShotT
    :$ goSnapShotT
    :$ (Simple snapShotFee)
  where
    shotsfun w x y z f = SnapShots w (PoolDistr x) y z f

-- ==================================================================
-- RewardUpdate

deltaT :: Term era (Maybe DeltaCoin)
deltaT = Var (V "deltaT" (MaybeR DeltaCoinR) (Yes NewEpochStateR deltaTL))

deltaTL :: NELens era (Maybe DeltaCoin)
deltaTL = nesRuL . help
  where
    help :: Lens' (StrictMaybe (PulsingRewUpdate c)) (Maybe DeltaCoin)
    help = lens view update
      where
        view SNothing = Nothing
        view (SJust (Complete x)) = Just (RU.deltaT x)
        view (SJust _) = Nothing
        update (SJust (Complete ru)) (Just change) = SJust (Complete (ru {RU.deltaT = change}))
        update _ _ = SNothing

deltaR :: Term era (Maybe DeltaCoin)
deltaR = Var (V "deltaR" (MaybeR DeltaCoinR) (Yes NewEpochStateR deltaRL))

deltaRL :: NELens era (Maybe DeltaCoin)
deltaRL = nesRuL . help
  where
    help :: Lens' (StrictMaybe (PulsingRewUpdate c)) (Maybe DeltaCoin)
    help = lens view update
      where
        view SNothing = Nothing
        view (SJust (Complete x)) = Just (RU.deltaR x)
        view (SJust _) = Nothing
        update (SJust (Complete ru)) (Just change) = SJust (Complete (ru {RU.deltaR = change}))
        update _ _ = SNothing

deltaF :: Term era (Maybe DeltaCoin)
deltaF = Var (V "deltaF" (MaybeR DeltaCoinR) (Yes NewEpochStateR deltaFL))

deltaFL :: NELens era (Maybe DeltaCoin)
deltaFL = nesRuL . help
  where
    help :: Lens' (StrictMaybe (PulsingRewUpdate c)) (Maybe DeltaCoin)
    help = lens view update
      where
        view SNothing = Nothing
        view (SJust (Complete x)) = Just (RU.deltaF x)
        view (SJust _) = Nothing
        update (SJust (Complete ru)) (Just change) = SJust (Complete (ru {RU.deltaF = change}))
        update _ _ = SNothing

rewardSet :: Term era (Map (Credential 'Staking (EraCrypto era)) (Set (Reward (EraCrypto era))))
rewardSet = Var (V "rewardSet" (MapR CredR (SetR RewardR)) No)

rewardSetL :: NELens era (Maybe (Map (Credential 'Staking (EraCrypto era)) (Set (Reward (EraCrypto era)))))
rewardSetL = nesRuL . help
  where
    help :: Lens' (StrictMaybe (PulsingRewUpdate c)) (Maybe (Map (Credential 'Staking c) (Set (Reward c))))
    help = lens view update
      where
        view SNothing = Nothing
        view (SJust (Complete x)) = Just (RU.rs x)
        view (SJust _) = Nothing
        update (SJust (Complete ru)) (Just change) = SJust (Complete (ru {RU.rs = change}))
        update _ _ = SNothing

-- ===================================================================
-- Non Access variables

totalAda :: Term era Coin
totalAda = Var $ V "totalAda" CoinR No

utxoCoin :: Term era Coin
utxoCoin = Var $ V "utxoCoin" CoinR No

-- | The universe of Staking Credentials. A credential is either KeyHash of a ScriptHash
--   Any Plutus scripts in this Universe are NOT Spending scripts, so they do not need a Redeemer
credsUniv :: Term era (Set (Credential 'Staking (EraCrypto era)))
credsUniv = Var $ V "credsUniv" (SetR CredR) No

-- | The universe of Staking Credentials. A credential is either KeyHash of a ScriptHash
--   All Plutus scripts in this Universe are SPENDING scripts, so they will need a Redeemer
--   Use this ONLY in the Pay-part of an Address (Do not use this in the Stake-part of an Address)
spendCredsUniv :: Term era (Set (Credential 'Payment (EraCrypto era)))
spendCredsUniv = Var $ V "spendCredsUniv" (SetR PCredR) No

-- | The universe of Voting Credentials. A credential is either KeyHash of a ScriptHash
voteUniv :: Term era (Set (Credential 'Voting (EraCrypto era)))
voteUniv = Var $ V "voteUniv" (SetR VCredR) No

-- | The universe of Payment Credentials. A credential is either KeyHash of a ScriptHash
--   We only find payment credentials in the Payment part of an Addr.
payUniv :: Term era (Set (Credential 'Payment (EraCrypto era)))
payUniv = Var $ V "payUniv" (SetR PCredR) No

-- | The universe of Scripts (and their hashes) useable in spending contexts
--  That means if they are Plutus scripts then they will be passed an additional
--  argument (the TxInfo context)
spendscriptUniv :: Proof era -> Term era (Map (ScriptHash (EraCrypto era)) (ScriptF era))
spendscriptUniv p = Var (V "spendscriptUniv" (MapR ScriptHashR (ScriptR p)) No)

-- | The universe of Scripts (and their hashes) useable in contexts other than Spending
scriptUniv :: Proof era -> Term era (Map (ScriptHash (EraCrypto era)) (ScriptF era))
scriptUniv p = Var (V "scriptUniv" (MapR ScriptHashR (ScriptR p)) No)

-- | The universe of Data (and their hashes)
dataUniv :: Era era => Term era (Map (DataHash (EraCrypto era)) (Data era))
dataUniv = Var (V "dataUniv" (MapR DataHashR DataR) No)

-- | The universe of StakePool key hashes. These hashes hash the cold key of the
--   Pool operators.
poolHashUniv :: Term era (Set (KeyHash 'StakePool (EraCrypto era)))
poolHashUniv = Var $ V "poolHashUniv" (SetR PoolHashR) No

-- | The universe of the Genesis key hashes and their signing and validating GenDelegPairs
genesisHashUniv :: Term era (Map (KeyHash 'Genesis (EraCrypto era)) (GenDelegPair (EraCrypto era)))
genesisHashUniv = Var $ V "genesisHashUniv" (MapR GenHashR GenDelegPairR) No

voteHashUniv :: Term era (Set (KeyHash 'Voting (EraCrypto era)))
voteHashUniv = Var $ V "voteHashUniv" (SetR VHashR) No

-- | The universe of TxIns. Pairs of TxId: hashes of previously run transaction bodies,
--   and TxIx: indexes of one of the bodies outputs.
txinUniv :: Term era (Set (TxIn (EraCrypto era)))
txinUniv = Var $ V "txinUniv" (SetR TxInR) No

txoutUniv :: Proof era -> Term era [TxOutF era]
txoutUniv p = Var $ V "txoutUniv" (ListR (TxOutR p)) No

datumsUniv :: Era era => Term era [Datum era]
datumsUniv = Var (V "datumsUniv" (ListR DatumR) No)

multiAssetUniv :: Term era [MultiAsset (EraCrypto era)]
multiAssetUniv = Var (V "multiAssetUniv" (ListR MultiAssetR) No)

-- | The universe of key hashes, and the signing and validating key pairs they represent.
keymapUniv :: Term era (Map (KeyHash 'Witness (EraCrypto era)) (KeyPair 'Witness (EraCrypto era)))
keymapUniv = Var (V "keymapUniv" (MapR WitHashR KeyPairR) No)

currentSlot :: Term era SlotNo
currentSlot = Var (V "currentSlot" SlotNoR No)

-- See also currentEpoch in NewEpochState fields

network :: Term era Network
network = Var (V "network" NetworkR No)

addrUniv :: Term era (Set (Addr (EraCrypto era)))
addrUniv = Var $ V "addrUniv" (SetR AddrR) No

ptrUniv :: Term era (Set Ptr)
ptrUniv = Var $ V "ptrUniv" (SetR PtrR) No

-- ====================================================================
-- Targets for sub types of NewEpochState
-- A Target assembles variables into data stuctures. The main concern
-- is transforming the types used in the variable model into the real types
-- stored in the data structures. 4 examples of such transformation
-- 1) Wrapping and unwraping newtypes like StakeDistr
-- 2) Transforming Coin into (CompactForm Coin) a Word64
-- 3) Transforming Data.Map into Data.VMap
-- 4) Transforming the Models view of Data Families (TxOut, Value, PParams, PParamsUpdate) into
--    the data structures view.
--
-- The strategy we use is to define a "constructor function" which accepts the model types,
-- and which converts the model types into the data structure types. We then wrap this
-- "constructor function" in the "Constr" of Target. See 'newEpochStateConstr',
-- 'utxofun' and 'dstate' for examples of how this is done.

-- | Abstract constuctor function for NewEpochState
newEpochStateConstr ::
  Proof era ->
  EpochNo ->
  Map (KeyHash 'StakePool (EraCrypto era)) Natural ->
  Map (KeyHash 'StakePool (EraCrypto era)) Natural ->
  EpochState era ->
  Map (KeyHash 'StakePool (EraCrypto era)) (IndividualPoolStake (EraCrypto era)) ->
  NewEpochState era
newEpochStateConstr
  proof
  nesEL'
  nesBprev'
  nesBcur'
  nesEs'
  nesPd' =
    NewEpochState
      nesEL'
      (BlocksMade nesBprev')
      (BlocksMade nesBcur')
      nesEs'
      SNothing
      (PoolDistr nesPd')
      ( case proof of
          Shelley _ -> UTxO Map.empty
          Allegra _ -> ()
          Mary _ -> ()
          Alonzo _ -> ()
          Babbage _ -> ()
          Conway _ -> ()
      )

-- | Target for NewEpochState
newEpochStateT :: Proof era -> Target era (NewEpochState era)
newEpochStateT proof =
  Constr "NewEpochState" (newEpochStateConstr proof)
    ^$ currentEpoch
    ^$ prevBlocksMade
    ^$ currBlocksMade
    :$ epochStateT proof
    ^$ poolDistr

-- | Target for EpochState
epochStateT :: Proof era -> Target era (EpochState era)
epochStateT proof =
  Constr "EpochState" epochStateFun
    :$ accountStateT
    :$ snapShotsT
    :$ ledgerStateT proof
    ^$ prevpparams proof
    ^$ pparams proof
  where
    epochStateFun a s l pp p = EpochState a s l (unPParams pp) (unPParams p) (NonMyopic Map.empty (Coin 0))

-- | Target for AccountState
accountStateT :: Target era AccountState
accountStateT = Constr "AccountState" AccountState ^$ treasury ^$ reserves

-- | Target for LedgerState
ledgerStateT :: Proof era -> Target era (LedgerState era)
ledgerStateT proof = Constr "LedgerState" LedgerState :$ utxoStateT proof :$ dpstateT

-- | Target for UTxOState
utxoStateT :: Proof era -> Target era (UTxOState era)
utxoStateT p = Constr "UTxOState" (utxofun p) ^$ (pparams p) ^$ utxo p ^$ deposits ^$ fees :$ governanceStateT p
  where
    utxofun ::
      Proof era ->
      PParamsF era ->
      Map (TxIn (EraCrypto era)) (TxOutF era) ->
      Coin ->
      Coin ->
      GovernanceState era ->
      UTxOState era
    utxofun (Shelley _) (PParamsF _ pp) u c1 c2 (GovernanceState _ x) = smartUTxOState pp (liftUTxO u) c1 c2 x
    utxofun (Mary _) (PParamsF _ pp) u c1 c2 (GovernanceState _ x) = smartUTxOState pp (liftUTxO u) c1 c2 x
    utxofun (Allegra _) (PParamsF _ pp) u c1 c2 (GovernanceState _ x) = smartUTxOState pp (liftUTxO u) c1 c2 x
    utxofun (Alonzo _) (PParamsF _ pp) u c1 c2 (GovernanceState _ x) = smartUTxOState pp (liftUTxO u) c1 c2 x
    utxofun (Babbage _) (PParamsF _ pp) u c1 c2 (GovernanceState _ x) = smartUTxOState pp (liftUTxO u) c1 c2 x
    utxofun (Conway _) (PParamsF _ pp) u c1 c2 (GovernanceState _ x) = smartUTxOState pp (liftUTxO u) c1 c2 x

-- | Target for CertState
dpstateT :: Target era (CertState era)
dpstateT = Constr "CertState" CertState :$ vstateT :$ pstateT :$ dstateT

-- | Target for VState
vstateT :: Target era (VState era)
vstateT = Constr "VState" VState ^$ dreps ^$ ccHotKeys

-- | Target for PState
pstateT :: Target era (PState era)
pstateT = Constr "PState" PState ^$ regPools ^$ futureRegPools ^$ retiring ^$ poolDeposits

-- | Target for DState
dstateT :: Target era (DState era)
dstateT =
  Constr "DState" dstate
    ^$ rewards
    ^$ stakeDeposits
    ^$ delegations
    ^$ ptrs
    ^$ futureGenDelegs
    ^$ genDelegs
    :$ instantaneousRewardsT

-- | Abstract construcor function for DState
dstate ::
  Map (Credential 'Staking (EraCrypto era)) Coin ->
  Map (Credential 'Staking (EraCrypto era)) Coin ->
  Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era)) ->
  Map Ptr (Credential 'Staking (EraCrypto era)) ->
  Map (FutureGenDeleg (EraCrypto era)) (GenDelegPair (EraCrypto era)) ->
  Map (KeyHash 'Genesis (EraCrypto era)) (GenDelegPair (EraCrypto era)) ->
  DPS.InstantaneousRewards (EraCrypto era) ->
  DState era
dstate rew dep deleg ptr fgen gen instR =
  DState (unSplitUMap (Split rew dep deleg undefined ptr)) fgen (GenDelegs gen) instR

instantaneousRewardsT :: Target era (DPS.InstantaneousRewards (EraCrypto era))
instantaneousRewardsT =
  Constr "InstantaneousRewards" DPS.InstantaneousRewards
    ^$ instanReserves
    ^$ instanTreasury
    ^$ deltaReserves
    ^$ deltaTreasury

-- | A String that pretty prints the complete set of variables
allvars :: String
allvars = show (ppTarget (newEpochStateT (Shelley Standard)))

-- =====================================================================
-- PParams fields

withEraPParams :: forall era a. Proof era -> (EraPParams era => a) -> a
withEraPParams (Shelley _) x = x
withEraPParams (Mary _) x = x
withEraPParams (Allegra _) x = x
withEraPParams (Alonzo _) x = x
withEraPParams (Babbage _) x = x
withEraPParams (Conway _) x = x

-- | ProtVer in pparams
protVer :: Proof era -> Term era ProtVer
protVer proof =
  Var
    ( V
        "protVer"
        (ProtVerR proof)
        (Yes (PParamsR proof) $ withEraPParams proof (pparamsWrapperL . ppProtocolVersionL))
    )

-- | ProtVer in prevpparams
prevProtVer :: Proof era -> Term era ProtVer
prevProtVer proof =
  Var
    ( V
        "prevProtVer"
        (ProtVerR proof)
        (Yes (PParamsR proof) $ withEraPParams proof (pparamsWrapperL . ppProtocolVersionL))
    )

minFeeA :: Proof era -> Term era Coin
minFeeA proof =
  Var
    ( V
        "minFeeA"
        CoinR
        (Yes (PParamsR proof) $ withEraPParams proof (pparamsWrapperL . ppMinFeeAL))
    )

minFeeB :: Proof era -> Term era Coin
minFeeB proof =
  Var
    ( V
        "minFeeB"
        CoinR
        (Yes (PParamsR proof) $ withEraPParams proof (pparamsWrapperL . ppMinFeeBL))
    )

-- ppPrices :: Proof era -> Term era Prices
-- ppPrices proof = Var (V "ppPrices" undefined) (Yes (PParamsR proof) $ withEraPParams proof (pparamsWrapperL . ppPricesL))

-- | Max Block Body Size
maxBBSize :: Proof era -> Term era Natural
maxBBSize p =
  Var
    ( V
        "maxBBSize"
        NaturalR
        (Yes (PParamsR p) (withEraPParams p (pparamsWrapperL . ppMaxBBSizeL)))
    )

-- | Max Tx Size
maxTxSize :: Proof era -> Term era Natural
maxTxSize p =
  Var
    ( V
        "maxTxSize"
        NaturalR
        (Yes (PParamsR p) (withEraPParams p (pparamsWrapperL . ppMaxTxSizeL)))
    )

-- | Max Block Header Size
maxBHSize :: Proof era -> Term era Natural
maxBHSize p =
  Var
    ( V
        "maxBHSize"
        NaturalR
        (Yes (PParamsR p) (withEraPParams p (pparamsWrapperL . ppMaxBHSizeL)))
    )

poolDepAmt :: Proof era -> Term era Coin
poolDepAmt p =
  Var $
    V
      "poolDepAmt"
      CoinR
      (Yes (PParamsR p) (withEraPParams p (pparamsWrapperL . ppPoolDepositL)))

keyDepAmt :: Proof era -> Term era Coin
keyDepAmt p =
  Var $
    V
      "keyDepAmt"
      CoinR
      (Yes (PParamsR p) (withEraPParams p (pparamsWrapperL . ppKeyDepositL)))

-- =================================================================
-- TxBody vars

inputs :: Term era (Set (TxIn (EraCrypto era)))
inputs = Var $ V "inputs" (SetR TxInR) No

collateral :: Term era (Set (TxIn (EraCrypto era)))
collateral = Var $ V "collateral" (SetR TxInR) No

refInputs :: Term era (Set (TxIn (EraCrypto era)))
refInputs = Var $ V "refInputs" (SetR TxInR) No

outputs :: Proof era -> Term era [TxOutF era]
outputs p = Var $ V "outputs" (ListR (TxOutR p)) No

collateralReturn :: Proof era -> Term era (TxOutF era)
collateralReturn p = Var $ V "collateralReturn" (TxOutR p) No

totalCol :: Term era (Maybe Coin)
totalCol = Var $ V "totalCol" (MaybeR CoinR) No

certs :: Reflect era => Term era [TxCertF era]
certs = Var $ V "certs" (ListR (TxCertR reify)) No

withdrawals :: forall era. Term era (Map (RewardAcnt (EraCrypto era)) Coin)
withdrawals = Var $ V "withdrawals" (MapR (RewardAcntR @era) CoinR) No

txfee :: Term era Coin
txfee = Var $ V "txfee" CoinR No

ttl :: Term era SlotNo
ttl = Var $ V "ttl" SlotNoR No

validityInterval :: Term era ValidityInterval
validityInterval = Var $ V "validityInterval" ValidityIntervalR No

mint :: Term era (MultiAsset (EraCrypto era))
mint = Var $ V "mint" MultiAssetR No

reqSignerHashes :: Term era (Set (KeyHash 'Witness (EraCrypto era)))
reqSignerHashes = Var $ V "reqSignerHashes" (SetR WitHashR) No

networkID :: Term era (Maybe Network)
networkID = Var $ V "networkID" (MaybeR NetworkR) No

redeemers :: Reflect era => Term era (Map RdmrPtr (Data era, ExUnits))
redeemers = Var $ V "redeemers" (MapR RdmrPtrR (PairR DataR ExUnitsR)) No

txdats :: Reflect era => Term era (Map (DataHash (EraCrypto era)) (Data era))
txdats = Var $ V "txdats" (MapR DataHashR DataR) No

-- ==============================================================
-- Terms and Fields for use in TxOut and TxBody

-- Lenses for use in TxBody

getRwdCredL :: Lens' (RewardAcnt c) (Credential 'Staking c)
getRwdCredL = lens getRwdCred (\r c -> r {getRwdCred = c})

txOutFL :: Lens' (TxOutF era) (TxOut era)
txOutFL = lens unTxOut (\(TxOutF p _) y -> TxOutF p y)

valueFL :: Reflect era => Lens' (Value era) (ValueF era)
valueFL = lens (ValueF reify) (\_ (ValueF _ u) -> u)

lensVC :: Val t => Lens' t Coin
lensVC = lens coin $ \t c -> modifyCoin (const c) t

valueFCoinL :: Reflect era => Lens' (ValueF era) Coin
valueFCoinL = lens (coin . unValue) (\(ValueF p v) c -> ValueF p (modifyCoin (const c) v))

outputCoinL :: Reflect era => Lens' (TxOutF era) Coin
outputCoinL =
  lens
    (\(TxOutF _ out) -> out ^. coinTxOutL)
    (\(TxOutF p out) c -> TxOutF p (out & coinTxOutL .~ c))

-- | a Field from (ValueF era) to Coin
valCoinF :: Reflect era => Field era (ValueF era) Coin
valCoinF = Field "valCoin" CoinR (ValueR reify) valueFCoinL

valCoin :: Reflect era => Term era Coin
valCoin = fieldToTerm valCoinF

maryValueMultiAssetL :: Lens' (MaryValue c) (MultiAsset c)
maryValueMultiAssetL =
  lens
    (\(MaryValue _ ma) -> ma)
    (\(MaryValue c _) ma -> MaryValue c ma)

valueFMultiAssetL :: Lens' (ValueF era) (MultiAsset (EraCrypto era))
valueFMultiAssetL = lens get put
  where
    get :: ValueF era -> MultiAsset (EraCrypto era)
    get (ValueF p x) = case whichValue p of
      ValueShelleyToAllegra -> MultiAsset Map.empty
      ValueMaryToConway -> x ^. maryValueMultiAssetL

    put :: ValueF era -> MultiAsset (EraCrypto era) -> ValueF era
    put (ValueF p x) new = case whichValue p of
      ValueShelleyToAllegra -> ValueF p x
      ValueMaryToConway -> ValueF p (x & maryValueMultiAssetL .~ new)

-- | a Field from (ValueF era) to MultiAsset
valueFMultiAssetF :: Reflect era => Field era (ValueF era) (MultiAsset (EraCrypto era))
valueFMultiAssetF = Field "valueFMultiAsset" MultiAssetR (ValueR reify) valueFMultiAssetL

valueFMultiAsset :: Reflect era => Term era (MultiAsset (EraCrypto era))
valueFMultiAsset = fieldToTerm valueFMultiAssetF

-- | a Field from (TxOut era) to (Addr era)
txoutAddressF :: Reflect era => Field era (TxOutF era) (Addr (EraCrypto era))
txoutAddressF = Field "txoutAddress" AddrR (TxOutR reify) (txOutFL . addrTxOutL)

txoutAddress :: Reflect era => Term era (Addr (EraCrypto era))
txoutAddress = fieldToTerm txoutAddressF

-- | a Field from (TxOutF era) to Coin
txoutCoinF :: Reflect era => Field era (TxOutF era) Coin
txoutCoinF = Field "txoutCoin" CoinR (TxOutR reify) outputCoinL

txoutCoin :: Reflect era => Term era Coin
txoutCoin = fieldToTerm txoutCoinF

-- | a Field from (TxOutF era) to (ValueF era)
txoutAmountF :: Reflect era => Field era (TxOutF era) (ValueF era)
txoutAmountF = Field "txoutAmount" (ValueR reify) (TxOutR reify) (txOutFL . valueTxOutL . valueFL)

txoutAmount :: Reflect era => Term era (ValueF era)
txoutAmount = fieldToTerm txoutAmountF
