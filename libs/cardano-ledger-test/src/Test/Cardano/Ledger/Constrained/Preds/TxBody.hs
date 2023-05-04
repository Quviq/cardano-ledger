{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- {-# OPTIONS_GHC -Wno-unused-imports #-}
-- {-# OPTIONS_GHC -Wno-unused-binds #-}

module Test.Cardano.Ledger.Constrained.Preds.TxBody where

-- import Cardano.Ledger.Api(getMinFeeTx)
import Cardano.Ledger.Address (Withdrawals (..))
import Cardano.Ledger.BaseTypes (EpochNo (..), StrictMaybe (..), maybeToStrictMaybe)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Conway.Delegation (
  ConwayDCert (..),
  ConwayDelegCert (..),
  ConwayEraDCert,
  Delegatee (..),
 )
import Cardano.Ledger.Core (EraTxBody (..), coinTxOutL)
import Cardano.Ledger.Credential (StakeCredential)
import Cardano.Ledger.Crypto (StandardCrypto)
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.Shelley.AdaPots (consumedTxBody, producedTxBody)
import Cardano.Ledger.Shelley.Delegation (
  DCert,
  Delegation (..),
  PoolCert (..),
  ShelleyDCert (..),
  ShelleyDelegCert (..),
  ShelleyEraDCert (..),
 )
import Cardano.Ledger.TxIn (TxIn (..))
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Lens.Micro
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Classes
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Examples (checkForSoundness)
import Test.Cardano.Ledger.Constrained.Monad (monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.DPState (dstateStage, pstateStage, vstateStage)
import Test.Cardano.Ledger.Constrained.Preds.PParams (pParamsStage)
import Test.Cardano.Ledger.Constrained.Preds.TxOut (txOutPreds)
import Test.Cardano.Ledger.Constrained.Preds.Universes
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.Size (OrdCond (..))
import Test.Cardano.Ledger.Constrained.Solver (toolChainSub)
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Fields (TxBodyField (..))
import Test.Cardano.Ledger.Generic.PrettyCore (PrettyC (..), pcTxBody)
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Updaters (newTxBody)
import Test.QuickCheck

-- import Cardano.Ledger.Core (EraTxOut (..), TxOut, addrTxOutL, coinTxOutL, valueTxOutL)
import Cardano.Ledger.Shelley.LedgerState (keyCertsRefunds, totalCertsDeposits)

-- =======================================================================================
-- How to construct an actual TxBody from an (Env era) that stores a
-- variable for each of the 'bodyNames'. If one of these vars is not
-- in the Env them, that component of the TxBody will use the default value
-- stored in Test.Cardano.Ledger.Generic.Fields(initialTxBody)

bodyNames :: [String]
bodyNames =
  [ "inputs"
  , "refInputs"
  , "collateral"
  , "outputs"
  , "collateralReturn"
  , "totalCol"
  , "certs"
  , "withdrawals"
  , "txfee"
  , "ttl"
  , "validityInterval"
  , "mint"
  , "reqSignerHashes"
  , "networkID"
  ]

lookupTxBody :: Env era -> String -> [TxBodyField era]
lookupTxBody (Env m) name = case (name, Map.lookup name m) of
  ("inputs", Just (Payload (SetR TxInR) t _)) -> [Inputs t]
  ("refInputs", Just (Payload (SetR TxInR) t _)) -> [RefInputs t]
  ("collateral", Just (Payload (SetR TxInR) t _)) -> [Collateral t]
  ("outputs", Just (Payload (ListR (TxOutR _)) ts _)) -> [Outputs' (map unTxOut ts)]
  ("collateralReturn", Just (Payload (TxOutR _) x _)) -> [CollateralReturn (SJust (unTxOut x))]
  ("totalCol", Just (Payload CoinR x _)) -> [TotalCol (SJust x)]
  ("certs", Just (Payload (ListR (DCertR _)) xs _)) -> [Certs' (map unDCertF xs)]
  ("withdrawals", Just (Payload (MapR (RewardAcntR @era) CoinR) mp _)) -> [Withdrawals' (Withdrawals mp)]
  ("txfee", Just (Payload CoinR x _)) -> [Txfee x]
  ("ttl", Just (Payload SlotNoR x _)) -> [TTL x]
  ("validityInterval", Just (Payload ValidityIntervalR x _)) -> [Vldt x]
  ("mint", Just (Payload MultiAssetR x _)) -> [Mint x]
  ("reqSignerHashes", Just (Payload (SetR WitHashR) x _)) -> [ReqSignerHashes x]
  ("networkID", Just (Payload (MaybeR NetworkR) x _)) -> [Txnetworkid (maybeToStrictMaybe x)]
  _ -> []

txBodyFromEnv :: Proof era -> Env era -> TxBody era
txBodyFromEnv proof env = unReflect newTxBody proof (concat (map (lookupTxBody env) bodyNames))

-- =====================================================================
data DCertWit era where
  DCertShelleyToBabbage :: (DCert era ~ ShelleyDCert era, ShelleyEraDCert era) => DCertWit era
  DCertConwayToConway :: (DCert era ~ ConwayDCert era, ConwayEraDCert era) => DCertWit era

whichDCert :: Proof era -> DCertWit era
whichDCert (Shelley _) = DCertShelleyToBabbage
whichDCert (Allegra _) = DCertShelleyToBabbage
whichDCert (Mary _) = DCertShelleyToBabbage
whichDCert (Alonzo _) = DCertShelleyToBabbage
whichDCert (Babbage _) = DCertShelleyToBabbage
whichDCert (Conway _) = DCertConwayToConway

-- ======================================================================
-- Reusable Targets
-- First order representations of functions that construct DCert
-- values. For use in building 'Target's. We will apply these to (Term Era t)
-- variables, (using  (:$) and (^$)) to indicate how to construct a
-- DCert from the random values assigned to those variables.
-- Thus:  delegateF (delegationF stkCred poolHash)
-- builds a random 'delegation' DCert from the random values assigned to
-- 'Term's :  'stkCred' and 'poolHash', which are generated using the 'Pred's that
-- mention those 'Term's. By convention we name these "functional" targets by
-- post-fixing their names with a captial "F" or "T"
-- These may be a bit more prescriptive rather than descriptive, but you do what you have to do.

regKeyF :: Proof era -> Term era (StakeCredential (EraCrypto era)) -> Target era (DCertF era)
regKeyF p x = case whichDCert p of
  DCertShelleyToBabbage -> Constr "regKeyF" (DCertF p . ShelleyDCertDelegCert . RegKey) ^$ x
  DCertConwayToConway -> Constr "regKeyF" (DCertF p . ConwayDCertDeleg . (`ConwayRegCert` SNothing)) ^$ x

deRegKeyF :: Proof era -> Term era (StakeCredential (EraCrypto era)) -> Target era (DCertF era)
deRegKeyF p x = case whichDCert p of
  DCertShelleyToBabbage -> Constr "deRegKeyF" (DCertF p . ShelleyDCertDelegCert . DeRegKey) ^$ x
  DCertConwayToConway -> Constr "deRegKeyF" (DCertF p . ConwayDCertDeleg . (`ConwayUnRegCert` SNothing)) ^$ x

delegateF ::
  Proof era ->
  Term era (StakeCredential (EraCrypto era)) ->
  Term era (KeyHash 'StakePool (EraCrypto era)) ->
  Target era (DCertF era)
delegateF p st pl = case whichDCert p of
  DCertShelleyToBabbage -> Constr "delegateF" ff ^$ st ^$ pl
    where
      ff x y = DCertF p (ShelleyDCertDelegCert (Delegate (Delegation x y)))
  DCertConwayToConway -> Constr "delegateF" ff ^$ st ^$ pl
    where
      ff x y = DCertF p (ConwayDCertDeleg (ConwayDelegCert x (DelegStake y)))

retirePoolF ::
  Proof era ->
  Term era (KeyHash 'StakePool (EraCrypto era)) ->
  Term era EpochNo ->
  Target era (DCertF era)
retirePoolF p x y = case whichDCert p of
  DCertShelleyToBabbage -> Constr "retirePoolF" (\h e -> DCertF p (ShelleyDCertPool (RetirePool h e))) ^$ x ^$ y
  DCertConwayToConway ->
    Constr "retirePoolF" (\h e -> DCertF p (ConwayDCertPool (RetirePool h e))) ^$ x ^$ y

certsRefundsT :: Reflect era => Proof era -> Target era Coin
certsRefundsT proof = Constr "certsRefunds" certsRefunds ^$ pparams proof ^$ stakeDeposits ^$ certs
  where
    certsRefunds (PParamsF _ pp) depositsx certsx = keyCertsRefunds pp (`Map.lookup` depositsx) (map unDCertF certsx)

getUtxoCoinT ::
  Reflect era =>
  Term era (TxIn (EraCrypto era)) ->
  Term era (Map (TxIn (EraCrypto era)) (TxOutF era)) ->
  Target era Coin
getUtxoCoinT feeinput spending = Constr "getUtxoCoin" getUtxoCoin ^$ feeinput ^$ spending
  where
    getUtxoCoin input mp = case Map.lookup input mp of
      Just (TxOutF _ txout) -> txout ^. coinTxOutL
      Nothing -> error "feeinput not in spending"

-- ==============================================================
-- Using constraints to generate a TxBody

txBodyPreds :: Reflect era => Proof era -> [Pred era]
txBodyPreds p =
  (txOutPreds p balanceCoin)
    ++ [ Random mint -- Compute outputs that sum to 'balanceCoin'
       , Random networkID
       , Random txoutAmount
       , Member txoutAddress addrUniv
       , Sized (ExactSize 5) (utxo p)
       , Sized (Range 2 5) inputs
       , Sized (Range 0 2) withdrawals
       , Sized (Range 0 1) refInputs
       , Sized (Range 1 2) collateral
       , Sized (Range 1 2) reqSignerHashes
       , Subset reqSignerHashes (Dom keymapUniv)
       , Subset (Dom (utxo p)) txinUniv
       , Member feeInput (Dom (utxo p))
       , Subset inputs (Dom (utxo p))
       , Member feeInput inputs
       , Subset refInputs (Dom (utxo p))
       , Subset collateral (Dom (utxo p))
       , NotMember feeInput collateral
       , spending :=: Restrict inputs (utxo p)
       , withoutfee :<-: (Constr "filter (/= feeInput)" Map.delete ^$ feeInput ^$ spending)
       , colUtxo :=: Restrict collateral (utxo p)
       , SumsTo (Right (Coin 1)) totalCol EQL [Project CoinR colUtxo]
       , nonZeroRewards :<-: (Constr "filter (/=0)" (Map.filter (/= (Coin 0))) ^$ rewards)
       , Subset (ProjS getRwdCredL CredR (Dom withdrawals)) (Dom nonZeroRewards)
       , Choose
          (Range 1 4)
          certs
          [ (regKeyF p regkey, [NotMember regkey (Dom rewards)])
          , (deRegKeyF p deregkey, [MapMember deregkey (Lit CoinR (Coin 0)) rewards])
          ,
            ( delegateF p stkCred poolHash
            , [Member poolHash (Dom regPools), Member stkCred (Dom rewards)]
            )
          ,
            ( retirePoolF p poolHash epoch
            , [Member poolHash (Dom regPools), CanFollow epoch epochNo]
            )
          ]
       , ttl :<-: (Constr "(+5)" (\x -> x + 5) ^$ currentSlot)
       , txfee :<-: getUtxoCoinT feeInput spending
       , SumsTo
          (Right (Coin 1))
          balanceCoin
          EQL
          [Project CoinR withoutfee, SumMap withdrawals, One txrefunds, One txdeposits]
       , txrefunds :<-: (Constr "certsRefunds" certsRefunds ^$ pparams p ^$ stakeDeposits ^$ certs)
       , txdeposits :<-: (Constr "certsDeposits" certsDeposits ^$ pparams p ^$ regPools ^$ certs)
       ]
  where
    spending = Var (V "spending" (MapR TxInR (TxOutR p)) No)
    withoutfee = Var (V "withoutfee" (MapR TxInR (TxOutR p)) No)
    colUtxo = Var (V "colUtxo" (MapR TxInR (TxOutR p)) No)
    regkey = var "regkey" CredR
    deregkey = var "deregkey" CredR
    stkCred = var "stkCred" CredR
    poolHash = var "poolHash" PoolHashR
    epoch = var "epoch" EpochR
    nonZeroRewards = var "nonZeroRewards" (MapR CredR CoinR)
    feeInput = var "feeInput" TxInR
    balanceCoin = Var (V "balanceCoin" CoinR No)
    certsRefunds (PParamsF _ pp) depositsx certsx = keyCertsRefunds pp (`Map.lookup` depositsx) (map unDCertF certsx)
    certsDeposits (PParamsF _ pp) regpools certsx = Coin (-n)
      where
        (Coin n) = totalCertsDeposits pp (`Map.member` regpools) (map unDCertF certsx)
    txrefunds = Var (V "txrefunds" CoinR No)
    txdeposits = Var (V "txdeposits" CoinR No)

txBodyStage ::
  Reflect era =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
txBodyStage proof subst0 = do
  let preds = txBodyPreds proof
  subst <- toolChainSub proof standardOrderInfo preds subst0
  (_env, status) <- monadTyped $ checkForSoundness preds subst
  case status of
    Nothing -> pure subst
    Just msg -> error msg

main :: IO ()
main = do
  let proof = Conway Standard -- Babbage Standard
  env <-
    generate
      ( pure []
          >>= pParamsStage proof
          >>= universeStage proof
          >>= vstateStage proof
          >>= pstateStage proof
          >>= dstateStage proof
          >>= txBodyStage proof
          >>= (\subst -> monadTyped $ substToEnv subst emptyEnv)
      )
  rewritten <- snd <$> generate (rewriteGen (1, txBodyPreds proof))
  putStrLn (show rewritten)
  certState <- monadTyped $ runTarget env dpstateT
  putStrLn (show (prettyC proof certState))
  let txb = txBodyFromEnv proof env
  putStrLn (show (pcTxBody proof txb))
  -- compute Produced and Consumed
  (PParamsF _ ppV) <- monadTyped (findVar (unVar (pparams proof)) env)
  utxoV <- monadTyped (findVar (unVar (utxo proof)) env)
  putStrLn (show (producedTxBody txb ppV certState))
  putStrLn (show (consumedTxBody txb ppV certState (liftUTxO utxoV)))

-- ========================================

bab :: Proof (BabbageEra StandardCrypto)
bab = Babbage Standard
