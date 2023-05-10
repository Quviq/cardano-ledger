{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Cardano.Ledger.Constrained.Preds.TxBody where

import Cardano.Ledger.Address (Withdrawals (..))
import Cardano.Ledger.Api (setMinFeeTx)
import Cardano.Ledger.BaseTypes (EpochNo (..), StrictMaybe (..), maybeToStrictMaybe)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Conway.TxCert (
  ConwayDelegCert (..),
  ConwayTxCert (..),
  Delegatee (..),
 )
import Cardano.Ledger.Core (EraTxBody (..), bodyTxL, coinTxOutL, feeTxBodyL)
import Cardano.Ledger.Credential (StakeCredential)
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.Pretty (PDoc, ppMap, ppSet, ppSexp)
import Cardano.Ledger.Shelley.AdaPots (consumedTxBody, producedTxBody)
import Cardano.Ledger.Shelley.TxCert (
  PoolCert (..),
  ShelleyDelegCert (..),
  ShelleyTxCert (..),
 )
import Cardano.Ledger.TxIn (TxIn (..))
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Debug.Trace
import Lens.Micro
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Classes
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Examples (checkForSoundness)
import Test.Cardano.Ledger.Constrained.Monad (Typed, monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.Certs (certsStage)
import Test.Cardano.Ledger.Constrained.Preds.DPState (dstateStage, pstateStage, vstateStage)
import Test.Cardano.Ledger.Constrained.Preds.PParams (pParamsStage)
import Test.Cardano.Ledger.Constrained.Preds.Repl (goRepl)
import Test.Cardano.Ledger.Constrained.Preds.TxOut (txOutPreds)
import Test.Cardano.Ledger.Constrained.Preds.Universes
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.Size (OrdCond (..), Size (..))
import Test.Cardano.Ledger.Constrained.Solver (toolChainSub)
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Fields (TxBodyField (..), TxField (..))
import Test.Cardano.Ledger.Generic.PrettyCore (pcScriptHash, pcScriptPurpose, pcScriptsNeeded, pcTxBody, pcTxIn, pcTxOut)
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Updaters (newTx, newTxBody)
import Test.QuickCheck

import Cardano.Ledger.Alonzo.Tx (ScriptPurpose (..))
import Cardano.Ledger.Alonzo.UTxO (AlonzoScriptsNeeded (..))
import Cardano.Ledger.Core (EraTxOut (..))
import Cardano.Ledger.Shelley.LedgerState (keyCertsRefunds, totalCertsDeposits)
import Cardano.Ledger.Shelley.UTxO (ShelleyScriptsNeeded (..))
import Cardano.Ledger.UTxO (EraUTxO (..), UTxO (..))
import Test.Cardano.Ledger.Generic.Functions (scriptsNeeded')

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
  ("totalCol", Just (Payload (MaybeR CoinR) x _)) -> [TotalCol (maybeToStrictMaybe x)]
  ("certs", Just (Payload (ListR (TxCertR _)) xs _)) -> [Certs' (map unTxCertF xs)]
  ("withdrawals", Just (Payload (MapR RewardAcntR CoinR) mp _)) -> [Withdrawals' (Withdrawals mp)]
  ("txfee", Just (Payload CoinR x _)) -> [Txfee x]
  ("ttl", Just (Payload SlotNoR x _)) -> [TTL x]
  ("validityInterval", Just (Payload ValidityIntervalR x _)) -> [Vldt x]
  ("mint", Just (Payload MultiAssetR x _)) -> [Mint x]
  ("reqSignerHashes", Just (Payload (SetR WitHashR) x _)) -> [ReqSignerHashes x]
  ("networkID", Just (Payload (MaybeR NetworkR) x _)) -> [Txnetworkid (maybeToStrictMaybe x)]
  _ -> []

txBodyFromEnv :: Proof era -> Env era -> TxBody era
txBodyFromEnv proof env = unReflect newTxBody proof (concat (map (lookupTxBody env) bodyNames))

-- ==============================================================

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

getNTxOut :: Size -> [TxOutF era] -> [TxOutF era]
getNTxOut (SzExact n) xs = take n xs
getNTxOut x _ =
  error
    ( "Non (SzExact n): "
        ++ show x
        ++ " in getNTxOut. Use (MetaSize size x) to get a random (SzExact n)."
    )

-- ==============================================================
-- Using constraints to generate a TxBody

txBodyPreds :: Reflect era => Proof era -> [Pred era]
txBodyPreds p =
  (txOutPreds p balanceCoin (outputs p))
    ++ [ MetaSize (SzRng 10 12) utxoSize -- must be bigger than max size of inputs and collateral
       , Sized (Range 2 5) inputs
       , Sized (Range 2 3) collateral
       , Random mint -- Compute outputs that sum to 'balanceCoin'
       , Random networkID
       , Sized utxoSize (utxo p)
       , utxoTxOuts :=: Elems (utxo p)
       , utxoTxOuts :<-: (Constr "getNTxOut" getNTxOut ^$ utxoSize ^$ (txoutUniv p))
       , Sized (Range 0 2) withdrawals
       , Sized (Range 0 1) refInputs
       , Sized (Range 1 2) reqSignerHashes
       , Subset reqSignerHashes (Dom keymapUniv)
       , Subset (Dom (utxo p)) txinUniv
       , Subset inputs (Dom (utxo p))
       , Subset collateral (Dom (utxo p))
       , Disjoint inputs collateral
       , Member feeInput inputs
       , Member colInput collateral
       , Subset refInputs (Dom (utxo p))
       , spending :=: Restrict inputs (utxo p)
       , withoutfee :<-: (Constr "filter (/= feeInput)" Map.delete ^$ feeInput ^$ spending)
       , colUtxo :=: Restrict collateral (utxo p)
       , SumsTo (Right (Coin 1)) sumCol EQL [ProjMap CoinR outputCoinL colUtxo]
       , GenFrom totalCol (maybeTarget ^$ sumCol)
       , nonZeroRewards :<-: (Constr "filter (/=0)" (Map.filter (/= (Coin 0))) ^$ rewards)
       , Subset (ProjS getRwdCredL CredR (Dom withdrawals)) (Dom nonZeroRewards)
       , ttl :<-: (Constr "(+5)" (\x -> x + 5) ^$ currentSlot)
       , txfee :<-: getUtxoCoinT feeInput spending
       , SumsTo
          (Right (Coin 1))
          balanceCoin
          EQL
          [ProjMap CoinR outputCoinL withoutfee, SumMap withdrawals, One txrefunds, One txdeposits]
       , txrefunds :<-: (Constr "certsRefunds" certsRefunds ^$ pparams p ^$ stakeDeposits ^$ certs)
       , txdeposits :<-: (Constr "certsDeposits" certsDeposits ^$ pparams p ^$ regPools ^$ certs)
       ]
  where
    spending = Var (V "spending" (MapR TxInR (TxOutR p)) No)
    withoutfee = Var (V "withoutfee" (MapR TxInR (TxOutR p)) No)
    colUtxo = Var (V "colUtxo" (MapR TxInR (TxOutR p)) No)
    nonZeroRewards = var "nonZeroRewards" (MapR CredR CoinR)
    balanceCoin = Var (V "balanceCoin" CoinR No)
    certsRefunds (PParamsF _ pp) depositsx certsx = keyCertsRefunds pp (`Map.lookup` depositsx) (map unTxCertF certsx)
    certsDeposits (PParamsF _ pp) regpools certsx = Coin (-n)
      where
        (Coin n) = totalCertsDeposits pp (`Map.member` regpools) (map unTxCertF certsx)
    txrefunds = Var (V "txrefunds" CoinR No)
    txdeposits = Var (V "txdeposits" CoinR No)
    sumCol = Var $ V "sumCol" CoinR No
    utxoSize = Var (V "utxoSize" SizeR No)
    utxoTxOuts = Var (V "utxoTxOuts" (ListR (TxOutR p)) No)

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
  env0 <-
    generate
      ( pure []
          >>= pParamsStage proof
          >>= universeStage proof
          >>= vstateStage proof
          >>= pstateStage proof
          >>= dstateStage proof
          >>= certsStage proof
          >>= txBodyStage proof
          >>= (\subst -> monadTyped $ substToEnv subst emptyEnv)
      )
  -- rewritten <- snd <$> generate (rewriteGen (1, txBodyPreds proof))
  -- putStrLn (show rewritten)

  -- Adjust the Env for fee
  env <- monadTyped (fixFee env0)

  -- Compute the TxBody from the fixed Env
  let txb = txBodyFromEnv proof env
  putStrLn (show (pcTxBody proof txb))

  -- compute Produced and Consumed
  certState <- monadTyped $ runTarget env dpstateT
  (PParamsF _ ppV) <- monadTyped (findVar (unVar (pparams proof)) env)
  utxoV <- monadTyped (findVar (unVar (utxo proof)) env)
  putStrLn (show (producedTxBody txb ppV certState))
  putStrLn (show (consumedTxBody txb ppV certState (liftUTxO utxoV)))
  let need = getScriptsNeeded (liftUTxO utxoV) txb
  putStrLn (show (pcScriptsNeeded proof need))
  -- enter the Repl
  goRepl proof env ""

-- ===================================================
-- At some point we will need to move this to the Tx preds
-- since the witnesses for Plutus scripts have Costs which
-- are added to the fee. And the witnesses are in the Tx, not
-- the TxBody.

-- | This term is set as part of the UTxO in the DState Preds
--   It refers to the key in the UTxO, used to pay the fee.
--   Using it, the fee is counted in both sides of the
--   Produced == Consumed computation. As the fee will
--   appear in the 'feeInput' entry in the UTxO and in
--   the 'txfee' field of the TxBody
-- E.g. Produced(Outputs 231, Fees 1343979, Deposits 0) = 1344210
--                            ^ from the 'txfee'
--      Consumed(Inputs 1344183, Refunds 27, Withdrawals 0) = 1344210
--               ^ includes amount from the 'feeInput' of the 'utxo'
feeInput :: Term era (TxIn (EraCrypto era))
feeInput = var "feeInput" TxInR

colInput :: Term era (TxIn (EraCrypto era))
colInput = var "colInput" TxInR

-- | Adjust the Env to get the right amout for the fee.
--   We need to adjust the 'utxo' and the 'txfee' variables
--   in the Env. We compute the right amount using 'setMinFeeTx'
fixFee :: Reflect era => Env era -> Typed (Env era)
fixFee env = do
  let proof = reify
  let txb = txBodyFromEnv proof env
  PParamsF _ ppV <- monadTyped (findVar (unVar (pparams proof)) env)
  feeTxIn <- monadTyped (findVar (unVar feeInput) env)
  colTxIn <- monadTyped (findVar (unVar colInput) env)
  let actualfee = (setMinFeeTx ppV (newTx proof [Body txb])) ^. (bodyTxL . feeTxBodyL)
  utxo0 <-
    trace ("\nTHERE\nfeeTxIn " ++ show (pcTxIn feeTxIn) ++ "\ncolTxIn" ++ show (pcTxIn colTxIn)) $
      monadTyped (findVar (unVar (utxo proof)) env)

  let utxo1 = fixTxInput feeTxIn actualfee utxo0
      utxo2 = fixTxInput colTxIn actualfee utxo1
      !env1 = storeVar (unVar txfee) actualfee env
      !env2 = storeVar (unVar (utxo proof)) utxo2 env1
  pure env2

fixTxInput ::
  (Reflect era) =>
  TxIn (EraCrypto era) ->
  Coin ->
  Map (TxIn (EraCrypto era)) (TxOutF era) ->
  Map (TxIn (EraCrypto era)) (TxOutF era)
fixTxInput k c m = Map.adjust (\(TxOutF p x) -> TxOutF p (x & coinTxOutL .~ c)) k m

-- ========================================

bab :: Proof (BabbageEra StandardCrypto)
bab = Babbage Standard

{-
Alonzo
--  Compared to pre-Alonzo eras, we additionally gather the certificates
--  required to authenticate collateral witnesses.
witsVKeyNeeded ::
  forall era.
  (EraTx era, AlonzoEraTxBody era) =>
  UTxO era ->
  Tx era ->
  GenDelegs (EraCrypto era) ->
  Set (KeyHash 'Witness (EraCrypto era))
witsVKeyNeeded utxo' tx genDelegs =

Shelley
-- | Collect the set of hashes of keys that needs to sign a
--  given transaction. This set consists of the txin owners,
--  certificate authors, and withdrawal reward accounts.
witsVKeyNeeded ::
  forall era.
  ( EraTx era
  , ShelleyEraTxBody era
  , ProtVerAtMost era 8
  ) =>
  UTxO era ->
  Tx era ->
  GenDelegs (EraCrypto era) ->
  Set (KeyHash 'Witness (EraCrypto era))
-}
