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
import Cardano.Ledger.Keys (GenDelegs (..), KeyHash, KeyRole (..))
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
import Test.Cardano.Ledger.Constrained.Solver (toolChain, toolChainSub)
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Fields (TxBodyField (..), TxField (..))
import Test.Cardano.Ledger.Generic.PrettyCore

-- (pcScriptHash, pcScriptPurpose, pcScriptsNeeded, pcTxBody, pcTxIn, pcTxOut, pcKeyHash,pcGenDelegPair)
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Updaters (newTx, newTxBody)
import Test.QuickCheck

import Cardano.Ledger.Address (Addr (..))
import Cardano.Ledger.Alonzo.Tx (ScriptPurpose (..))
import Cardano.Ledger.Alonzo.UTxO (AlonzoScriptsNeeded (..))
import Cardano.Ledger.Core (EraTxOut (..), Value)
import Cardano.Ledger.Credential (Credential (..), StakeReference (..))
import Cardano.Ledger.Mary.Value (MaryValue (..))
import Cardano.Ledger.Shelley.LedgerState (keyCertsRefunds, totalCertsDeposits)
import Cardano.Ledger.Shelley.Rules (witsVKeyNeeded)
import Cardano.Ledger.Shelley.UTxO (ShelleyScriptsNeeded (..))
import Cardano.Ledger.UTxO (EraUTxO (..), UTxO (..))
import Cardano.Ledger.Val (Val (coin))
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Word (Word16)
import qualified Data.Word as Word
import System.IO.Unsafe
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

-- outputCoinL
getNTxOut :: Reflect era => Size -> TxOutF era -> [TxOutF era] -> [TxOutF era]
getNTxOut (SzExact n) feeoutput outputuniv =
  (feeoutput & outputCoinL .~ (Coin 1000000)) : take (n - 1) outputuniv
getNTxOut x _ _ =
  error
    ( "Non (SzExact n): "
        ++ show x
        ++ " in getNTxOut. Use (MetaSize size x) to get a random (SzExact n)."
    )

-- ==============================================================
-- Using constraints to generate a TxBody

txBodyPreds :: forall era. Reflect era => Proof era -> [Pred era]
txBodyPreds p =
  (txOutPreds p balanceCoin (outputs p))
    ++ [ Random mint
       , Random networkID
       , -- utxo
         MetaSize (SzRng 9 9) utxoSize -- must be bigger than sum of (maxsize inputs 5) and (mazsize collateral 3)
       , Sized utxoSize (utxo p)
       , Member (Left feeTxOut) (Rng (utxo p))
       , MapMember feeTxIn feeTxOut (Right (utxo p))
       , Subset (Dom (utxo p)) txinUniv
       , SubMap colUtxo (utxo p)
       , -- inputs
         Sized (Range 2 5) inputs
       , Member (Left feeTxIn) inputs
       , Subset inputs (Dom (utxo p))
       , -- collateral
         Disjoint inputs collateral
       , Sized (Range 2 3) collateral
       , Sized (Range 4 4) colUtxo
       , Subset (Dom colUtxo) txinUniv
       , Subset (Rng colUtxo) (colTxoutUniv p)
       , Subset collateral (Dom colUtxo)
       , Member (Left colInput) collateral -- DO we use this?
       , colRestriction :=: Restrict collateral colUtxo
       , SumsTo (Right (Coin 1)) sumCol EQL [ProjMap CoinR outputCoinL colRestriction]
       , totalCol :<-: (justTarget sumCol)
       , -- Or maybe   , GenFrom totalCol (maybeTarget ^$ sumCol)

         -- withdrawals
         Sized (Range 0 2) withdrawals
       , Subset (ProjS getRwdCredL CredR (Dom withdrawals)) (Dom nonZeroRewards)
       , nonZeroRewards :<-: (Constr "filter (/=0)" (Map.filter (/= (Coin 0))) ^$ rewards)
       , -- refInputs
         Sized (Range 0 1) refInputs
       , Subset refInputs (Dom (utxo p))
       , Sized (Range 1 2) reqSignerHashes
       , Subset reqSignerHashes (Dom keymapUniv)
       , ttl :<-: (Constr "(+5)" (\x -> x + 5) ^$ currentSlot)
       , txfee :<-: (constTarget (Coin 0))
       , -- balanceCoin, used by (txOutPreds p balanceCoin (outputs p)) go generate 'outputs' that balance
         spending :=: Restrict inputs (utxo p)
       , SumsTo
          (Right (Coin 1))
          balanceCoin
          EQL
          [ProjMap CoinR outputCoinL spending, SumMap withdrawals, One txrefunds, One txdeposits]
       , txrefunds :<-: (Constr "certsRefunds" certsRefunds ^$ pparams p ^$ stakeDeposits ^$ certs)
       , txdeposits :<-: (Constr "certsDeposits" certsDeposits ^$ pparams p ^$ regPools ^$ certs)
       ]
  where
    spending = Var (V "spending" (MapR TxInR (TxOutR p)) No)
    withoutfee = Var (V "withoutfee" (MapR TxInR (TxOutR p)) No)
    colUtxo = Var (V "colUtxo" (MapR TxInR (TxOutR p)) No)
    colRestriction = Var (V "colRestriction" (MapR TxInR (TxOutR p)) No)
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
    noScriptAddr = Var (V "noScriptAddr" (SetR AddrR) No)
    feeInput = Var (V "feeInput" TxInR No)
    feeAddr = Var (V "feeAddr" AddrR No)
    colInput = var "colInput" TxInR

txBodyStage ::
  Reflect era =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
txBodyStage proof subst0 = do
  let preds = txBodyPreds proof
  -- (_, g) <- compileGen standardOrderInfo (map (substPred subst0) preds)
  --  trace ("GRAPH\n" ++ show g) $
  subst <- toolChainSub standardOrderInfo preds subst0
  (_env, status) <- monadTyped $ checkForSoundness preds subst
  case status of
    Nothing -> pure subst
    Just msg -> error msg

main :: IO ()
main = do
  let proof = Conway Standard
  -- Babbage Standard
  -- Alonzo Standard
  -- Mary Standard
  -- Shelley Standard
  env0 <-
    generate
      ( toolChain
          proof
          [ pParamsStage
          , universeStage
          , vstateStage
          , pstateStage
          , dstateStage
          , certsStage
          , txBodyStage
          ]
      )
  -- rewritten <- snd <$> generate (rewriteGen (1, txBodyPreds proof))
  -- putStrLn (show rewritten)

  -- Adjust the Env for fee
  env <- pure env0 -- monadTyped (fixFee env0)

  -- Compute the TxBody from the fixed Env
  let txb = txBodyFromEnv proof env
  putStrLn (show (pcTxBody proof txb))

  -- compute Produced and Consumed
  certState <- monadTyped $ runTarget env dpstateT
  (PParamsF _ ppV) <- monadTyped (findVar (unVar (pparams proof)) env)
  utxoV <- monadTyped (findVar (unVar (utxo proof)) env)
  putStrLn (show (producedTxBody txb ppV certState))
  putStrLn (show (consumedTxBody txb ppV certState (liftUTxO utxoV)))
  let needS = getScriptsNeeded (liftUTxO utxoV) txb
  -- putStrLn ("Needed Scripts\n"++show (pcScriptsNeeded proof needS))
  gd <- monadTyped (findVar (unVar genDelegs) env)
  -- putStrLn (show (ppMap pcKeyHash pcGenDelegPair gd))
  let needK = witsVKeyNeeded (liftUTxO utxoV) (newTx proof [Body txb]) (GenDelegs gd)
  -- putStrLn ("Needed keys\n"++show(ppSet pcKeyHash needK))
  -- enter the Repl
  -- goRepl proof env ""
  displayTerm env (utxo proof)
  -- env1 <- generate (fixCollateral proof (Coin 500) env)
  displayTerm env collateral
  displayTerm env (var "colUtxo" (MapR TxInR (TxOutR proof)))
  displayTerm env (var "colRestriction" (MapR TxInR (TxOutR proof)))

{-
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
    -- trace ("\nTHERE\nfeeTxIn " ++ show (pcTxIn feeTxIn) ++ "\ncolTxIn" ++ show (pcTxIn colTxIn)) $
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

proof0 =  Conway Standard

mkEnv =  generate
      ( pure []
          >>= pParamsStage proof0
          >>= universeStage proof0
      --    >>= vstateStage proof0
      --    >>= pstateStage proof0
      --    >>= dstateStage proof0
      --    >>= certsStage proof0
      --    >>= (\subst -> monadTyped $ substToEnv subst emptyEnv)
      )

subst0 = unsafePerformIO mkEnv

preds0 = map (substPred subst0)
       [ -- MetaSize (SzRng 8 8) utxoSize -- must be bigger than sum of (maxsize inputs) and (mazsize collateral)
         Sized (Range 8 8) (utxo proof0)
       , Member (Left feeTxOut) (Rng (utxo proof0))
       , MapMember feeTxIn feeTxOut (Right (utxo proof0))
       ]

-- outputCoinL :: Reflect era => Lens' (TxOutF era) Coin

{- We compute the fee, and fixup the transaction as follows
1) Compute the needed fee (say 241)
2) We know there is at least one input (feeTxIn) with enough money to pay the fee.
3) We have computed a balanced TxBody
   Produced(Outputs 2000231, Fees 0, Deposits 10) = 2000241
   Consumed(Inputs 2000234, Refunds 0, Withdrawals 7) = 2000241
4) We move the fee amount (241) from outputs to fee, So things still balance
   Produced(Outputs 1999990, Fees 241, Deposits 10) = 2000241
   Consumed(Inputs 2000234, Refunds 0, Withdrawals 7) = 2000241
   This means changing the bindings for 'outputs' and 'txfee'
5) We fix the collateral (which play no part in the balancing)
   to have enough money. This means changing the bindings for 'utxo'
   sum(collateral) >= fee * collpercent
-}

balanceMap :: Ord k => [(k,Coin)] -> Map k t -> Lens' t Coin -> Map k t
balanceMap pairs m0 l = foldl' accum m0 pairs
  where accum m (k,coin) = Map.adjust (\ t -> t & l .~ coin) k m

fixCollateral :: Reflect era => Proof era -> Coin -> Env era -> Gen (Env era)
fixCollateral p coin env = do
  col <- monadTyped (findVar (unVar collateral) env)
  u <- monadTyped (findVar (unVar (utxo p)) env)
  let n = Set.size col
  coins <- partitionCoin (Coin 1) [] n coin
  let utxo' = balanceMap (zip (Set.toList col) coins) u outputCoinL
  pure $ storeVar (unVar (utxo p)) utxo' env

-}
