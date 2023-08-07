{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Constrained.Trace.Tests
where

-- import Debug.Trace
import Cardano.Ledger.Alonzo.Scripts.Data (BinaryData, Datum (..))
import Cardano.Ledger.Babbage.TxOut (BabbageTxOut (..))
import Cardano.Ledger.BaseTypes (TxIx)
import Cardano.Ledger.Core (EraRule, EraTx (..), EraTxBody (..), Tx)
import Cardano.Ledger.Shelley.LedgerState (LedgerState (..))
import Cardano.Ledger.Shelley.Rules (LedgerEnv (..))
import Cardano.Ledger.TreeDiff (
  Expr (App),
  ToExpr (toExpr),
 )
import Control.State.Transition.Extended (STS (..), TRC (..))
import Data.Foldable (toList)
import Lens.Micro ((^.))
import System.IO (hSetEncoding, stdout, utf8)
import Test.Cardano.Ledger.Constrained.Ast (emptySubst, runTarget, runTerm, substToEnv)
import Test.Cardano.Ledger.Constrained.Classes (PParamsF (..), TxF (..), TxOutF (..))
import Test.Cardano.Ledger.Constrained.Env (Env (..), emptyEnv)
import Test.Cardano.Ledger.Constrained.Monad (Typed)
import Test.Cardano.Ledger.Constrained.Preds.Repl (goRepl)
import Test.Cardano.Ledger.Constrained.Trace.Actions (feesAction, inputsAction, outputsAction)
import Test.Cardano.Ledger.Constrained.Trace.SimpleTx (simpleTx)
import Test.Cardano.Ledger.Constrained.Trace.TraceMonad (
  TraceM,
  certStateTrace,
  fstTriple,
  getEnv,
  getTarget,
  ledgerStateTrace,
  liftGen,
  liftTyped,
  pparamsTrace,
  pstateTrace,
  putEnv,
  runTraceM,
  setVar,
  toGen,
  universeTrace,
  vstateTrace,
 )
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.PrettyCore (pcTx)
import Test.Cardano.Ledger.Generic.Proof hiding (lift)
import Test.Cardano.Ledger.Generic.TxGen (applySTSByProof)
import Test.QuickCheck (Arbitrary (..), Property, conjoin, counterexample, generate, whenFail, withMaxSuccess, (===))
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty)

-- import qualified Data.Map.Strict as Map

-- =================================

instance ToExpr (BabbageTxOut (BabbageEra StandardCrypto)) where
  toExpr (BabbageTxOut addr val dat sc) = App "BabbageTxOut" [toExpr addr, toExpr val, toExpr dat, toExpr sc]

instance ToExpr (Datum (BabbageEra StandardCrypto)) where
  toExpr NoDatum = App "NoDatum" []
  toExpr (DatumHash x) = App "DatumHash" [toExpr x]
  toExpr (Datum bd) = App "Datum" [toExpr bd]

instance ToExpr (BinaryData (BabbageEra StandardCrypto)) where
  toExpr _ = App "BinaryData" []

-- ===================================================

-- | Generate an Env that contains the pieces of the LedgerState
--   by chaining smaller pieces together.
genLedgerStateEnv :: Reflect era => Proof era -> TraceM era (Env era)
genLedgerStateEnv proof = do
  subst <-
    pure emptySubst
      >>= pparamsTrace proof
      >>= universeTrace proof
      >>= vstateTrace proof
      >>= pstateTrace proof
      >>= certStateTrace proof
      >>= ledgerStateTrace proof
  env <- liftTyped (substToEnv subst emptyEnv)
  putEnv env

go :: IO ()
go = do
  x <- generate (fstTriple <$> runTraceM 0 emptyEnv (genLedgerStateEnv (Babbage Standard)))
  goRepl (Babbage Standard) x ""

-- | Given an (Env era) construct the pair the the LendgerEnv and the LedgerState
getSTSLedgerEnv :: Reflect era => Proof era -> TxIx -> Env era -> Typed (LedgerEnv era, LedgerState era)
getSTSLedgerEnv proof txIx env = do
  ledgerstate <- runTarget env (ledgerStateT proof)
  slot <- runTerm env currentSlot
  (PParamsF _ pp) <- runTerm env (pparams proof)
  accntState <- runTarget env accountStateT
  pure $ (LedgerEnv slot txIx pp accntState, ledgerstate)

-- =======================================================================
-- Test that simpleTx and the 'actions' actually agree with the applySTS

-- | Construct and run one simpleTx, and run it through applySTS
--  Check that the computed LedgerState is the same as the expected LedgerState
--  Computed by using 'inputsAction' , 'outputsAction' , and 'feesAction'
genAndRunSimpleTx :: TraceM (ConwayEra StandardCrypto) Property
genAndRunSimpleTx = do
  let proof = Conway Standard
  _ <- genLedgerStateEnv proof

  -- Compute the TRC before we make the Tx, because that adds things to the Env
  txIx <- liftGen arbitrary
  env0 <- getEnv
  (lenv, ledgerstate) <- liftTyped $ getSTSLedgerEnv proof txIx env0

  -- Now generate a simpleTx, and store it in the Env
  -- apply the changes we expect this Tx to make, and save the result.
  tx <- simpleTx proof
  setVar txterm (TxF proof tx)
  let txb = tx ^. bodyTxL
      feeCoin = txb ^. feeTxBodyL
  inputsAction proof (txb ^. inputsTxBodyL)
  outputsAction proof txb (fmap (TxOutF proof) (toList (txb ^. outputsTxBodyL)))
  feesAction feeCoin
  expectedLedgerState <- getTarget (ledgerStateT proof)
  env1 <- getEnv

  -- Now compute the env we compute using the STS
  case applySTSByProof proof (TRC (lenv, ledgerstate, tx)) of
    Right ledgerState' ->
      pure (ledgerState' === {- `ediffEq` -} expectedLedgerState)
    Left errs ->
      pure
        ( counterexample
            ("\napplySTS fails\n" ++ unlines (map show errs) ++ "\nTx =\n" ++ (show (pcTx proof tx)))
            ( whenFail
                (putStrLn ("\napplySTS fails\n" ++ unlines (map show errs)) >> (goRepl proof env1 ""))
                (True === False)
            )
        )

main1 :: IO ()
main1 = do
  hSetEncoding stdout utf8
  defaultMain $ testProperty "TraceMain" (withMaxSuccess 50 (toGen genAndRunSimpleTx))

-- ==============================================================
-- Code to make Traces

-- | Iterate a function 'make' to make a trace of length 'n'. Each call to 'make' gets the
--   most recent value of the Env internal to TraceM. The function 'make' is
--   supposed to compute 'a', and (possibly) update the Env internal to TraceM.
makeTrace :: Int -> TraceM era a -> TraceM era [(Env era, a)]
makeTrace 0 _ = pure []
makeTrace n make = do
  env0 <- getEnv
  a <- make
  xs <- makeTrace (n - 1) make
  pure ((env0, a) : xs)

data Trip era a = Trip !(Env era) !(Env era) !a

beforeAfterTrace :: Int -> (Int -> TraceM era a) -> TraceM era [Trip era a]
beforeAfterTrace 0 _ = pure []
beforeAfterTrace !n make = do
  !beforeEnv <- getEnv
  !a <- make n
  !afterEnv <- getEnv
  xs <- beforeAfterTrace (n - 1) make
  let !ans = Trip beforeEnv afterEnv a : xs
  pure ans

-- =================================================================
-- Show that each step in a trace computes the right LedgerState

runOne ::
  ( Environment (EraRule "LEDGER" era) ~ LedgerEnv era
  , State (EraRule "LEDGER" era) ~ LedgerState era
  , Signal (EraRule "LEDGER" era) ~ Tx era
  , Show (PredicateFailure (EraRule "LEDGER" era))
  , Reflect era
  ) =>
  Proof era ->
  TxIx ->
  Trip era (Signal (EraRule "LEDGER" era)) ->
  Typed Property
runOne proof txIx (Trip beforeEnv afterEnv tx) = do
  (lenv, ledgerstate) <- getSTSLedgerEnv proof txIx beforeEnv
  expectedLedgerState <- runTarget afterEnv (ledgerStateT proof)
  case applySTSByProof proof (TRC (lenv, ledgerstate, tx)) of
    Right ledgerState' -> pure (ledgerState' === expectedLedgerState)
    Left errs ->
      pure
        ( counterexample
            ("\napplySTS fails\n" ++ unlines (map show errs) ++ "\nTx =\n" ++ (show (pcTx proof tx)))
            ( whenFail
                (putStrLn ("\napplySTS fails\n" ++ unlines (map show errs)) >> (goRepl proof afterEnv ""))
                (True === False)
            )
        )

oneTx :: Reflect era => Proof era -> Int -> TraceM era (Tx era)
oneTx proof _n = do
  !tx <- simpleTx proof
  setVar txterm (TxF proof tx)
  let !txb = tx ^. bodyTxL
      !feeCoin = txb ^. feeTxBodyL
  inputsAction proof (txb ^. inputsTxBodyL)
  outputsAction proof txb (fmap (TxOutF proof) (toList (txb ^. outputsTxBodyL)))
  feesAction feeCoin
  pure tx

testTrace ::
  ( Environment (EraRule "LEDGER" era) ~ LedgerEnv era
  , State (EraRule "LEDGER" era) ~ LedgerState era
  , Signal (EraRule "LEDGER" era) ~ Tx era
  , Reflect era
  , Show (PredicateFailure (EraRule "LEDGER" era))
  ) =>
  Proof era ->
  Int ->
  TraceM era Property
testTrace proof tracelen = do
  !_ <- genLedgerStateEnv proof
  !txIx <- liftGen arbitrary
  !pairs <- beforeAfterTrace tracelen (oneTx proof)
  conjoin <$> mapM (\ !x -> liftTyped (runOne proof txIx x)) pairs

main :: IO ()
main = do
  hSetEncoding stdout utf8
  let tracelen = 100
      n = 4
  defaultMain $
    testProperty
      ("Testing Trace: length=" ++ show tracelen ++ ", Success=" ++ show n)
      (withMaxSuccess n (fstTriple <$> (runTraceM 0 emptyEnv (testTrace (Conway Standard) tracelen))))
