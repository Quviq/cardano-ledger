{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Test.Cardano.Ledger.Constrained.LedgerTests where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List (find)
import Data.Maybe
import Data.Maybe.Strict
import Lens.Micro ((^.), (&), (.~), (%~))
import Control.State.Transition.Extended

import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Env

import Data.Default.Class (Default (def))
import Test.Cardano.Ledger.Generic.Updaters
import Cardano.Slotting.Slot
import Cardano.Protocol.TPraos.BHeader

-- import Cardano.Ledger.Coin
-- import Cardano.Ledger.Shelley
-- import Cardano.Ledger.Era (Era)
import Cardano.Ledger.Shelley.LedgerState (NewEpochState(..), EpochState(..))
import Test.Cardano.Ledger.Constrained.Classes
import Test.Cardano.Ledger.Constrained.Monad
import Test.Cardano.Ledger.Constrained.Size
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.Lenses
import Test.Cardano.Ledger.Constrained.Tests (checkPredicates)

import Test.Cardano.Ledger.Constrained.Shrink

import Test.Cardano.Ledger.Constrained.Examples hiding (newepochConstraints)
import Test.Cardano.Ledger.Constrained.Solver
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Proof (Reflect (..), AlonzoEra)
import Test.Cardano.Ledger.EraBuffet (TestCrypto)
import Test.Cardano.Ledger.Alonzo.AlonzoEraGen ()
import Test.Cardano.Ledger.Alonzo.EraMapping ()

-- import Test.Cardano.Ledger.Shelley.Utils (testGlobals)
-- import Cardano.Ledger.Shelley.API.Mempool (applyTxs, ApplyTxError(..))
import Cardano.Ledger.Alonzo.Scripts (Prices(..))
import Cardano.Ledger.Alonzo.Core
import Cardano.Ledger.Alonzo.PParams
import Cardano.Ledger.Alonzo.Rules
import Cardano.Ledger.Pretty
import Cardano.Ledger.Block
import Cardano.Ledger.Coin
import Cardano.Ledger.BaseTypes
import Cardano.Ledger.PoolDistr
import Cardano.Ledger.Keys
import Test.Cardano.Ledger.Shelley.Rules.Chain
import Test.Cardano.Ledger.Shelley.Generator.Block
import Test.Cardano.Ledger.Shelley.Generator.Core
import Test.Cardano.Ledger.Shelley.Generator.Presets
import Test.Cardano.Ledger.Shelley.Constants
import Test.Cardano.Ledger.Shelley.Utils

import Test.QuickCheck hiding (getSize, total)

genFromConstraints :: Era era => Proof era -> OrderInfo -> [Pred era] -> Target era t -> Gen t
genFromConstraints proof order cs target = do
  graph  <- monadTyped $ compile order $ rewrite cs
  result <- genDependGraph False proof graph
  case result of
    Left errs   -> error $ unlines errs
    Right subst -> do
      env <- monadTyped $ substToEnv subst emptyEnv
      monadTyped (runTarget env target)

shrinkFromConstraints :: Era era => Rep era t -> OrderInfo -> [Pred era] -> Target era t -> t -> [t]
shrinkFromConstraints rep order cs target val = do
  let env = saturateEnv (unTarget rep target val) cs
  graph <- monadTyped $ compile order $ rewrite cs
  env'  <- shrinkEnv graph env
  monadTyped $ runTarget env' target

unTarget :: Era era => Rep era t -> Target era t -> t -> Env era
unTarget rep target v =
    Env $ Map.fromList [ (x, Payload repX (v ^. lens) acc)
                       | Name (V x repX acc@(Yes rep' lens)) <- names
                       , Just Refl <- [testEql rep rep']
                       ]
  where names = Set.toList $ varsOfTarget mempty target

-- | Add variables to the environment that are uniquely determined by the constraints.
saturateEnv :: Era era => Env era -> [Pred era] -> Env era
saturateEnv env0 preds = go env0 preds
  where
    go env [] = env
    go env (p : ps)
      | Just (x, v) <- solveUnknown env p = saturateEnv (storeName x v env) preds
      | otherwise                         = go env ps

solveUnknown :: Era era => Env era -> Pred era -> Maybe (Name era, Payload era)
solveUnknown env p = case p of

  SumsTo _ (Var x@(V _ rep acc)) EQL sums
    | unknown (Name x)
    , all known $ foldl varsOfSum mempty sums
    , Right v <- runTyped (sumAdds <$> mapM (runSum env) sums) -> Just (Name x, Payload rep v acc)

  Component tm (AnyF (Field s rep acc@(Yes _ lens)) : _)
    | all known (varsOfTerm mempty tm)
    , unknown x
    , Right r <- runTyped (runTerm env tm) ->
        Just (x, Payload rep (r ^. lens) acc)
    where
      x = Name (V s rep acc)

  Component r (_ : flds) ->
    solveUnknown env (Component r flds)

  _ -> Nothing

  where
    known   = isJust . flip findName env
    unknown = not . known

-- NewEpochState generator ------------------------------------------------

randoms :: Proof era -> [Pred era]
randoms p =
  [ Random poolDistr
  , Random regPools
  , Random retiring
  , Random futureRegPools
  , Random poolDeposits
  , Random prevBlocksMade
  , Random currBlocksMade
  , Random markPools
  , Random markPoolDistr
  , Random setPools
  , Random goPools
  , Random stakeDeposits
  , Random delegations
  , Random rewards
  , Random markStake
  , Random markDelegs
  , Random setStake
  , Random setDelegs
  , Random goStake
  , Random goDelegs
  , Random instanReserves
  , Random instanTreasury
  , Random (proposalsT p)
  , Random (futureProposalsT p)
  , Random genDelegs
  , Random (utxo p)
  ]

newepochConstraints :: Reflect era => Proof era -> [Pred era]
newepochConstraints pr =
  randoms pr
  ++ pstatePreds pr
  ++ dstatePreds pr
  ++ utxostatePreds pr
  ++ accountstatePreds pr
  ++ epochstatePreds pr
  ++ newepochstatePreds pr

genNewEpochState :: forall era. (AlonzoEraPParams era, ExactEra AlonzoEra era, Reflect era)
                 => Proof era
                 -> EpochStateUniv era
                 -> Gen (NewEpochState era)
genNewEpochState proof env = do
  nes <- genFromConstraints
            proof
            standardOrderInfo {sumBeforeParts = False}
            (univPreds proof env ++ sizePreds proof ++ newepochConstraints proof)
            (newEpochStateT proof)
  -- Fix up issues with PParams generator
  let pp = applyPPUpdates
                (updatePParams proof (esPp $ nesEs nes) (defaultCostModels proof)
                  & ppPricesL .~ Prices minBound minBound
                  & ppMinFeeAL .~ Coin 44
                  & ppMinFeeBL .~ Coin 155381
                  & ppCoinsPerUTxOWordL .~ CoinPerWord (Coin 34482)
                  & ppMaxValSizeL .~ 5000
                  & ppMaxCollateralInputsL .~ 3
                  & ppProtocolVersionL %~ \ ver -> ver{ pvMajor = natVersion @5 } -- TODO
                ) ppu
      ppu = case proof of
              Alonzo _ -> PParamsUpdate $ (emptyPParamsStrictMaybe @era) { appD = SJust minBound }
              _        -> PParamsUpdate (emptyPParamsStrictMaybe @era)

      fixPoolStakeVrfs (PoolDistr pd) = PoolDistr $ Map.mapWithKey fixPoolStakeVrf pd
      fixPoolStakeVrf kh stake = stake{ individualPoolStakeVrf = hashVerKeyVRF vrfk }
        where
          vrfk = case find ((== kh) . aikColdKeyHash) (ksStakePools $ keysUniv env) of
                   Just issuerKeys -> vrfVerKey $ aikVrf issuerKeys
                   Nothing -> error $ "Bad stake pool hash " ++ show kh


  pure $ nes & nesEsL . esPpL .~ pp
             & nesPdL %~ fixPoolStakeVrfs

shrinkNewEpochState :: Reflect era => Proof era -> NewEpochState era -> [NewEpochState era]
shrinkNewEpochState proof st =
  shrinkFromConstraints
    NewEpochStateR
    standardOrderInfo
    (sizePreds proof ++ newepochConstraints proof)
    (newEpochStateT proof)
    st

-- Property ---------------------------------------------------------------

type TestEra = AlonzoEra TestCrypto

-- This exists in Test.Cardano.Ledger.Alonzo.ChainTrace, but that's in a test package that we can't
-- depend on here.
instance Embed (AlonzoBBODY TestEra) (CHAIN TestEra) where
  wrapFailed = BbodyFailure
  wrapEvent = BbodyEvent

testProof :: Proof TestEra
testProof = Alonzo Mock

prop_newEpochState :: EpochStateUniv TestEra -> Property
prop_newEpochState env =
  forAllShrinkBlind (genNewEpochState testProof env) (shrinkNewEpochState testProof) $ \ st ->
  validEpochState st .&&. conjoin (map validEpochState $ shrinkNewEpochState testProof st)

validEpochState :: NewEpochState TestEra -> Property
validEpochState st = checkPredicates preds (saturateEnv env preds)
  where
    env   = unTarget NewEpochStateR (newEpochStateT testProof) st
    preds = newepochConstraints testProof

-- testTxValidForLEDGER
-- Test.Cardano.Ledger.Shelley.Generator.genBlock

testGenerateTx :: IO ()
testGenerateTx = do -- quickCheck prop_generateTx
  env0 <- generate arbitrary
  let genv = genEnv undefined defaultConstants
      keyspace = geKeySpace genv
      env = env0 { keysUniv = keyspace }
  nes <- generate $ genNewEpochState testProof env
  putStrLn "--- UTxO set ---"
  print $ prettyA $ nes ^. nesEsL . esLStateL . lsUTxOStateL . utxosUtxoL
  putStrLn "--- PParams ---"
  print $ nes ^. nesEsL . esPpL
  let slot :: SlotNo
      slot = 3551
      hh = HashHeader def
      st :: ChainState TestEra
      st = ChainState { chainNes              = nes
                      , chainOCertIssue       = mempty
                      , chainEpochNonce       = NeutralNonce
                      , chainEvolvingNonce    = NeutralNonce
                      , chainCandidateNonce   = NeutralNonce
                      , chainPrevEpochNonce   = NeutralNonce
                      , chainLastAppliedBlock = At $ LastAppliedBlock 100 slot hh
                      }
  print hh
  -- trace "next test case ---------->" $
  block@(Block bh@(BHeader bhb _) _) <- generate $ genBlock genv st
  putStrLn "--- Block ---"
  print bh
  let slotNo = bheaderSlotNo bhb
      st' = tickChainState slotNo st
  case runShelleyBase $ applySTS @(CHAIN TestEra) $ TRC ((), st', block) of
    Left err -> putStrLn $ "--- Error ---\n" ++ show err
    Right _st' -> putStrLn "Success!"

prop_generateTx :: EpochStateUniv TestEra -> Property
prop_generateTx env0 =
  forAllBlind (genNewEpochState testProof env) $ \ nes ->
    -- counterexample "--- NewEpochState ---" $
    -- counterexample (show $ prettyA $ nes ^. nesEsL . esLStateL . lsUTxOStateL . utxosUtxoL) $
    counterexample "--- PParams ---" $
    counterexample (show $ nes ^. nesEsL . esPpL) $
    counterexample "--- Stake pools ---" $
    counterexample (show $ nes ^. nesPdL) $
    let slot :: SlotNo
        slot = 3551
        hh = HashHeader def
        st :: ChainState TestEra
        st = ChainState { chainNes              = nes
                        , chainOCertIssue       = mempty
                        , chainEpochNonce       = NeutralNonce -- mkNonceFromNumber 2
                        , chainEvolvingNonce    = NeutralNonce -- mkNonceFromNumber 3
                        , chainCandidateNonce   = NeutralNonce -- mkNonceFromNumber 4
                        , chainPrevEpochNonce   = NeutralNonce -- mkNonceFromNumber 5
                        , chainLastAppliedBlock = At $ LastAppliedBlock 100 slot hh
                        }
    in
    forAllBlind (genBlock genv st) $ \ block@(Block bh@(BHeader bhb _) _) ->
    counterexample "--- Block ---" $
    counterexample (show bh) $
    let slotNo = bheaderSlotNo bhb
        st' = tickChainState slotNo st
    in case runShelleyBase $ applySTS @(CHAIN TestEra) $ TRC ((), st', block) of
      Left err -> counterexample ("--- Error ---\n" ++ show err) False
      Right st'' -> validEpochState (chainNes st'')
  where
    genv = genEnv undefined defaultConstants
    keyspace = geKeySpace genv
    env = env0 { keysUniv = keyspace }

