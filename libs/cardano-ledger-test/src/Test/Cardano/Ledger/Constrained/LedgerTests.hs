{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
module Test.Cardano.Ledger.Constrained.LedgerTests where

import Control.Monad
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Data.Maybe.Strict
import Lens.Micro ((^.), (&), (.~), (%~))

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
import Test.Cardano.Ledger.Generic.Proof (Reflect (..), AlonzoEra, Standard)
import Test.Cardano.Ledger.Alonzo.AlonzoEraGen ()

-- import Test.Cardano.Ledger.Shelley.Utils (testGlobals)
-- import Cardano.Ledger.Shelley.API.Mempool (applyTxs, ApplyTxError(..))
import Cardano.Ledger.Alonzo.Scripts (Prices(..))
import Cardano.Ledger.Alonzo.Core
import Cardano.Ledger.Alonzo.PParams
import Cardano.Ledger.Pretty
import Cardano.Ledger.Coin
import Cardano.Ledger.BaseTypes
import Test.Cardano.Ledger.Shelley.Rules.Chain
import Test.Cardano.Ledger.Shelley.Generator.Block
import Test.Cardano.Ledger.Shelley.Generator.Core
import Test.Cardano.Ledger.Shelley.Generator.Presets
import Test.Cardano.Ledger.Shelley.Constants

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
            (univPreds proof env ++ newepochConstraints proof)
            (newEpochStateT proof)
  -- Fix up issues with PParams generator
  feeA   <- choose (1, 100)
  minAda <- choose (1, 10)
  let pp = applyPPUpdates
                (updatePParams proof (esPp $ nesEs nes) (defaultCostModels proof)
                  & ppPricesL .~ Prices minBound minBound
                  & ppMinFeeAL .~ Coin feeA
                  & ppCoinsPerUTxOWordL .~ CoinPerWord (Coin minAda)
                  & ppMaxValSizeL .~ 4000
                  & ppProtocolVersionL %~ \ ver -> ver{ pvMajor = natVersion @5 } -- TODO
                ) ppu
      ppu = case proof of
              Alonzo _ -> PParamsUpdate $ (emptyPParamsStrictMaybe @era) { appD = SJust minBound }
              _        -> PParamsUpdate (emptyPParamsStrictMaybe @era)

  pure $ nes & nesEsL . esPpL .~ pp

shrinkNewEpochState :: Reflect era => Proof era -> NewEpochState era -> [NewEpochState era]
shrinkNewEpochState proof st =
  shrinkFromConstraints
    NewEpochStateR
    standardOrderInfo
    (newepochConstraints proof)
    (newEpochStateT proof)
    st

-- Property ---------------------------------------------------------------

type TestEra = AlonzoEra Standard

testProof :: Proof TestEra
testProof = Alonzo Standard

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
  block <- generate $ genBlock genv st
  -- counterexample (show $ prettyA block) $
  when (length (show $ prettyA block) >= 0) $ putStrLn "Success!"

prop_generateTx :: EpochStateUniv TestEra -> Property
prop_generateTx env0 =
  forAllBlind (genNewEpochState testProof env) $ \ nes ->
    -- counterexample "--- NewEpochState ---" $
    -- counterexample (show $ prettyA $ nes ^. nesEsL . esLStateL . lsUTxOStateL . utxosUtxoL) $
    -- counterexample "--- PParams ---" $
    -- counterexample (show pp) $
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
    in
    -- trace "next test case ---------->" $
    forAllBlind (genBlock genv st) $ \ block ->
    -- counterexample (show $ prettyA block) $
    length (show $ prettyA block) >= 0
  where
    genv = genEnv undefined defaultConstants
    keyspace = geKeySpace genv
    env = env0 { keysUniv = keyspace }

