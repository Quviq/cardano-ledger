{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Cardano.Ledger.Constrained.Preds.DPState where

import Cardano.Ledger.Coin (Coin (..), DeltaCoin (..))
import Cardano.Ledger.Pretty (ppMap)
import GHC.Real ((%))
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Lenses (fGenDelegGenKeyHashL)
import Test.Cardano.Ledger.Constrained.Monad (monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.Universes
import Test.Cardano.Ledger.Constrained.Rewrite (standardOrderInfo)
import Test.Cardano.Ledger.Constrained.Size (OrdCond (..))
import Test.Cardano.Ledger.Constrained.Solver
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.PrettyCore (
  PrettyC (..),
  pcDState,
  pcIndividualPoolStake,
  pcKeyHash,
  pcPState,
  pcVState,
 )
import Test.Cardano.Ledger.Generic.Proof
import Test.QuickCheck

-- ======================================

vstatePreds :: Proof era -> [Pred era]
vstatePreds _p =
  [ Sized (Range 3 8) dreps
  , Sized (Range 5 7) (Dom ccHotKeys)
  , Subset dreps voteUniv
  , Subset (Dom ccHotKeys) voteHashUniv
  ]

vstateStage ::
  Reflect era =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
vstateStage proof = toolChainSub proof standardOrderInfo (vstatePreds proof)

mainV :: IO ()
mainV = do
  let proof = Babbage Standard
  env <-
    generate
      ( pure []
          >>= universeStage proof
          >>= vstateStage proof
          >>= (\subst -> monadTyped $ substToEnv subst emptyEnv)
      )
  vstate <- monadTyped $ runTarget env vstateT
  putStrLn (show (pcVState vstate))
  putStrLn "\n"
  putStrLn (unlines (otherFromEnv [] env))

-- ==========================================

pstateNames :: [String]
pstateNames =
  [ "regPools"
  , "futureRegPools"
  , "retiring"
  , "poolDeposits"
  ]

pstatePreds :: Reflect era => Proof era -> [Pred era]
pstatePreds _p =
  [ Random epochNo -- Should this be defined in Universes?
  -- These Sized constraints are needd to be ensure that regPools is bigger than retiring
  , Sized (ExactSize 3) retiring
  , Sized (AtLeast 3) regPools
  , Subset (Dom regPools) poolHashUniv
  , Subset (Dom futureRegPools) poolHashUniv
  , Subset (Dom poolDeposits) poolHashUniv
  , Subset (Dom retiring) (Dom regPools) -- Note regPools must be bigger than retiring
  , Dom regPools :=: Dom poolDeposits
  , NotMember (Lit CoinR (Coin 0)) (Rng poolDeposits)
  , Disjoint (Dom regPools) (Dom futureRegPools)
  , epochs :=: Elems retiring
  , Choose
      (ExactSize 3)
      epochs
      [ (Constr "id" id ^$ e, [CanFollow e epochNo])
      , (Constr "(+1)" (+ 1) ^$ e, [CanFollow e epochNo])
      , (Constr "(+3)" (+ 3) ^$ e, [CanFollow e epochNo])
      , (Constr "(+5)" (+ 5) ^$ e, [CanFollow e epochNo])
      ]
  , -- poolDistr not needed in PState, but is needed in NewEpochState
    -- But since it is so intimately tied to regPools we define it here
    -- Alternately we could put this in NewEpochState, and insist that pStateStage
    -- preceed newEpochStateStage
    Dom regPools :=: Dom poolDistr
  , SumsTo (Right (1 % 1000)) (Lit RationalR 1) EQL [Project RationalR poolDistr]
  ]
  where
    e = var "e" EpochR
    epochs = var "epochs" (ListR EpochR)

pstateStage ::
  Reflect era =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
pstateStage proof = toolChainSub proof standardOrderInfo (pstatePreds proof)

mainP :: IO ()
mainP = do
  let proof = Babbage Standard
  env <-
    generate
      ( pure []
          >>= universeStage proof
          >>= pstateStage proof
          >>= (\subst -> monadTyped $ substToEnv subst emptyEnv)
      )
  pstate <- monadTyped $ runTarget env pstateT
  pDistr <- monadTyped (findVar (unVar poolDistr) env)
  putStrLn (show (pcPState pstate))
  putStrLn "\n"
  putStrLn (show (ppMap pcKeyHash pcIndividualPoolStake pDistr))
  putStrLn "\n"
  putStrLn (unlines (otherFromEnv [] env))

-- ============================================================================

dstatePreds :: Proof era -> [Pred era]
dstatePreds _p =
  [ Sized (Range 1 8) rewards -- Small enough that it leaves some slack with credUniv (size about 30),
  -- but it also cannot be empty
  , Sized (AtLeast 1) treasury --  If these have size zero, the SumsTo can't be solved
  , Sized (AtLeast 1) instanReserves
  , Random instanTreasury
  , Dom rewards :⊆: credsUniv
  , Member (Lit CoinR (Coin 0)) (Rng rewards) -- At least 1 cred has zero rewards
  , NotMember (Lit CoinR (Coin 0)) (Rng stakeDeposits)
  , Dom rewards :=: Dom stakeDeposits
  , Dom delegations :⊆: Dom rewards
  , Dom rewards :=: Rng ptrs
  , Dom genDelegs :⊆: Dom genesisHashUniv
  , Negate (deltaReserves) :=: deltaTreasury
  , SumsTo (Right (Coin 1)) instanReservesSum EQL [SumMap instanReserves]
  , SumsTo (Right (DeltaCoin 1)) (Delta instanReservesSum) LTH [One (Delta reserves), One deltaReserves]
  , SumsTo (Right (Coin 1)) instanTreasurySum EQL [SumMap instanTreasury]
  , SumsTo (Right (DeltaCoin 1)) (Delta instanTreasurySum) LTH [One (Delta treasury), One deltaTreasury]
  , ProjS fGenDelegGenKeyHashL GenHashR (Dom futureGenDelegs) :=: Dom genDelegs
  ]
  where
    instanReservesSum = Var (V "instanReservesSum" CoinR No)
    instanTreasurySum = Var (V "instanTreasurySum" CoinR No)

dstateStage ::
  Reflect era =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
dstateStage proof = toolChainSub proof standardOrderInfo (dstatePreds proof)

mainD :: IO ()
mainD = do
  let proof = Babbage Standard
  env <-
    generate
      ( pure []
          >>= universeStage proof
          >>= dstateStage proof
          >>= (\subst -> monadTyped $ substToEnv subst emptyEnv)
      )
  dState <- monadTyped $ runTarget env dstateT
  putStrLn (show (pcDState dState))
  putStrLn "\n"
  putStrLn (unlines (otherFromEnv [] env))

-- ===============================================

mainC :: IO ()
mainC = do
  let proof = Babbage Standard
  env <-
    generate
      ( pure []
          >>= universeStage proof
          >>= vstateStage proof
          >>= pstateStage proof
          >>= dstateStage proof
          >>= (\subst -> monadTyped $ substToEnv subst emptyEnv)
      )
  certState <- monadTyped $ runTarget env dpstateT
  putStrLn (show (prettyC proof certState))
  putStrLn "\n"
  putStrLn (unlines (otherFromEnv [] env))
