module Test.Cardano.Ledger.Constrained.LedgerTests where

import Test.Cardano.Ledger.Constrained.Ast

-- import Cardano.Ledger.Coin
-- import Cardano.Ledger.Era (Era)
-- import Cardano.Ledger.Shelley
import Cardano.Ledger.Shelley.LedgerState
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Monad
import Test.Cardano.Ledger.Constrained.Rewrite

-- import Test.Cardano.Ledger.Constrained.Shrink

import Test.Cardano.Ledger.Constrained.Examples
import Test.Cardano.Ledger.Constrained.Solver
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Proof (Reflect (..))
import Test.QuickCheck hiding (getSize, total)

genFromConstraints :: Proof era -> OrderInfo -> [Pred era] -> Target era t -> Gen t
genFromConstraints proof order cs target = do
  graph <- monadTyped $ compile order $ rewrite cs
  result <- genDependGraph False proof graph
  case result of
    Left errs -> error $ unlines errs
    Right subst -> do
      env <- monadTyped $ substToEnv subst emptyEnv
      monadTyped (runTarget env target)

genNewEpochState :: Reflect era => Proof era -> Gen (NewEpochState era)
genNewEpochState proof =
  genFromConstraints
    proof
    standardOrderInfo {sumBeforeParts = False}
    (newepochConstraints proof)
    (newEpochStateT proof)
