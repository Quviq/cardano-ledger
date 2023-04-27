{-# LANGUAGE GADTs #-}
module Test.Cardano.Ledger.Constrained.LedgerTests where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Lens.Micro ((^.))

import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Env

-- import Cardano.Ledger.Coin
-- import Cardano.Ledger.Shelley
import Cardano.Ledger.Era (Era)
import Cardano.Ledger.Shelley.LedgerState
import Test.Cardano.Ledger.Constrained.Classes
import Test.Cardano.Ledger.Constrained.Monad
import Test.Cardano.Ledger.Constrained.Size
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.Tests (checkPredicates)

-- import Test.Cardano.Ledger.Constrained.Shrink

import Test.Cardano.Ledger.Constrained.Examples (univPreds, pstatePreds, dstatePreds, utxostatePreds, accountstatePreds,
                                                 epochstatePreds, newepochstatePreds, runTarget)
import Test.Cardano.Ledger.Constrained.Solver
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Proof (Reflect (..), ConwayEra, Standard)
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

newepochConstraints :: Reflect era => Proof era -> [Pred era]
newepochConstraints pr =
  pstatePreds pr
  ++ dstatePreds pr
  ++ utxostatePreds pr
  ++ accountstatePreds pr
  ++ epochstatePreds pr
  ++ newepochstatePreds pr

genNewEpochState :: Reflect era => Proof era -> Gen (NewEpochState era)
genNewEpochState proof =
  genFromConstraints
    proof
    standardOrderInfo {sumBeforeParts = False}
    (univPreds proof ++ newepochConstraints proof)
    (newEpochStateT proof)

unTarget :: Era era => Rep era t -> Target era t -> t -> Env era
unTarget rep target v =
    Env $ Map.fromList [ (x, Payload repX (v ^. lens) acc)
                       | Name (V x repX acc@(Yes rep' lens)) <- names
                       , Just Refl <- [testEql rep rep']
                       ]
  where names = Set.toList $ varsOfTarget mempty target

type TestEra = ConwayEra Standard

testProof :: Proof TestEra
testProof = Conway Standard

prop_newEpochState :: Property
prop_newEpochState = forAll (genNewEpochState testProof) $ \ st ->
  let env   = unTarget NewEpochStateR (newEpochStateT testProof) st
      preds = newepochConstraints testProof in
  checkPredicates preds (saturateEnv env preds)

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

