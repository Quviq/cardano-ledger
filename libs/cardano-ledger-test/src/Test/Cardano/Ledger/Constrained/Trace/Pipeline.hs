module Test.Cardano.Ledger.Constrained.Trace.Pipeline where

import qualified Data.Map.Strict as Map
import Data.Pulse (foldlM')
import Data.Set (Set)
import qualified Data.Set as Set
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Env (Env, Name, emptyEnv)
import Test.Cardano.Ledger.Constrained.Monad (monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.Repl (goRepl)
import Test.Cardano.Ledger.Constrained.Rewrite (
  DependGraph (..),
  initialOrder,
  mkDependGraph,
  notBefore,
  rewriteGen,
 )
import Test.Cardano.Ledger.Constrained.Solver (solveOneVar)
import Test.Cardano.Ledger.Constrained.Stage (Pipeline, Stage (..), ledgerPipeline)
import Test.Cardano.Ledger.Constrained.Trace.TraceMonad
import Test.Cardano.Ledger.Constrained.Vars (dstateT)
import Test.Cardano.Ledger.Generic.Proof hiding (lift)
import Test.QuickCheck (generate)

-- ===============================================

{-
- Get 3 things
Gen a, a -> [a], a -> Bool
-}
-- ====================================

-- | Translate a Pipe into a DependGraph, given the set
--   of variables that have aready been solved for.
pipeToGraph :: Stage era -> Set (Name era) -> TraceM era (DependGraph era)
pipeToGraph (Stage info ps) alreadyDefined = do
  simple <- liftCounter rewriteGen ps
  orderedNames <- liftTyped $ initialOrder info simple
  liftTyped $ mkDependGraph (length orderedNames) [] alreadyDefined orderedNames [] (Prelude.filter notBefore simple)

-- | Merge a Pipeline into an existing DependGraph, given the set of variables
--   that have aready been solved for, to get a larger DependGraph
mergePipeline :: Pipeline era -> Set (Name era) -> DependGraph era -> TraceM era (DependGraph era)
mergePipeline [] _ graph = pure graph
mergePipeline (pipe : more) defined (DependGraph xs) = do
  DependGraph ys <- pipeToGraph pipe defined
  let names = concat (map fst ys)
  mergePipeline more (Set.union (Set.fromList names) defined) (DependGraph (xs ++ ys))

-- | Solve a Pipeline to get both an Env and a DependGraph
solvePipeline :: Reflect era => Pipeline era -> TraceM era (Env era, DependGraph era)
solvePipeline pipes = do
  gr@(DependGraph pairs) <- mergePipeline pipes Set.empty (DependGraph [])
  Subst subst <- liftGen (foldlM' solveOneVar emptySubst pairs)
  let isTempV k = not (elem '.' k)
  let sub = Subst (Map.filterWithKey (\k _ -> isTempV k) subst)
  env <- liftTyped (substToEnv sub emptyEnv)
  pure (env, gr)

main :: IO ()
main = do
  let proof = Babbage Standard
  ((env, DependGraph zs), _, _) <- generate (runTraceM 0 emptyEnv (solvePipeline (ledgerPipeline proof)))
  _dstate <- monadTyped $ runTarget env dstateT
  let vs = varsOfTarget Set.empty dstateT
  -- putStrLn (show(pcDState dstate))
  let ok (xs, _) = any (\x -> Set.member x vs) xs
  putStrLn (show (DependGraph (filter ok zs)))
  goRepl proof env ""
