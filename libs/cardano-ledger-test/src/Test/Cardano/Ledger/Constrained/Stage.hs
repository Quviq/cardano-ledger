{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Test.Cardano.Ledger.Constrained.Stage where

import Cardano.Ledger.Pretty (ppMap, ppMaybe)
import Cardano.Ledger.Shelley.LedgerState (NewEpochState (..), certDStateL, esLStateL, lsCertStateL, nesEsL)
import qualified Data.Map.Strict as Map
import Data.Pulse (foldlM')
import Data.Set (Set)
import qualified Data.Set as Set
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Env (Access (..), Env, Name, P (..), V (..), bulkStore, emptyEnv)
import Test.Cardano.Ledger.Constrained.Monad (monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.CertState (certStatePreds, pstatePreds, vstatePreds)
import Test.Cardano.Ledger.Constrained.Preds.LedgerState (ledgerStatePreds)
import Test.Cardano.Ledger.Constrained.Preds.PParams (pParamsPreds)
import Test.Cardano.Ledger.Constrained.Preds.Universes (universePreds)
import Test.Cardano.Ledger.Constrained.Rewrite (
  DependGraph (..),
  OrderInfo,
  initialOrder,
  mkDependGraph,
  notBefore,
  rewriteGen,
  standardOrderInfo,
 )
import Test.Cardano.Ledger.Constrained.Solver (solveOneVar)
import Test.Cardano.Ledger.Constrained.TypeRep (Rep (..), testEql, (:~:) (Refl))
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.ModelState (newEpochStateZero)
import Test.Cardano.Ledger.Generic.PrettyCore (pcCoin, pcCredential, pcDState)
import Test.Cardano.Ledger.Generic.Proof hiding (lift)

import Cardano.Ledger.CertState (DState (..))
import Cardano.Ledger.Shelley.LedgerState (dsFutureGenDelegsL, dsGenDelegsL, dsUnifiedL)
import Lens.Micro
import Test.Cardano.Ledger.Constrained.Lenses
import Test.QuickCheck (Gen, generate)

-- ===============================================

{-
- Get 3 things
Gen a, a -> [a], a -> Bool
-}
-- ====================================

-- | Group together some Preds and OrderInfo about how to decide the
--   order in which to solve the variables appearing in the Preds
data Stage era = Stage OrderInfo [Pred era]

type Pipeline era = [Stage era]

-- | A pipeline for specifying the LederState
ledgerPipeline :: Reflect era => Proof era -> Pipeline era
ledgerPipeline proof =
  [ Stage standardOrderInfo (pParamsPreds proof)
  , Stage standardOrderInfo (universePreds proof)
  , Stage standardOrderInfo (vstatePreds proof)
  , Stage standardOrderInfo (pstatePreds proof)
  , Stage standardOrderInfo (certStatePreds proof)
  , Stage standardOrderInfo (ledgerStatePreds proof)
  ]

-- | Translate a Stage into a DependGraph, given the set
--   of variables that have aready been solved for.
stageToGraph :: Int -> Stage era -> Set (Name era) -> Gen (Int, DependGraph era)
stageToGraph n0 (Stage info ps) alreadyDefined = do
  (n1, simple) <- rewriteGen (n0, ps)
  orderedNames <- monadTyped $ initialOrder info simple
  graph <- monadTyped $ mkDependGraph (length orderedNames) [] alreadyDefined orderedNames [] (Prelude.filter notBefore simple)
  pure (n1, graph)

-- | Merge a Pipeline into an existing DependGraph, given the set of variables
--   that have aready been solved for, to get a larger DependGraph
mergePipeline :: Int -> Pipeline era -> Set (Name era) -> DependGraph era -> Gen (Int, DependGraph era)
mergePipeline n [] _ graph = pure (n, graph)
mergePipeline n0 (pipe : more) defined (DependGraph xs) = do
  (n1, DependGraph ys) <- stageToGraph n0 pipe defined
  let names = concat (map fst ys)
  mergePipeline n1 more (Set.union (Set.fromList names) defined) (DependGraph (xs ++ ys))

-- | Solve a Pipeline to get both an Env and a DependGraph
solvePipeline :: Reflect era => Pipeline era -> Gen (Env era, DependGraph era)
solvePipeline pipes = do
  (_, gr@(DependGraph pairs)) <- mergePipeline 0 pipes Set.empty (DependGraph [])
  Subst subst <- foldlM' solveOneVar emptySubst pairs
  let isTempV k = not (elem '.' k)
  let sub = Subst (Map.filterWithKey (\k _ -> isTempV k) subst)
  env <- monadTyped (substToEnv sub emptyEnv)
  pure (env, gr)

-- ======================================================================
-- Experiment number 1, change the Access in the Vars in a Target
-- ======================================================================

-- | Show all the details of a Var term, including its Access Lens', if present
fullVar :: Term era t -> String
fullVar (Var (V nm t No)) = nm ++ " :: " ++ show t ++ " No Lens"
fullVar (Var (V nm t (Yes x _))) = nm ++ " :: " ++ show t ++ " Lens " ++ show x
fullVar x = "NOT A VAR " ++ show x

-- | Show all the details of every Var Term in a Target
targetVars :: Target era t -> [String]
targetVars t = help [] t
  where
    help :: [String] -> Target era t -> [String]
    help ans s = case s of
      (a :$ b) -> help (help ans a) b
      (Simple x) -> (fullVar x) : ans
      (Constr _ _) -> ans
      (Invert x _) -> help ans x

-- | Information to ReAccess a Term to the type 's', given it is
--  currently Accessed to the type NewEpochState
data ReAccess era s = ReAccess (Rep era s) (Lens' (NewEpochState era) s)

-- | An example, information to ReAccess to Dstate
dstateReAccess :: ReAccess era (DState era)
dstateReAccess = ReAccess DStateR (nesEsL . esLStateL . lsCertStateL . certDStateL)

-- | ReAccess a (V era t) from NewEpochState to type 's'
reAccessV :: Reflect era => V era t -> (ReAccess era s) -> V era t
reAccessV
  (V nm tRep (Yes newepochRep newepochToTLens))
  (ReAccess sRep newepochToSLens) =
    case testEql newepochRep NewEpochStateR of
      Just Refl -> V nm tRep (Yes sRep (magicLens newepochToSLens . newepochToTLens))
      --        ^ Note the composition of the magicLens with the existing Lens
      Nothing -> error (nm ++ " does not have NewEpochState Access.")
reAccessV (V nm _ No) _ = error (nm ++ " does not have any Access.")

-- | Construct a magic Lens' that flips a (Lens' (NewEpochState era) d) to (Lens' d (NewEpochState era))
--  It does this by constructing an empty NewEpochState context around the type 'd'
--  By composing this with an existing Access field, we can change how it is accessed
magicLens :: forall era d. Reflect era => Lens' (NewEpochState era) d -> Lens' d (NewEpochState era)
magicLens l =
  lens
    (\d -> (newEpochStateZero @era) & l .~ d)
    (\_ e -> e ^. l)

-- | ReAccess a Var term from NewEpochState to type 's'
reAccessVar :: Reflect era => Term era t -> (ReAccess era s) -> Term era t
reAccessVar (Var v) acc = Var (reAccessV v acc)
reAccessVar term _ = error ("Can't reAccess " ++ show term ++ ", it is not a Var.")

-- | Change the Access of a Target from NewEpochState to 's'
reAccessTarget :: Reflect era => Target era t -> (ReAccess era s) -> Target era t
reAccessTarget t acc = case t of
  (a :$ b) -> reAccessTarget a acc :$ reAccessTarget b acc
  (Simple (Var v)) -> Simple (Var (reAccessV v acc))
  (Simple term) -> Simple term
  (Constr x y) -> Constr x y
  (Invert x f) -> Invert (reAccessTarget x acc) f

-- | fetch a Value of type 't' from a value of type 's', provided the Var term
--   has an Access field of type 's'
fetch :: Rep era s -> Term era t -> s -> Maybe t
fetch r1 (Var (V _ _ (Yes r2 l))) s = case testEql r1 r2 of
  Just Refl -> Just (s ^. l)
  Nothing -> Nothing
fetch _ _ _ = Nothing

-- | Fetch a value of type 't' from a value of type 's', using a Var term that
-- is accessed to NewEpochState, by reAccessing it using 'acc' to one Accessed by 's'
fetchVar :: Reflect era => Term era t -> ReAccess era s -> s -> Maybe t
fetchVar term acc@(ReAccess repS _) t = fetch repS (reAccessVar term acc) t

-- | an example Target that has been ReAccessed
dstateT2 :: Reflect era => Proof era -> Target era (DState era)
dstateT2 _ = reAccessTarget dstateT dstateReAccess

-- | A Test of experiment 1
main :: IO ()
main = do
  let proof = Conway Standard
  (env, DependGraph zs) <- generate (solvePipeline (ledgerPipeline proof))

  -- run the Target to get the value using the ReAccessed dstateT, and print it
  dstateV <- monadTyped $ runTarget env (dstateT2 proof)
  putStrLn (show (pcDState dstateV))

  -- Show that all the vars from the ReAccessed dstateT exist, and that
  -- 1) Their constraints are in the DependGraph
  -- 2) That they have been ReAccessed to DState
  let vs = varsOfTarget Set.empty (dstateT2 proof)
  let ok (xs, _) = any (\x -> Set.member x vs) xs
  putStrLn (show (DependGraph (filter ok zs)))
  putStrLn (unlines (targetVars (dstateT2 proof)))

  -- Demonstrate that we can fetch the 'rewards' field using the ReAccessed 'rewards' var
  let xx = fetchVar rewards dstateReAccess dstateV
  putStrLn (show (ppMaybe (ppMap pcCredential pcCoin) xx))

-- ======================================================================
-- Experiment number 2, Create a new type of Target that is Invertable
-- This requires adding a new Constructor to the type Target
-- ======================================================================

bindT :: Term era t -> t -> P era
bindT (Var v) t = P v t
bindT term _ = error ("bindT applied to a non Var: " ++ show term)

dstateT3 :: Target era (DState era)
dstateT3 = Invert dstateT f
  where
    f d =
      bulkStore
        [ bindT rewards (d ^. (dsUnifiedL . rewardsUMapL))
        , bindT stakeDeposits (d ^. (dsUnifiedL . stakeDepositsUMapL))
        , bindT delegations (d ^. (dsUnifiedL . delegationsUMapL))
        , bindT ptrs (d ^. (dsUnifiedL . ptrsUMapL))
        , bindT futureGenDelegs (d ^. dsFutureGenDelegsL)
        , bindT genDelegs (d ^. (dsGenDelegsL . unGenDelegsL))
        -- We are deliberately ignoring instantaneousRewards for now
        ]

invert :: Target era t -> t -> Env era -> Env era
invert (Invert _ f) = f
invert x = error ("Target " ++ show x ++ " is not an Invert Target")

-- | A Test of experiment 2
main2 :: IO ()
main2 = do
  let proof = Conway Standard
  (env, DependGraph zs) <- generate (solvePipeline (ledgerPipeline proof))

  -- run the Target to get the value using the ReAccessed dstateT, and print it
  dstateV <- monadTyped $ runTarget env dstateT3
  putStrLn (show (pcDState dstateV))

  -- Show that all the vars from the ReAccessed dstateT exist, and that
  -- 1) Their constraints are in the DependGraph
  let vs = varsOfTarget Set.empty dstateT3
  let ok (xs, _) = any (\x -> Set.member x vs) xs
  putStrLn (show (DependGraph (filter ok zs)))

  -- Show that dstateT3 is invertable
  putStrLn (show (invert dstateT3 dstateV emptyEnv))
