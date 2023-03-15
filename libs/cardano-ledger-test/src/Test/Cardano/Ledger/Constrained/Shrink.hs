{-# LANGUAGE GADTs #-}

module Test.Cardano.Ledger.Constrained.Shrink where

import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import Cardano.Ledger.Core (Era (..))
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Monad
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.TypeRep

import Test.QuickCheck

shrinkEnv :: Era era => DependGraph era -> Env era -> [Env era]
shrinkEnv (DependGraph vs) env =
  [ env'
  | (before, (x, cs), after) <- splits vs
  , env' <- shrinkOneVar env (map fst before) x cs after
  ]

splits :: [a] -> [([a], a, [a])]
splits [] = []
splits (x : xs) = ([], x, xs) : [(x : ys, y, zs) | (ys, y, zs) <- splits xs]

shrinkOneVar :: Era era => Env era -> [Name era] -> Name era -> [Pred era] -> [(Name era, [Pred era])] -> [Env era]
shrinkOneVar originalEnv before x cs after =
  [ env'
  | val' <- shrinkVar x cs' val
  , let fixup env (y, ycs) = do
          p <- findName y originalEnv
          p' <- fixupVar y (map (substPred $ envToSubst env) ycs) p
          pure $ storeName y p' env
  , env' <- maybeToList $ foldM fixup (storeName x val' beforeEnv) after
  ]
  where
    beforeEnv = restrictEnv before originalEnv
    beforeSubst = envToSubst beforeEnv
    cs' = map (substPred beforeSubst) cs
    val = fromJust $ findName x originalEnv

shrinkVar :: Era era => Name era -> [Pred era] -> Payload era -> [Payload era]
shrinkVar v cs p = [p' | p' <- shrinkPayload p, validAssignment v p' cs]

-- | Compute something satisfying the constraints that's as "close" to the original value as
--   possible. TODO: more cleverness
fixupVar :: Era era => Name era -> [Pred era] -> Payload era -> Maybe (Payload era)
fixupVar v cs p = listToMaybe [p' | p' <- [p | validAssignment v p cs] ++ reverse (shrinkVar v cs p)]

validAssignment :: Name era -> Payload era -> [Pred era] -> Bool
validAssignment v p cs = all (runPred_ $ singletonEnv v p) cs

shrinkPayload :: Era era => Payload era -> [Payload era]
shrinkPayload (Payload rep t acc) = [Payload rep t' acc | t' <- shrinkRep rep t]

shrinkRep :: Era era => Rep era t -> t -> [t]
shrinkRep CoinR t = shrink t
shrinkRep (_ :-> _) _ = []
shrinkRep (MapR a b) t = shrinkMapBy Map.fromList Map.toList (shrinkRep $ ListR (PairR a b)) t
shrinkRep (SetR a) t = shrinkMapBy Set.fromList Set.toList (shrinkRep $ ListR a) t
shrinkRep (ListR a) t = shrinkList (shrinkRep a) t
shrinkRep CredR t = shrink t
shrinkRep PoolHashR t = shrink t
shrinkRep WitHashR t = shrink t
shrinkRep GenHashR t = shrink t
shrinkRep GenDelegHashR t = shrink t
shrinkRep PoolParamsR t = shrink t
shrinkRep EpochR t = shrink t
shrinkRep RationalR t = shrink t
shrinkRep Word64R t = shrink t
shrinkRep IntR t = shrink t
shrinkRep NaturalR t = shrink t
shrinkRep FloatR t = shrink t
shrinkRep TxInR t = shrink t
shrinkRep (ValueR _) _ = []
shrinkRep (TxOutR _) _ = []
shrinkRep (UTxOR _) _ = []
shrinkRep (PParamsR _) _ = []
shrinkRep (PParamsUpdateR _) _ = []
shrinkRep StringR t = shrink t
shrinkRep DeltaCoinR t = shrink t
shrinkRep GenDelegPairR t = shrink t
shrinkRep FutureGenDelegR t = shrink t
shrinkRep (PPUPStateR _) _ = []
shrinkRep PtrR t = shrink t
shrinkRep IPoolStakeR t = shrink t
shrinkRep SnapShotsR t = shrink t
shrinkRep UnitR t = shrink t
shrinkRep (PairR a b) (x, y) = [(x', y) | x' <- shrinkRep a x] ++ [(x, y') | y' <- shrinkRep b y]
shrinkRep RewardR t = shrink t
shrinkRep (MaybeR a) t = shrinkMapBy listToMaybe maybeToList (shrinkRep $ ListR a) t
shrinkRep NewEpochStateR _ = []
shrinkRep (ProtVerR _) t = shrink t
shrinkRep SlotNoR t = shrink t
shrinkRep SizeR _ = []

findName :: Name era -> Env era -> Maybe (Payload era)
findName (Name (V name _ _)) (Env env) = Map.lookup name env

storeName :: Name era -> Payload era -> Env era -> Env era
storeName (Name (V name _ _)) p (Env env) = Env $ Map.insert name p env

restrictEnv :: [Name era] -> Env era -> Env era
restrictEnv names (Env env) = Env $ Map.filterWithKey (\x _ -> elem x xs) env
  where
    xs = [x | Name (V x _ _) <- names]

envToSubst :: Env era -> Subst era
envToSubst (Env env) =
  [ SubItem (V x rep acc) (Lit rep t)
  | (x, Payload rep t acc) <- Map.toList env
  ]

runPred_ :: Env era -> Pred era -> Bool
runPred_ env p = either (const False) id $ runTyped $ runPred env p

singletonEnv :: Name era -> Payload era -> Env era
singletonEnv (Name (V name rep _)) p@(Payload rep' _ _)
  | Just Refl <- testEql rep rep' = Env $ Map.singleton name p
  | otherwise = error $ "singletonEnv: type mismatch " ++ show rep ++ " /= " ++ show rep'
