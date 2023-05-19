{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- {-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Cardano.Ledger.Constrained.Preds.Universes
where

import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Classes hiding (genTxOut)
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Monad (monadTyped)
import Test.Cardano.Ledger.Constrained.Rewrite (standardOrderInfo)
import Test.Cardano.Ledger.Constrained.Solver
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Proof
import Test.Tasty.QuickCheck

import Cardano.Ledger.Address (Addr (..))
import Test.Cardano.Ledger.Shelley.Utils (epochFromSlotNo)

import Cardano.Ledger.Allegra.Scripts (ValidityInterval (..))
import qualified Cardano.Ledger.Alonzo.Scripts as Scripts (Tag (..))
import Cardano.Ledger.BaseTypes (
  Network (..),
  SlotNo (..),
  StrictMaybe (..),
  TxIx (..),
  mkCertIxPartial,
 )

import Cardano.Ledger.Alonzo.Scripts.Data (Data (..), Datum (..), dataToBinaryData, hashData)
import Cardano.Ledger.Alonzo.TxOut (AlonzoTxOut (..))
import Cardano.Ledger.Babbage.TxOut (BabbageTxOut (..))
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core (
  EraScript,
  EraTxOut (..),
  TxOut,
  Value,
  hashScript,
  isNativeScript,
 )
import Cardano.Ledger.Credential (Credential (..), Ptr (..), StakeReference (..))
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Hashes (DataHash, ScriptHash)
import Cardano.Ledger.Keys (KeyHash, KeyRole (..), coerceKeyRole)
import Cardano.Ledger.Mary.Value (
  AssetName (..),
  MaryValue (..),
  MultiAsset (..),
  PolicyID (..),
  multiAssetFromList,
 )
import Cardano.Ledger.Pretty (ppList)
import Cardano.Ledger.Shelley.TxOut (ShelleyTxOut (..))
import Cardano.Ledger.Val (Val (inject))
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString (..))
import Test.Cardano.Ledger.Constrained.Combinators (genFromMap, itemFromSet, mapSized, setSized)
import Test.Cardano.Ledger.Constrained.Preds.Repl (goRepl)
import Test.Cardano.Ledger.Constrained.Scripts (genCoreScript)
import Test.Cardano.Ledger.Core.KeyPair (KeyPair (..))
import Test.Cardano.Ledger.Generic.PrettyCore (pcMultiAsset)

-- ============================================================

variedCoin :: Gen Coin
variedCoin =
  Coin
    <$> frequency
      [ (12, pure 0)
      , (5, choose (1, 10))
      , (10, choose (11, 100))
      , (8, choose (101, 1000))
      , (7, choose (1001, 10000))
      , (2, choose (10001, 100000))
      ]

noZeroCoin :: Gen Coin
noZeroCoin =
  Coin
    <$> frequency
      [ (5, choose (1, 10))
      , (10, choose (11, 100))
      , (8, choose (101, 1000))
      , (7, choose (1001, 10000))
      , (2, choose (10001, 100000))
      ]

-- | The universe of non-empty Datums. i.e. There are no NoDatum Datums in this list
genDatums :: Era era => Int -> Map (DataHash (EraCrypto era)) (Data era) -> Gen [Datum era]
genDatums n datauniv = vectorOf n (genDatum datauniv)

-- | Only generate non-empty Datums. I.e. There are no NoDatum Datums generated.
genDatum :: Era era => Map (DataHash (EraCrypto era)) (Data era) -> Gen (Datum era)
genDatum datauniv =
  oneof
    [ DatumHash . fst <$> genFromMap ["from genDatums DatumHash case"] datauniv
    , Datum . dataToBinaryData . snd <$> genFromMap ["from genDatums Datum case"] datauniv
    ]

genValueF :: Proof era -> Coin -> Map (ScriptHash (EraCrypto era)) (ScriptF era) -> Gen (Value era)
genValueF p (Coin c) scripts = case whichValue p of
  ValueShelleyToAllegra -> pure (Coin c)
  ValueMaryToConway -> MaryValue c <$> multiAsset scripts

genTxOut ::
  Reflect era =>
  Proof era ->
  Coin ->
  Set (Addr (EraCrypto era)) ->
  Map (ScriptHash (EraCrypto era)) (ScriptF era) ->
  Map (ScriptHash (EraCrypto era)) (ScriptF era) ->
  Map (DataHash (EraCrypto era)) (Data era) ->
  Gen (TxOut era)
genTxOut p c addruniv scriptuniv spendscriptuniv datauniv =
  case whichTxOut p of
    TxOutShelleyToMary ->
      ShelleyTxOut <$> pick1 ["genTxOut ShelleyToMary Addr"] addruniv <*> genValueF p c scriptuniv
    TxOutAlonzoToAlonzo -> do
      addr <- pick1 ["genTxOut AlonzoToAlonzo Addr"] addruniv
      v <- genValueF p c scriptuniv
      case addr of
        AddrBootstrap _ -> pure (AlonzoTxOut addr v SNothing)
        Addr _ paycred _ ->
          if needsDatum paycred spendscriptuniv
            then
              AlonzoTxOut addr v . SJust . fst
                <$> genFromMap ["from genTxOut, AlonzoToAlonzo, needsDatum case"] datauniv
            else pure (AlonzoTxOut addr v SNothing)
    TxOutBabbageToConway -> do
      addr <- pick1 ["genTxOut BabbageToConway Addr"] addruniv
      v <- genValueF p c scriptuniv
      (ScriptF _ refscript) <- snd <$> genFromMap ["genTxOut, BabbageToConway, refscript case"] scriptuniv
      maybescript <- elements [SNothing, SJust refscript]
      case addr of
        AddrBootstrap _ -> pure $ BabbageTxOut addr v NoDatum maybescript
        Addr _ paycred _ ->
          if needsDatum paycred spendscriptuniv
            then BabbageTxOut addr v <$> genDatum datauniv <*> pure maybescript
            else pure $ BabbageTxOut addr v NoDatum maybescript

needsDatum :: EraScript era => Credential 'Payment (EraCrypto era) -> Map (ScriptHash (EraCrypto era)) (ScriptF era) -> Bool
needsDatum (ScriptHashObj hash) spendScriptUniv = case Map.lookup hash spendScriptUniv of
  Nothing -> False
  Just (ScriptF _ script) -> not (isNativeScript script)
needsDatum _ _ = False

genTxOuts ::
  Reflect era =>
  Proof era ->
  Set (Addr (EraCrypto era)) ->
  Map (ScriptHash (EraCrypto era)) (ScriptF era) ->
  Map (ScriptHash (EraCrypto era)) (ScriptF era) ->
  Map (DataHash (EraCrypto era)) (Data era) ->
  Gen [TxOutF era]
genTxOuts p addruniv scriptuniv spendscriptuniv datauniv = do
  let genOne = do
        c <- noZeroCoin
        genTxOut p c addruniv scriptuniv spendscriptuniv datauniv
  vectorOf 30 (TxOutF p <$> genOne)

-- ==================================================================
-- MultiAssets

assets :: Set AssetName
assets = Set.fromList [AssetName (fromString ("Asset" ++ show (n :: Int))) | n <- [1 .. 10]]

genMultiAssetTriple ::
  Map.Map (ScriptHash (EraCrypto era)) (ScriptF era) ->
  Set AssetName ->
  Gen Integer ->
  Gen (PolicyID (EraCrypto era), AssetName, Integer)
genMultiAssetTriple scriptMap assetSet genAmount =
  (,,)
    <$> (PolicyID . fst <$> (genFromMap [] scriptMap))
    <*> (fst <$> (itemFromSet [] assetSet))
    <*> genAmount

multiAsset :: Map.Map (ScriptHash (EraCrypto era)) (ScriptF era) -> Gen (MultiAsset (EraCrypto era))
multiAsset scripts = do
  n <- elements [0, 1, 2]
  if n == 0
    then pure mempty -- About 1/3 of the list will be the empty MA
    else do
      -- So lots of duplicates, but we want to choose the empty MA, 1/3 of the time.
      xs <- vectorOf n (genMultiAssetTriple scripts assets (choose (1, 100)))
      pure $ multiAssetFromList xs

-- ===================================================================
-- Generating a solution for the Universes directly in the Gen monad.

item' :: Term era t -> t -> SubItem era
item' (Var (V name rep _)) t = SubItem (V name rep No) (Lit rep t)
item' term _ = error ("item' applied to non Var Term: " ++ show term)

scriptWits ::
  Cardano.Ledger.Core.EraScript era =>
  Proof era ->
  Int ->
  Scripts.Tag ->
  Map
    (KeyHash 'Witness (EraCrypto era))
    (KeyPair 'Witness (EraCrypto era)) ->
  ValidityInterval ->
  Gen (Map (ScriptHash (EraCrypto era)) (ScriptF era))
scriptWits p size tag m vi = do
  scs <- vectorOf size (genCoreScript p tag m vi)
  pure $ Map.fromList $ map (\x -> (hashScript x, ScriptF p x)) scs

dataWits ::
  Era era =>
  Proof era ->
  Int ->
  Gen (Map (DataHash (EraCrypto era)) (Data era))
dataWits _p size = do
  scs <- vectorOf size arbitrary
  pure $ Map.fromList $ map (\x -> (hashData x, x)) scs

genAddrWith ::
  Network ->
  Set (Credential 'Payment c) ->
  Set Ptr ->
  Set (Credential 'Staking c) ->
  Gen (Addr c)
genAddrWith net ps ptrss cs =
  frequency
    [ (8, Addr net <$> pick1 ["from genPayCred ScriptHashObj"] ps <*> genStakeRefWith ptrss cs)
    , (2, AddrBootstrap <$> arbitrary)
    ]

pick1 :: [String] -> Set t -> Gen t
pick1 msgs s = fst <$> itemFromSet ("from pick1" : msgs) s

genStakeRefWith :: Set Ptr -> Set (Credential 'Staking c) -> Gen (StakeReference c)
genStakeRefWith ps cs =
  frequency
    [ (80, StakeRefBase <$> pick1 ["from genStakeRefWith StakeRefBase"] cs)
    , (5, StakeRefPtr <$> pick1 ["from genStakeRefWith StakeRefPtr"] ps)
    , (15, pure StakeRefNull)
    ]

genPtr :: SlotNo -> Gen Ptr
genPtr (SlotNo n) =
  Ptr
    <$> (SlotNo <$> choose (0, n))
    <*> (TxIx <$> choose (0, 10))
    <*> (mkCertIxPartial <$> choose (1, 20))

initUniv :: forall era. Reflect era => Proof era -> Gen (Subst era)
initUniv p = do
  poolsuniv <- setSized ["From init poolsuniv"] 30 (genRep @era PoolHashR)
  votehashuniv <- setSized ["From init votehashuniv"] 30 (genRep @era VHashR)
  keymapuniv <- mapSized ["From init keymapuniv"] 30 (genRep @era WitHashR) (genRep @era KeyPairR)
  genesisuniv <- mapSized ["From init genesisuniv"] 10 (genRep @era GenHashR) (genRep @era GenDelegPairR)
  txinuniv <- setSized ["From init txinuniv"] 30 (genRep @era TxInR)
  lower <- choose (100, 500)
  let slotno = (lower + 3)
  upper <- choose (slotno + 1, slotno + 6)
  let validityinterval = ValidityInterval (SJust (SlotNo lower)) (SJust (SlotNo upper))
  spendscriptuniv <- scriptWits p 25 Scripts.Spend keymapuniv validityinterval
  scriptuniv <- scriptWits p 25 Scripts.Cert keymapuniv validityinterval
  multiassetuniv <- (vectorOf 50 (multiAsset scriptuniv)) :: Gen [MultiAsset (EraCrypto era)]
  datauniv <- dataWits p 30
  datumsuniv <- genDatums 30 datauniv
  creduniv <-
    setSized
      ["From init creduniv"]
      30
      ( oneof
          [ ScriptHashObj . fst <$> genFromMap ["From init, creduniv, ScriptHashObj"] scriptuniv
          , KeyHashObj . coerceKeyRole . fst <$> genFromMap ["From init, creduniv, KeyHashObj"] keymapuniv
          ]
      )
  spendcreduniv <- -- For use in Payment part of Addr, Plutus scripts take a redeemer
    setSized
      ["From init creduniv"]
      50
      ( oneof
          [ ScriptHashObj . fst <$> genFromMap ["From init, creduniv, ScriptHashObj"] spendscriptuniv
          , KeyHashObj . coerceKeyRole . fst <$> genFromMap ["From init, creduniv, KeyHashObj"] keymapuniv
          ]
      )
  networkv <- arbitrary
  ptruniv <- setSized ["From init ptruniv"] 30 (genPtr (SlotNo slotno))
  addruniv <- setSized ["From init addruniv"] 40 (genAddrWith networkv spendcreduniv ptruniv creduniv)
  colltxoutuniv <- setSized ["From init colTxoutUniv"] 10 (colTxOutT p (Set.filter (noScripts p) addruniv))
  txoutsuniv <- genTxOuts p addruniv scriptuniv spendscriptuniv datauniv
  bigcoin <- pure (Coin 2000000)
  feetxout <- txOutT p <$> pick1 [] (Set.filter (noScripts p) addruniv) <*> pure bigcoin

  pure
    [ item' poolHashUniv poolsuniv
    , item' genesisHashUniv genesisuniv
    , item' voteHashUniv votehashuniv
    , item' keymapUniv keymapuniv
    , item' currentSlot (SlotNo slotno)
    , item' validityInterval validityinterval
    , item' (spendscriptUniv p) spendscriptuniv
    , item' (scriptUniv p) scriptuniv
    , item' dataUniv datauniv
    , item' datumsUniv datumsuniv
    , item' credsUniv creduniv
    , item' spendCredsUniv spendcreduniv
    , item' payUniv spendcreduniv
    , item' voteUniv (Set.map coerceKeyRole creduniv)
    , item' txinUniv txinuniv
    , item' currentEpoch (epochFromSlotNo (SlotNo slotno))
    , item' network networkv
    , item' ptrUniv ptruniv
    , item' addrUniv addruniv
    , item' multiAssetUniv multiassetuniv
    , item' (txoutUniv p) (Set.insert feetxout (Set.union colltxoutuniv (Set.fromList txoutsuniv)))
    , item' bigCoin bigcoin
    , item' feeTxOut feetxout
    , item' (colTxoutUniv p) colltxoutuniv
    ]

noScripts :: Proof era -> Addr (EraCrypto era) -> Bool
noScripts _ (Addr _ (ScriptHashObj _) _) = False
noScripts _ (Addr _ _ (StakeRefBase (ScriptHashObj _))) = False
noScripts _ (AddrBootstrap _) = False
noScripts _ _ = True

txOutT :: Reflect era => Proof era -> Addr (EraCrypto era) -> Coin -> TxOutF era
txOutT p x c = TxOutF p (mkBasicTxOut x (inject c))

-- | The collateral consists only of VKey addresses
--   and the collateral outputs in the UTxO do not contain any non-ADA part
colTxOutT :: EraTxOut era => Proof era -> Set (Addr (EraCrypto era)) -> Gen (TxOutF era)
colTxOutT p noScriptAddr = TxOutF p <$> (mkBasicTxOut <$> pick1 [] noScriptAddr <*> (inject <$> noZeroCoin))

-- ======================================================================
-- Reusable Targets. First order representations of functions for use in
-- building 'Target's. We will apply these to Term variables,
-- (using  (:$) and (^$)) to indicate how to construct a random values assigned
-- to those variables. By convention we name these "functional" targets by
-- post-fixing their names with a captial "T". These may be a bit more
-- prescriptive rather than descriptive, but you do what you have to do.

scriptHashObjT :: Term era (ScriptHash (EraCrypto era)) -> Target era (Credential k (EraCrypto era))
scriptHashObjT x = Constr "ScriptHashObj" ScriptHashObj ^$ x

keyHashObjT :: Term era (KeyHash 'Witness (EraCrypto era)) -> Target era (Credential k (EraCrypto era))
keyHashObjT x = Constr "KeyHashObj" (KeyHashObj . coerceKeyRole) ^$ x

makeValidityT :: Term era SlotNo -> Term era SlotNo -> Term era SlotNo -> Target era ValidityInterval
makeValidityT begin current end =
  Constr
    "(-i)x(+j)"
    (\i x j -> ValidityInterval (SJust (x - i)) (SJust (x + j)))
    ^$ begin
    ^$ current
    ^$ end

ptrUnivT :: Term era SlotNo -> Target era (Gen (Set Ptr))
ptrUnivT x = Constr "" (setSized ["From init ptruniv"] 30) :$ (Constr "" genPtr ^$ x)

addrUnivT ::
  Term era Network ->
  Term era (Set (Credential 'Payment c)) ->
  Term era (Set Ptr) ->
  Term era (Set (Credential 'Staking c)) ->
  Target era (Gen (Set (Addr c)))
addrUnivT net ps pts cs =
  Constr "" (setSized ["From addrUnivT"] 40)
    :$ (Constr "genAddrWith" genAddrWith ^$ net ^$ ps ^$ pts ^$ cs)

-- =================================================================
-- Using constraints to generate the Universes

scriptWitsT ::
  Proof era ->
  Int ->
  Scripts.Tag ->
  Term era (Map (KeyHash 'Witness (EraCrypto era)) (KeyPair 'Witness (EraCrypto era))) ->
  Term era ValidityInterval ->
  Target era (Gen (Map (ScriptHash (EraCrypto era)) (ScriptF era)))
scriptWitsT p size tag m vi =
  Constr "scriptWits" (unReflect scriptWits p size tag) ^$ m ^$ vi

universePreds :: Reflect era => Proof era -> [Pred era]
universePreds p =
  [ Sized (Range 100 500) currentSlot
  , Sized (Range 0 3) beginSlotDelta
  , Sized (Range 1 15) endSlotDelta
  , Sized (ExactSize 30) poolHashUniv
  , Sized (ExactSize 10) genesisHashUniv
  , Sized (ExactSize 10) voteHashUniv
  , Sized (ExactSize 30) keymapUniv
  , Sized (ExactSize 40) txinUniv
  , Member (Right feeTxIn) txinUniv
  , validityInterval :<-: makeValidityT beginSlotDelta currentSlot endSlotDelta
  , Choose
      (ExactSize 30)
      credList
      [ (scriptHashObjT scripthash, [Member (Left scripthash) (Dom (scriptUniv p))])
      , (keyHashObjT keyhash, [Member (Left keyhash) (Dom keymapUniv)])
      ]
  , credsUniv :<-: listToSetTarget credList
  , Choose
      (ExactSize 50)
      spendcredList
      [ (scriptHashObjT scripthash, [Member (Left scripthash) (Dom (spendscriptUniv p))])
      , (keyHashObjT keyhash, [Member (Left keyhash) (Dom keymapUniv)])
      ]
  , spendCredsUniv :<-: listToSetTarget spendcredList
  , currentEpoch :<-: (Constr "epochFromSlotNo" epochFromSlotNo ^$ currentSlot)
  , GenFrom (spendscriptUniv p) (scriptWitsT p 25 Scripts.Spend keymapUniv validityInterval)
  , GenFrom (scriptUniv p) (scriptWitsT p 25 Scripts.Cert keymapUniv validityInterval)
  , GenFrom dataUniv (Constr "dataWits" (dataWits p) ^$ (Lit IntR 30))
  , GenFrom datumsUniv (Constr "genDatums" (genDatums 30) ^$ dataUniv)
  , GenFrom network (constTarget arbitrary) -- Choose Testnet or Mainnet
  , GenFrom ptrUniv (ptrUnivT currentSlot)
  , GenFrom addrUniv (addrUnivT network spendCredsUniv ptrUniv credsUniv)
  , GenFrom multiAssetUniv (Constr "multiAsset" (vectorOf 50 . multiAsset) ^$ (scriptUniv p))
  , GenFrom preTxoutUniv (Constr "genTxOuts" (genTxOuts p) ^$ addrUniv ^$ (scriptUniv p) ^$ (spendscriptUniv p) ^$ dataUniv)
  , GenFrom
      (colTxoutUniv p)
      ( Constr
          "colTxOutUniv"
          (\x -> setSized ["From init colTxoutUniv"] 10 (colTxOutT p (Set.filter (noScripts p) x)))
          ^$ addrUniv
      )
  , payUniv :=: spendCredsUniv
  , voteUniv :<-: (Constr "coerce" (Set.map stakeToVote) ^$ credsUniv)
  , bigCoin :<-: constTarget (Coin 2000000)
  , GenFrom
      feeTxOut
      ( Constr
          "txout"
          ( \a c ->
              txOutT p
                <$> pick1 [] (Set.filter (noScripts p) a)
                <*> pure c
          )
          ^$ addrUniv
          ^$ bigCoin
      )
  , txoutUniv p
      :<-: ( Constr
              "insert"
              (\x y z -> Set.insert x (Set.union z (Set.fromList y)))
              ^$ feeTxOut
              ^$ preTxoutUniv
              ^$ (colTxoutUniv p)
           )
  ]
  where
    endSlotDelta = Var (V "endSlot.Delta" SlotNoR No)
    beginSlotDelta = Var (V "beginSlot.Delta" SlotNoR No)
    credList = Var (V "cred.list" (ListR CredR) No)
    spendcredList = Var (V "spendcred.list" (ListR PCredR) No)
    keyhash = Var (V "keyhash" WitHashR No)
    scripthash = Var (V "scripthash" ScriptHashR No)
    preTxoutUniv = Var (V "preTxoutUniv" (ListR (TxOutR p)) No)

stakeToVote :: Credential 'Staking c -> Credential 'Voting c
stakeToVote = coerceKeyRole

solveUniv :: Reflect era => Proof era -> Gen (Subst era)
solveUniv proof = do
  toolChainSub proof standardOrderInfo (universePreds proof) []

universeStage ::
  Reflect era =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
universeStage proof =
  if True
    then toolChainSub proof standardOrderInfo (universePreds proof)
    else const (initUniv proof)

mainUniverses :: IO ()
mainUniverses = do
  let proof = Babbage Standard
  subst <- generate (universeStage proof [])
  putStrLn "\n"
  putStrLn (show subst)
  env <- monadTyped (substToEnv subst emptyEnv)
  ptrsx <- monadTyped (findVar (unVar ptrUniv) env)
  putStrLn (show ptrsx)
  multi <- monadTyped (findVar (unVar multiAssetUniv) env)
  putStrLn (show (length multi, length (List.nub multi)))
  putStrLn (show (ppList pcMultiAsset multi))
  goRepl proof env ""
