{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Cardano.Ledger.Constrained.Preds.TxOut where

import Cardano.Ledger.Alonzo.Scripts.Data (Data (..), Datum (..), dataToBinaryData, hashData)
import Cardano.Ledger.Alonzo.TxOut (AlonzoEraTxOut (..), AlonzoTxOut (..))
import Cardano.Ledger.Babbage.TxOut (BabbageEraTxOut (..), BabbageTxOut (..))
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core (Era (EraCrypto), EraScript (..), EraTxOut (..), Script, TxOut, addrTxOutL, coinTxOutL, hashScript, valueTxOutL)
import Cardano.Ledger.Hashes (DataHash)
import Cardano.Ledger.Pretty (ppList, ppMap)
import Cardano.Ledger.Shelley.TxOut (ShelleyTxOut (..))
import qualified Data.Map.Strict as Map
import Data.Maybe.Strict (StrictMaybe (..), maybeToStrictMaybe, strictMaybeToMaybe)
import Lens.Micro
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Classes
import Test.Cardano.Ledger.Constrained.Combinators (genFromMap, itemFromSet)
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Monad (monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.Universes
import Test.Cardano.Ledger.Constrained.Rewrite (rewriteGen, standardOrderInfo)
import Test.Cardano.Ledger.Constrained.Size
import Test.Cardano.Ledger.Constrained.Solver (toolChain, toolChainSub)
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Fields (TxBodyField (..), TxOutField (..))
import Test.Cardano.Ledger.Generic.PrettyCore (pcData, pcDataHash, pcScript, pcScriptHash, pcTxOut)
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Updaters (newTxBody, newTxOut)
import Test.QuickCheck

-- import Test.Cardano.Ledger.Mary.Arbitrary(hashOfDigitByteStrings)

import Cardano.Crypto.Hash.Class (Hash, HashAlgorithm, castHash, hashWith)
import Cardano.Ledger.Hashes (ScriptHash (..))
import Cardano.Ledger.Mary.Value (
  AssetName (..),
  MaryValue (..),
  MultiAsset (..),
  PolicyID (..),
  multiAssetFromList,
 )
import Data.Int (Int64)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString (..))

-- =========================================================================

scriptFL :: Reflect era => Lens' (Script era) (ScriptF era)
scriptFL = lens (ScriptF reify) (\_ (ScriptF _ u) -> u)

strictMaybeMaybeL :: Lens' (StrictMaybe a) (Maybe a)
strictMaybeMaybeL = lens strictMaybeToMaybe (const maybeToStrictMaybe)

txoutRefScriptL :: (Reflect era, BabbageEraTxOut era) => Lens' (TxOutF era) (Maybe (ScriptF era))
txoutRefScriptL = txOutFL . referenceScriptTxOutL . strictMaybeMaybeL . liftMaybeL scriptFL

liftMaybeL :: Lens' a b -> Lens' (Maybe a) (Maybe b)
liftMaybeL l = lens foo bar
  where
    foo (Just x) = Just (x ^. l)
    foo Nothing = Nothing
    bar (Just a) (Just b) = Just (a & l .~ b)
    bar (Just _a) Nothing = Nothing -- Type wise this Nothing could be (Just a), but that is wrong
    bar Nothing _ = Nothing

txoutScriptF :: (Reflect era, BabbageEraTxOut era) => Field era (TxOutF era) (Maybe (ScriptF era))
txoutScriptF = Field "txoutScript" (MaybeR (ScriptR reify)) (TxOutR reify) txoutRefScriptL

txoutScript :: (Reflect era, BabbageEraTxOut era) => Term era (Maybe (ScriptF era))
txoutScript = fieldToTerm txoutScriptF

txoutDatumF :: (Reflect era, BabbageEraTxOut era) => Field era (TxOutF era) (Datum era)
txoutDatumF = Field "txoutDatumF" DatumR (TxOutR reify) (txOutFL . datumTxOutL)

txoutDatum :: (Reflect era, BabbageEraTxOut era) => Term era (Datum era)
txoutDatum = fieldToTerm txoutDatumF

txoutDataHashF :: (Reflect era, AlonzoEraTxOut era) => Field era (TxOutF era) (Maybe (DataHash (EraCrypto era)))
txoutDataHashF =
  Field
    "txoutDataHashF"
    (MaybeR DataHashR)
    (TxOutR reify)
    (txOutFL . dataHashTxOutL . strictMaybeMaybeL)

txoutDataHash :: (Reflect era, AlonzoEraTxOut era) => Term era (Maybe (DataHash (EraCrypto era)))
txoutDataHash = fieldToTerm txoutDataHashF

-- ==============================================

outNames :: [String]
outNames =
  [ "address"
  , "amount"
  , "dhash"
  , "fdatum"
  , "refscript"
  ]

lookupTxOut :: Env era -> String -> [TxOutField era]
lookupTxOut (Env m) name = case (name, Map.lookup name m) of
  ("address", Just (Payload AddrR t _)) -> [Address t]
  ("amount", Just (Payload (ValueR _) (ValueF _ v) _)) -> [Amount v]
  _ -> []

txOutFromEnv :: Proof era -> Env era -> TxOut era
txOutFromEnv proof env = unReflect newTxOut proof (concat (map (lookupTxOut env) outNames))

-- ================================================================================

txOutPreds :: (Reflect era) => Proof era -> Term era Coin -> Term era [TxOutF era] -> [Pred era]
txOutPreds p balanceCoin outputS =
  [ Choose
      (Range 6 6)
      datums
      [ (Simple (Lit DatumR NoDatum), [])
      , (Constr "DatumHash" DatumHash ^$ hash, [Member hash (Dom dataUniv)])
      , (Constr "Datum" (Datum . dataToBinaryData) ^$ dat, [Member (HashD dat) (Dom dataUniv)])
      ]
  , datumsSet :<-: listToSetTarget datums
  , case whichTxOut p of
      TxOutShelleyToMary ->
        ForEach
          (Range 5 5)
          outputS
          ( Pat
              outR
              [ Arg txoutAddressF
              , ArgPs txoutAmountF [Pat (ValueR p) [Arg valCoinF], Pat (ValueR p) [Arg valueFMultiAssetF]]
              ]
          )
          [ Member txoutAddress addrUniv
          , Component (Right txoutAmount) [field (ValueR p) valCoin, field (ValueR p) valueFMultiAsset]
          , SumsTo (Left (Coin 1)) balanceCoin EQL [One valCoin]
          , GenFrom valueFMultiAsset (Constr "multiAsset" multiAsset ^$ (scriptUniv p))
          ]
      TxOutAlonzoToAlonzo ->
        ForEach
          (Range 5 5)
          outputS
          ( Pat -- analog to Haskell pattern (TxOut{txoutAddress, txoutAmount{valCoin}, txoutDataHash})
              (TxOutR p)
              [ Arg txoutAddressF
              , ArgPs txoutAmountF [Pat valueR [Arg valCoinF], Pat (ValueR p) [Arg valueFMultiAssetF]]
              , Arg txoutDataHashF
              ]
          )
          [ Member txoutAddress addrUniv
          , Component (Right txoutAmount) [field (ValueR p) valCoin]
          , Maybe txoutDataHash (Simple hash) [Member hash (Dom dataUniv)]
          , SumsTo (Left (Coin 1)) balanceCoin EQL [One valCoin]
          , GenFrom valueFMultiAsset (Constr "multiAsset" multiAsset ^$ (scriptUniv p))
          ]
      TxOutBabbageToConway ->
        ForEach
          (Range 5 5)
          outputS
          ( Pat
              (TxOutR p)
              [ Arg txoutAddressF
              , argP outR txoutAmount [Pat (ValueR p) [Arg valCoinF], Pat (ValueR p) [Arg valueFMultiAssetF]]
              , Arg txoutScriptF
              , Arg txoutDatumF
              ]
          )
          [ Member txoutAddress addrUniv
          , Component (Right txoutAmount) [field (ValueR p) valCoin]
          , Maybe txoutScript (Simple script) [Member (HashS script) (Dom (spendscriptUniv p))]
          , Member txoutDatum datumsSet
          , SumsTo (Left (Coin 2)) balanceCoin EQL [One valCoin]
          , GenFrom valueFMultiAsset (Constr "multiAsset" multiAsset ^$ (scriptUniv p))
          ]
  ]
  where
    outR = TxOutR p
    valueR = ValueR p
    script = (var "x" (ScriptR p))
    datums = var "datums" (ListR DatumR)
    datumsSet = var "datumsSet" (SetR DatumR)
    hash = var "hash" DataHashR
    dat = var "dat" DataR

main :: IO ()
main = do
  let proof = Babbage Standard
  -- rewritten <- snd <$> generate (rewriteGen (1,(txOutPreds proof (Lit CoinR (Coin 100)) (outputs proof))))
  env <-
    generate
      ( pure []
          >>= universeStage proof
          >>= toolChain proof standardOrderInfo (txOutPreds proof (Lit CoinR (Coin 100)) (outputs proof))
      )
  -- putStrLn (show rewritten)
  -- putStrLn ""
  -- putStrLn (show env)
  outs <- monadTyped (findVar (unVar (outputs proof)) env)
  scrs <- monadTyped (findVar (unVar (spendscriptUniv proof)) env)
  datauniv <- monadTyped (findVar (unVar dataUniv) env)
  putStrLn (show (ppMap pcDataHash pcData datauniv))
  putStrLn (show (ppList (pcTxOut proof . unTxOut) outs))
  putStrLn (show (ppMap pcScriptHash (pcScript proof . unScriptF) scrs))
