{-# LANGUAGE GADTs #-}

module Test.Cardano.Ledger.Constrained.Preds.Repl where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Size (seps)
import Test.Cardano.Ledger.Constrained.TypeRep

-- import System.IO(getLine)

repl :: Proof era -> Env era -> IO ()
repl proof env@(Env emap) =
  do
    putStr "prompt> "
    mstr <- getLine
    case mstr of
      ":q" -> return ()
      "help" -> goRepl proof env []
      "?" -> goRepl proof env []
      (':' : 'p' : more) -> goRepl proof env more
      str ->
        case Map.lookup str emap of
          Nothing -> putStrLn "Not found" >> repl proof env
          Just (Payload rep t _) -> do
            putStrLn (str ++ " :: " ++ show rep)
            putStrLn (format rep t)
            repl proof env

goRepl :: Proof era -> Env era -> String -> IO ()
goRepl proof env@(Env emap) more = do
  let ok = Map.filterWithKey (\k _ -> List.isPrefixOf more k) emap
  if more == ""
    then
      putStrLn
        ( unlines
            [ "\nEnter one of these Strings at the 'prompt>' to see its value."
            , "Type ':q' to exit."
            , "Type ':pXXX' to see variables whose name have prefix 'XXX'."
            , "Type 'help' or '?' to see these instructions.\n"
            ]
        )
    else pure ()
  putStrLn (seps (Set.toList (Map.keysSet ok)))
  putStrLn ""
  repl proof env

-- List.isPrefixOf
