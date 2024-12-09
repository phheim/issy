module Main where

import System.Exit (die)

import Issy (parseRPG)

import qualified MuCLP
import qualified TSLT

import Common (checkArgs, liftErr)

main :: IO ()
main = do
  input <- getContents
  (g, wc) <- liftErr (parseRPG input)
  args <- checkArgs "TODO HELP TEXT"
  case args of
    ["muclp"] -> putStrLn (MuCLP.convert g wc)
    ["tslt"] -> putStrLn (TSLT.convert g wc)
    arg -> die $ "Unkown argument" ++ concatMap (" " ++) arg
