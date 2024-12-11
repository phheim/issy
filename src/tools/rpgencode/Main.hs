module Main where

import System.Exit (die)

import Issy (parseRPG, rpgToMuCLP, rpgToTSLT)

import Common (checkArgs, liftErr)

main :: IO ()
main = do
  input <- getContents
  (g, wc) <- liftErr (parseRPG input)
  args <- checkArgs "TODO HELP TEXT"
  case args of
    ["muclp"] -> putStrLn $ rpgToMuCLP g wc
    ["tslt"] -> putStrLn $ rpgToTSLT g wc
    arg -> die $ "Unkown argument" ++ concatMap (" " ++) arg
