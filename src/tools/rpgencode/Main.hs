module Main where

import System.Environment (getArgs)

import Issy (parseRPG)

import qualified MuCLP
import qualified TSLT

main :: IO ()
main = do
  input <- getContents
  case parseRPG input of
    Left err -> fail err
    Right (g, wc) -> do
      args <- getArgs
      case args of
        ["muclp"] -> putStrLn (MuCLP.convert g wc)
        ["tslt"] -> putStrLn (TSLT.convert g wc)
        _ -> error "Unkown arguments"
