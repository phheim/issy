module Main
  ( main
  ) where

import Control.Monad ((>=>))
import System.Exit (die)

import Issy (parseRPG, printRPG, rpgProduct)

import Common (checkArgs, liftErr)

main :: IO ()
main = do
  args <- checkArgs "TODO: WRITE HELP DESCIRPTION"
  case args of
    [] -> die "Expected at least on argument"
    [f] -> readFile f >>= (liftErr . parseRPG) >>= (putStrLn . printRPG)
    fs -> do
      games <- mapM (readFile >=> (liftErr . parseRPG)) fs
      putStrLn (printRPG (rpgProduct games))
