module Main where

import Issy (parseRPG, printRPG)

main :: IO ()
main = do
  input <- getContents
  case parseRPG input of
    Left err -> fail err
    Right game -> putStrLn (printRPG game)
