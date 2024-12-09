module Main where

import Issy (parseRPG, printRPG)

import Common (liftErr)

main :: IO ()
main = do
  input <- getContents
  game <- liftErr $ parseRPG input
  putStrLn (printRPG game)
