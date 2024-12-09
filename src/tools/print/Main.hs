module Main where

import Issy (parseIssyFormat, printIssyFormat)

import Common (liftErr)

main :: IO ()
main = do
  input <- getContents
  spec <- liftErr $ parseIssyFormat input
  putStrLn (printIssyFormat spec)
