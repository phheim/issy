module Main where

import Issy (argumentDescription, argumentParser, parseTSL, printRPG, tslToRPG)

import Common (checkArgs, liftErr)

main :: IO ()
main = do
  args <- checkArgs argumentDescription
  cfg <- liftErr $ argumentParser args
  input <- getContents
  spec <- parseTSL input
  game <- tslToRPG cfg spec
  putStrLn $ printRPG game
