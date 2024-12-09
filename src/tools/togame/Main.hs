module Main where

import Issy (argumentDescription, argumentParser, parseIssyFormat, printSG, specToSG)

import Common (checkArgs, liftErr)

main :: IO ()
main = do
  args <- checkArgs argumentDescription
  cfg <- liftErr $ argumentParser args
  input <- getContents
  spec <- liftErr $ parseIssyFormat input
  game <- specToSG cfg spec
  putStrLn $ printSG game
