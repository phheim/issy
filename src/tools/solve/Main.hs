module Main where

import Issy (argumentDescription, argumentParser, fromSG, parseIssyFormat, solve, specToSG)

import Common (checkArgs, liftErr)

main :: IO ()
main = do
  args <- checkArgs argumentDescription
  cfg <- liftErr $ argumentParser args
  input <- getContents
  spec <- liftErr $ parseIssyFormat input
  game <- specToSG cfg spec
  solve cfg (fromSG game)
