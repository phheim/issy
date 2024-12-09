module Main where

import Issy (argumentDescription, argumentParser, fromRPG, parseRPG, solve)

import Common (checkArgs, liftErr)

main :: IO ()
main = do
  args <- checkArgs argumentDescription
  cfg <- liftErr $ argumentParser args
  input <- getContents
  spec <- liftErr $ parseRPG input
  solve cfg (fromRPG spec)
