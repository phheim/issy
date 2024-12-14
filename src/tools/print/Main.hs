module Main where

import Issy
  ( argumentDescription
  , argumentParser
  , checkSpecification
  , parseIssyFormat
  , printIssyFormat
  )

import Common (checkArgs, liftErr)

main :: IO ()
main = do
  args <- checkArgs argumentDescription
  cfg <- liftErr $ argumentParser args
  input <- getContents
  spec <- liftErr $ parseIssyFormat input
  checkSpecification cfg spec >>= liftErr
  putStrLn (printIssyFormat spec)
