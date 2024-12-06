module Main where

import System.Environment (getArgs)

import Issy (argumentDescription, argumentParser, parseTSL, printRPG, tslToRPG)

liftErr :: Either String b -> IO b
liftErr res =
  case res of
    Left err -> fail err
    Right res -> return res

main :: IO ()
main = do
  args <- getArgs
  if any (`elem` args) ["--help", "-help", "-h", "-?"]
    then putStrLn argumentDescription
    else do
      cfg <- liftErr $ argumentParser args
      input <- getContents
      spec <- parseTSL input
      game <- tslToRPG cfg spec
      putStrLn $ printRPG game
