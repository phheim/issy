module Main where

import Issy (argumentParser, fromRPG, parseRPG, solve)

import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case argumentParser args of
    Left err -> fail err
    Right cfg -> do
      input <- getContents
      case parseRPG input of
        Left err -> fail err
        Right (game, wc) -> solve cfg (fromRPG game) wc
