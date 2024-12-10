{-# LANGUAGE LambdaCase #-}

module Main
  ( main
  ) where

import System.Exit (die)

import Compiler.Checker (check)
import Compiler.Lexer (tokenize)
import Compiler.Parser (parse)
import Compiler.Writer (write)

stopErr :: Either String a -> IO a
stopErr =
  \case
    Left err -> die err
    Right a -> pure a

main :: IO ()
main = do
  input <- getContents
  tokens <- stopErr $ tokenize input
  ast <- stopErr $ parse tokens
  _ <- stopErr $ check ast
  putStrLn (write ast)
