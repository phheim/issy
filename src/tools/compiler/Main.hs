{-# LANGUAGE LambdaCase #-}

module Main
  ( main
  ) where

import System.Exit (die)

import Compiler (compile)

main :: IO ()
main = do
  input <- getContents
  case compile input of
    Left err -> die err
    Right res -> putStrLn res
