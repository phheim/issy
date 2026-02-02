---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Compiler
-- Description : Top-level module of the issy's tool issy-format to lissy format compiler
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- TODO DOCUMENT
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Compiler
  ( compile
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Compiler.Checker (check)
import Issy.Compiler.Lexer (tokenize)
import Issy.Compiler.Parser (parse)
import Issy.Compiler.Writer (write)

---------------------------------------------------------------------------------------------------
-- | 'compile' takes an issy-formated string and outputs an lissy-formated string. It fail if the
-- the input format does not conform to the lissy format.
compile :: String -> Either String String
compile input = do
  tokens <- tokenize input
  ast <- parse tokens
  ast <- check ast
  Right $ write ast
---------------------------------------------------------------------------------------------------
