---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy
-- Description : Top-level module of the issy's tool issy-format to lissy format compiler
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Compiler
  ( compile
  ) where

---------------------------------------------------------------------------------------------------
import Compiler.Checker (check)
import Compiler.Lexer (tokenize)
import Compiler.Parser (parse)
import Compiler.Writer (write)

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
