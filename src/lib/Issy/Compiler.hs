---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Compiler
-- Description : Issy-format to llissy format compiler
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module is top-level module for the issy-format to llissy format compiler.
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
-- | Take an Issy-formatted string and outputs an LLissy-formatted string. It fails, if the
-- the input format does not conform to the Issy format.
compile :: String -> Either String String
compile input = do
  tokens <- tokenize input
  ast <- parse tokens
  ast <- check ast
  Right $ write ast
---------------------------------------------------------------------------------------------------
