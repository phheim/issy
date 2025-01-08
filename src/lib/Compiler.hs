module Compiler
  ( compile
  ) where

import Compiler.Checker (check)
import Compiler.Lexer (tokenize)
import Compiler.Parser (parse)
import Compiler.Writer (write)

compile :: String -> Either String String
compile input = do
  tokens <- tokenize input
  ast <- parse tokens
  check ast
  Right $ write ast
