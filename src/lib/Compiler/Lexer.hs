{-# LANGUAGE LambdaCase #-}

module Compiler.Lexer
  ( tokenize
  ) where

import Compiler.Base

tokenize :: String -> PRes [Token]
tokenize = lexer initPos . cleanup

cleanup :: String -> String
cleanup =
  \case
    [] -> []
    '\n':'\r':sr -> '\n' : cleanup sr
    '\r':'\n':sr -> '\n' : cleanup sr
    '\r':sr -> '\n' : cleanup sr
    '\t':sr -> ' ' : cleanup sr
    c:sr -> c : cleanup sr

operatorChar :: [Char]
operatorChar = "|&!+-*/=<>"

digit :: [Char]
digit = ['0' .. '9']

alpha :: [Char]
alpha = ['a' .. 'z'] ++ ['A' .. 'Z']

idChar :: [Char]
idChar = alpha ++ digit ++ ['\''] ++ ['_']

numChar :: [Char]
numChar = digit ++ ['.']

single :: [Char]
single = "()[]{}"

lexer :: Pos -> String -> PRes [Token]
lexer p =
  \case
    [] -> pure []
    '/':'/':s -> lexSLComment p ('/' : '/' : s)
    '/':'*':s -> lexMLComment p p ('/' : '*' : s)
    ' ':s -> lexer (nextSymbol p) s
    '\n':s -> lexer (nextLine p) s
    c:s
      | c `elem` operatorChar -> lexFor (`elem` operatorChar) "" p (c : s)
      | c `elem` alpha -> lexFor (`elem` idChar) "" p (c : s)
      | c `elem` digit -> lexFor (`elem` numChar) "" p (c : s)
      | c `elem` single -> (token p [c] :) <$> lexer (nextSymbol p) s
      | otherwise -> perr p $ "Found illegal character '" ++ [c] ++ "'"

lexFor :: (Char -> Bool) -> String -> Pos -> String -> PRes [Token]
lexFor pred acc p =
  \case
    [] -> pure [token p (reverse acc)]
    c:s
      | pred c -> lexFor pred (c : acc) (nextSymbol p) s
      | otherwise -> (token p (reverse acc) :) <$> lexer p (c : s)

lexSLComment :: Pos -> String -> PRes [Token]
lexSLComment p =
  \case
    [] -> pure []
    '\n':sr -> lexer (nextLine p) sr
    _:sr -> lexSLComment (nextSymbol p) sr

lexMLComment :: Pos -> Pos -> String -> PRes [Token]
lexMLComment q p =
  \case
    [] -> perr q "expected matching closing commment but found EOF"
    '*':'/':sr -> lexer (nextSymbol (nextSymbol p)) sr
    '\n':sr -> lexMLComment q (nextLine p) sr
    _:sr -> lexMLComment q (nextSymbol p) sr
