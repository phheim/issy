{-# LANGUAGE LambdaCase #-}

module Issy.Parsers.SMTLibLexer
  ( Token(..)
  , tokenize
  ) where

data Token
  = TLPar
  | TRPar
  | TId String
  deriving (Eq, Ord, Show)

tokenize :: String -> [Token]
tokenize =
  \case
    [] -> []
    ';':tr -> slComment tr
    ' ':tr -> tokenize tr
    '\n':tr -> tokenize tr
    '\r':tr -> tokenize tr
    '\t':tr -> tokenize tr
    '(':tr -> TLPar : tokenize tr
    ')':tr -> TRPar : tokenize tr
    cs -> tokenizeID "" cs
  where
    tokenizeID :: String -> String -> [Token]
    tokenizeID ident =
      \case
        [] -> [TId (reverse ident)]
        c:s
          | c `elem` [' ', '\n', '\t', '\r', ')', '('] -> TId (reverse ident) : tokenize (c : s)
          | otherwise -> tokenizeID (c : ident) s
    --
    slComment :: String -> [Token]
    slComment =
      \case
        [] -> []
        '\n':s -> tokenize s
        _:s -> slComment s
