---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Parsers.SExpression
-- Description : S-expression parser
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements a generic parser for s-expressions with SMTLib/Lisp like '; 'comments.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Parsers.SExpression
  ( SExpr(..)
  , Pos(..)
  , PRes
  , parse
  , getPos
  , perr
  ) where

---------------------------------------------------------------------------------------------------
import Data.Bifunctor (first)
import Data.Char (isAscii, isPrint, ord)

---------------------------------------------------------------------------------------------------
-- | Representation of a position in a parsed file or string.
data Pos = Pos
  { lineNum :: Word
  -- ^ the line number in the string, starting from one
  , pos :: Word
  -- ^ the column within a line, starting from one
  } deriving (Eq, Ord, Show)

nextSymbol :: Pos -> Pos
nextSymbol p = p {pos = pos p + 1}

nextLine :: Pos -> Pos
nextLine p = Pos {lineNum = lineNum p + 1, pos = 1}

---------------------------------------------------------------------------------------------------
-- | Representation of a generic parser result.
type PRes a = Either String a

-- | Create an parser error at a given position with an error message.
perr :: Pos -> String -> Either String a
perr p msg = Left $ "Parser error [" ++ show (lineNum p) ++ ":" ++ show (pos p) ++ "] : " ++ msg

---------------------------------------------------------------------------------------------------
data Token
  = TLPar Pos
  | TRPar Pos
  | TId Pos String
  deriving (Eq, Ord, Show)

getPosT :: Token -> Pos
getPosT =
  \case
    TLPar p -> p
    TRPar p -> p
    TId p _ -> p

cleanupNL :: String -> String
cleanupNL =
  \case
    [] -> []
    '\n':'\r':sr -> '\n' : cleanupNL sr
    '\r':'\n':sr -> '\n' : cleanupNL sr
    '\r':sr -> '\n' : cleanupNL sr
    '\t':sr -> ' ' : cleanupNL sr
    c:sr -> c : cleanupNL sr

terminators :: [Char]
terminators = [')', '(', ' ', ';', '\n']

tokenize :: String -> PRes [Token]
tokenize = go (Pos {lineNum = 1, pos = 1})
  where
    go p =
      \case
        [] -> Right []
        ';':sr -> go (nextLine p) $ drop 1 $ dropWhile (/= '\n') sr
        ' ':sr -> go (nextSymbol p) sr
        '\n':sr -> go (nextLine p) sr
        '(':sr -> (TLPar p :) <$> go (nextSymbol p) sr
        ')':sr -> (TRPar p :) <$> go (nextSymbol p) sr
        s -> goID p "" p s
    goID sp acc p =
      \case
        [] -> Right [TId sp (reverse acc)]
        c:sr
          | c `elem` terminators -> (TId sp (reverse acc) :) <$> go p (c : sr)
          | isAscii c && isPrint c -> goID sp (c : acc) (nextSymbol p) sr
          | otherwise -> perr p $ "Found illegal character '" ++ [c] ++ "' (" ++ show (ord c) ++ ")"

---------------------------------------------------------------------------------------------------
-- | Tree representation of a parsed s-expression.
data SExpr
  = SId Pos String
  -- ^ leafs of the tree are the identifiers/names in the expression
  | SPar Pos [SExpr]
  -- ^ inner nodes are just list of s-expressions
  deriving (Eq, Ord, Show)

-- | Return the position of an s-expression in the parsed input. For
-- a identifier this is the start of the identifier string and for
-- a list the opening parenthesis.
getPos :: SExpr -> Pos
getPos =
  \case
    SId p _ -> p
    SPar p _ -> p

parseSExpr :: [Token] -> PRes (SExpr, [Token])
parseSExpr =
  \case
    [] -> Left "Parser error: found EOF while parsing S-expression"
    TId p str:tr -> Right (SId p str, tr)
    TLPar p:tr -> do
      (es, tr) <- parseSExprs tr
      case tr of
        [] -> perr p "Did not find matching closing bracket ')'"
        TRPar _:tr -> Right (SPar p es, tr)
        _ -> error "assert: unreachable code"
    TRPar p:_ -> perr p "Closing ')' found without respective opening '('"

parseSExprs :: [Token] -> PRes ([SExpr], [Token])
parseSExprs =
  \case
    [] -> Right ([], [])
    TRPar p:tr -> Right ([], TRPar p : tr)
    ts -> do
      (e, ts) <- parseSExpr ts
      first (e :) <$> parseSExprs ts

---------------------------------------------------------------------------------------------------
-- | Parse a single s-expression.
parse :: String -> Either String SExpr
parse str = do
  tokens <- tokenize (cleanupNL str)
  (expr, rest) <- parseSExpr tokens
  case rest of
    [] -> Right expr
    t:_ -> perr (getPosT t) "Found token after parsing. Did you use multiple S-expressions?"
---------------------------------------------------------------------------------------------------
