{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Parsers.SExpression
  ( parse
  , SExpr(..)
  , Pos(..)
  , getPos
  , perr
  , PRes
  ) where

import Data.Bifunctor (first)
import Data.Char (isAscii, isPrint, ord)

data Pos = Pos
  { lineNum :: Word
  , pos :: Word
  } deriving (Eq, Ord, Show)

nextSymbol :: Pos -> Pos
nextSymbol p = p {pos = pos p + 1}

nextLine :: Pos -> Pos
nextLine p = Pos {lineNum = lineNum p + 1, pos = 1}

type PRes a = Either String a

perr :: Pos -> String -> Either String a
perr p msg = Left $ "Parser error [" ++ show (lineNum p) ++ ":" ++ show (pos p) ++ "] : " ++ msg

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

data SExpr
  = SId Pos String
  | SPar Pos [SExpr]
  deriving (Eq, Ord, Show)

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

parse :: String -> Either String SExpr
parse str = do
  tokens <- tokenize (cleanupNL str)
  (expr, rest) <- parseSExpr tokens
  case rest of
    [] -> Right expr
    t:_ -> perr (getPosT t) "Found token after parsing. Did you use multiple S-expressions?"
