{-# LANGUAGE LambdaCase #-}

module Issy.Parsers.SExpression
  ( parse
  , SExpr(..)
  , Pos(..)
  , getPos
  , perr
  , PRes
  ) where

import Data.Bifunctor (first)

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
  | TNum Pos String
  deriving (Eq, Ord, Show)

getPosT :: Token -> Pos
getPosT =
  \case
    TLPar p -> p
    TRPar p -> p
    TId p _ -> p
    TNum p _ -> p

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

digits :: [Char]
digits = ['0' .. '9']

idStarts :: [Char]
idStarts = ['a' .. 'z'] ++ ['A' .. 'Z']

idSymbols :: [Char]
idSymbols = idStarts ++ digits ++ ['\'', '_']

tokenize :: String -> PRes [Token]
tokenize = go (Pos {lineNum = 1, pos = 1})
  where
    go p =
      \case
        [] -> Right []
        ';':sr -> go (nextLine p) $ drop 1 $ dropWhile (/= ' ') sr
        ' ':sr -> go (nextSymbol p) sr
        '\n':sr -> go (nextLine p) sr
        '(':sr -> (TLPar p :) <$> go (nextSymbol p) sr
        ')':sr -> (TRPar p :) <$> go (nextSymbol p) sr
        c:sr
          | c `elem` digits -> goWord p "" p (c : sr)
          | c `elem` idStarts -> goID p "" p (c : sr)
          | otherwise -> perr p $ "Found illegal character '" ++ [c] ++ "'"
    goWord sp acc p =
      \case
        [] -> Right [TNum sp (reverse acc)]
        c:sr
          | c `elem` terminators -> (TNum sp (reverse acc) :) <$> go p (c : sr)
          | c `elem` digits ++ ['.'] -> goWord sp (c : acc) (nextSymbol p) sr
          | otherwise -> perr p $ "Found illegal character '" ++ [c] ++ "' in number"
    goID sp acc p =
      \case
        [] -> Right [TId sp (reverse acc)]
        c:sr
          | c `elem` terminators -> (TId sp (reverse acc) :) <$> go p (c : sr)
          | c `elem` idSymbols -> goID sp (c : acc) (nextSymbol p) sr
          | otherwise -> perr p $ "Found illegal character '" ++ [c] ++ "' in identifier"

data SExpr
  = SId Pos String
  | SNum Pos String
  | SPar Pos [SExpr]
  deriving (Eq, Ord, Show)

getPos :: SExpr -> Pos
getPos =
  \case
    SId p _ -> p
    SNum p _ -> p
    SPar p _ -> p

parseSExpr :: [Token] -> PRes (SExpr, [Token])
parseSExpr =
  \case
    [] -> Left "Parser error: found EOF while parsing S-expression"
    TId p str:tr -> Right (SId p str, tr)
    TNum p num:tr -> Right (SNum p num, tr)
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
