---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Compiler.Parser
-- Description : Parser for the issy-format to llissy-format compiler
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module contains the parser for the issy-to-llissy compiler.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Compiler.Parser
  ( parse
  ) where

---------------------------------------------------------------------------------------------------
import Control.Monad (unless, when)
import Data.Bifunctor (second)
import Data.Ratio ((%))
import Text.Read (readMaybe)

import Issy.Compiler.Base
  ( AstAtom(..)
  , AstDef(..)
  , AstGameStm(..)
  , AstGround(..)
  , AstIO(..)
  , AstLogicStm(..)
  , AstSort(..)
  , AstSpec
  , AstTF(..)
  , AstTerm(..)
  , AstWC(..)
  , BOP(..)
  , PRes
  , Pos
  , Token(..)
  , UOP(..)
  , perr
  , perrGen
  , posStr
  )

---------------------------------------------------------------------------------------------------
-- | 'parse' turns a (linear) list of tokens into the tree shaped AST of a lissy specification
parse :: [Token] -> PRes AstSpec
parse = fmap fst . parseSpec

parseSpec :: [Token] -> PRes (AstSpec, [Token])
parseSpec =
  \case
    [] -> pure ([], [])
    ts -> do
      (e, ts) <- parseDef ts
      (es, ts) <- parseSpec ts
      pure (e : es, ts)

parseDef :: [Token] -> PRes (AstDef, [Token])
parseDef ts = do
  (str, p, ts) <- next ts "specification definition"
  case str of
    "input" -> apply2 (AstVar p AInput) $ parseVar ts
    "state" -> apply2 (AstVar p AState) $ parseVar ts
    "formula" -> apply1 (AstLogic p) $ parseLogic ts
    "game" -> apply3 (AstGame p) $ parseGame ts
    "def" -> apply2 (AstMacro p) $ parseMacro ts
    _ -> expectErr p str "specification definition"

parseVar :: [Token] -> PRes (AstSort, String, [Token])
parseVar ts = do
  (str, p, ts) <- next ts "variable type"
  sort <-
    case str of
      "int" -> pure AInt
      "real" -> pure AReal
      "bool" -> pure ABool
      _ -> expectErr p str "variables type"
  (id, p, ts) <- next ts "identifier"
  checkID p id
  pure (sort, id, ts)

parseMacro :: [Token] -> PRes (String, AstTerm, [Token])
parseMacro ts = do
  (id, p, ts) <- next ts "identifier"
  checkID p id
  ts <- exact ts "="
  (term, ts) <- parseTerm ts
  pure (id, term, ts)

parseLogic :: [Token] -> PRes ([AstLogicStm], [Token])
parseLogic ts = exact ts "{" >>= go
  where
    go ts = do
      (str, p, ts) <- next ts "closing }"
      case str of
        "assert" -> do
          (e, ts) <- apply1 (AstAssert p) $ parseRPLTL ts
          apply1 (e :) $ go ts
        "assume" -> do
          (e, ts) <- apply1 (AstAssume p) $ parseRPLTL ts
          apply1 (e :) $ go ts
        "}" -> pure ([], ts)
        _ -> expectErr p str "assert, assume, or closing }"

parseGame :: [Token] -> PRes (AstWC, String, [AstGameStm], [Token])
parseGame ts = do
  (str, p, ts) <- next ts "winning condition"
  wc <-
    case str of
      "Safety" -> Right ASafety
      "Reachability" -> Right AReachability
      "Buechi" -> Right ABuechi
      "CoBuechi" -> Right ACoBuechi
      "ParityMaxOdd" -> Right AParityMaxOdd
      _ -> expectErr p str "winning condition"
  ts <- exact ts "from"
  (id, p, ts) <- next ts "identifier"
  checkID p id
  ts <- exact ts "{"
  (defs, ts) <- go ts
  pure (wc, id, defs, ts)
  where
    go ts = do
      (str, p, ts) <- next ts "\"}\""
      case str of
        "loc" -> do
          (e, ts) <- apply3 (ALoc p) $ parseLoc ts
          apply1 (e :) $ go ts
        "from" -> do
          (e, ts) <- apply3 (ATrans p) $ parseTrans ts
          apply1 (e :) $ go ts
        "}" -> pure ([], ts)
        _ -> expectErr p str "location, transition, or closing }"

parseLoc :: [Token] -> PRes (String, Integer, AstTerm, [Token])
parseLoc ts = do
  (id, pId, ts) <- next ts "identifier"
  checkID pId id
  (str, p) <- peak ts "}"
  (num, ts) <-
    if str `elem` ["trans", "loc", "}", "with"]
      then pure (0, ts)
      else do
        n <- parseInteger p str
        pure (n, consume ts)
  (str, _) <- peak ts "}"
  (term, ts) <-
    if str == "with"
      then parseTerm (consume ts)
      else pure (ATAtom pId (AABool pId True), ts)
  pure (id, num, term, ts)

parseTrans :: [Token] -> PRes (String, String, AstTerm, [Token])
parseTrans ts = do
  (id1, p, ts) <- next ts "identifier"
  checkID p id1
  ts <- exact ts "to"
  (id2, p, ts) <- next ts "identifier"
  checkID p id2
  ts <- exact ts "with"
  (term, ts) <- parseTerm ts
  pure (id1, id2, term, ts)

--
-- Parse basics
--
check :: (String -> Bool) -> String -> Pos -> String -> PRes ()
check pred name p id = unless (pred id) $ perr p $ "Found illegal " ++ name ++ " \"" ++ id ++ "\""

checkID :: Pos -> String -> PRes ()
checkID = check isProperID "identifier"

isKeyword :: String -> Bool
isKeyword =
  flip
    elem
    [ "assume"
    , "assert"
    , "input"
    , "state"
    , "loc"
    , "from"
    , "with"
    , "game"
    , "formula"
    , "int"
    , "bool"
    , "real"
    , "def"
    , "F"
    , "X"
    , "G"
    , "U"
    , "W"
    , "R"
    , "Safety"
    , "Reachability"
    , "Buechi"
    , "CoBuechi"
    , "ParityMaxOdd"
    , "keep"
    , "havoc"
    ]

isProperID :: String -> Bool
isProperID s =
  not (isKeyword s)
    && (case s of
          [] -> False
          c:s ->
            (c `elem` ['a' .. 'z'] ++ ['A' .. 'Z'])
              && all (`elem` ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ ['_']) s)

isId :: String -> Bool
isId s =
  case reverse s of
    '\'':s -> isProperID (reverse s)
    _ -> isProperID s

parseInteger :: Pos -> String -> PRes Integer
parseInteger p str =
  case readMaybe str of
    Just n -> pure n
    Nothing -> expectErr p str "natural number"

parseRat :: Pos -> String -> PRes Rational
parseRat p str =
  let (int, frac) = second (drop 1) $ span (/= '.') str
   in (% (10 ^ (toEnum (length frac) :: Integer))) <$> parseInteger p (int ++ frac)

--
-- Parsing with prescedence
--
parseRPLTL :: [Token] -> PRes (AstTF, [Token])
parseRPLTL =
  parseOps
    pars
    (\t -> apply1 (AFAtom (tpos t)) . parseAtom t)
    (unPred UOP AFUexp [(["!", "X", "G", "F"], 12)])
    (binPred
       BOP
       AFBexp
       [ (["R"], 0, 1)
       , (["U"], 3, 2)
       , (["W"], 5, 4)
       , (["<->", "->"], 7, 6)
       , (["||"], 8, 9)
       , (["&&"], 10, 11)
       ])
    (posStr . tpos)

parseTerm :: [Token] -> PRes (AstTerm, [Token])
parseTerm =
  parseOps
    pars
    (\t -> apply1 (ATAtom (tpos t)) . parseAtom t)
    (unPred UOP ATUexp [(["!"], 8)])
    (binPred BOP ATBexp [(["<->"], 1, 0), (["->"], 3, 2), (["||"], 4, 5), (["&&"], 6, 7)])
    (posStr . tpos)

parseAtom :: Token -> [Token] -> PRes (AstAtom, [Token])
parseAtom t ts =
  case tval t of
    "true" -> pure (AABool (tpos t) True, ts)
    "false" -> pure (AABool (tpos t) False, ts)
    "[" -> apply1 (AAGround (tpos t)) $ parseGround (t : ts)
    "keep" -> do
      ts <- exact ts "("
      (ids, ts) <- getIds [] ts
      ts <- exact ts ")"
      pure (AAKeep (tpos t) ids, ts)
    "havoc" -> do
      ts <- exact ts "("
      (ids, ts) <- getIds [] ts
      ts <- exact ts ")"
      pure (AAHavoc (tpos t) ids, ts)
    name -> do
      check isId name (tpos t) "identifier"
      pure (AAVar (tpos t) name, ts)
  where
    getIds acc ts = do
      (name, _) <- peak ts ") or id"
      if isId name
        then getIds (name : acc) (consume ts)
        else pure (reverse acc, ts)

parseGround :: [Token] -> PRes (AstGround, [Token])
parseGround ts = do
  ts <- exact ts "["
  (t, ts) <- parseGroundTerm ts
  ts <- exact ts "]"
  pure (t, ts)

parseGroundTerm :: [Token] -> PRes (AstGround, [Token])
parseGroundTerm =
  parseOps
    pars
    (\t ts ->
       case tval t of
         "true" -> pure (AConstBool (tpos t) True, ts)
         "false" -> pure (AConstBool (tpos t) False, ts)
         name ->
           case parseInteger (tpos t) name of
             Right n -> pure (AConstInt (tpos t) n, ts)
             _ ->
               case parseRat (tpos t) name of
                 Right n -> pure (AConstReal (tpos t) n, ts)
                 _ -> do
                   check isId name (tpos t) "identifier"
                   pure (AGVar (tpos t) name, ts))
    (unPred UOP AGUexp [(["!"], 5), (["-"], 12), (["abs"], 13)])
    (binPred
       BOP
       AGBexp
       [ (["||"], 0, 1)
       , (["&&"], 2, 3)
       , (["=", "<", ">", ">=", "<="], 6, 7)
       , (["+", "-"], 8, 9)
       , (["mod", "/", "*"], 10, 11)
       ])
    (posStr . tpos)

pars :: (Token -> Bool, Token -> Bool)
pars = ((== "(") . tval, (== ")") . tval)

unPred ::
     (String -> o) -> (Pos -> o -> e -> e) -> [([String], Word)] -> Token -> Maybe (e -> e, Word)
unPred opParse op preds t =
  case filter ((tval t `elem`) . fst) preds of
    [] -> Nothing
    (_, p):_ -> Just (op (tpos t) (opParse (tval t)), p)

binPred ::
     (String -> o)
  -> (Pos -> o -> e -> e -> e)
  -> [([String], Word, Word)]
  -> Token
  -> Maybe (e -> e -> e, Word, Word)
binPred opParse op preds t =
  case filter (\(n, _, _) -> tval t `elem` n) preds of
    [] -> Nothing
    (_, pl, pr):_ -> Just (op (tpos t) (opParse (tval t)), pl, pr)

-- TODO Move to own module!
parseOps ::
     (Eq t)
  => (t -> Bool, t -> Bool)
  -> (t -> [t] -> PRes (e, [t]))
  -> (t -> Maybe (e -> e, Word))
  -> (t -> Maybe (e -> e -> e, Word, Word))
  -> (t -> String)
  -> [t]
  -> PRes (e, [t])
parseOps (lpar, rpar) parseAtom unOp binOp posToken = go
  where
    errEOF = "Compiler Error : Found EOF while parsing primary operators"
    errToken t = "Compiler error " ++ posToken t ++ ": Found bad token while parsing operators"
       --
    go = parseOp 0
       --
    parseOp pred ts = do
      (e, ts) <- parsePrimUn ts
      parseBin e pred ts
        --
    parsePrimUn =
      \case
        [] -> Left errEOF
        t:ts
          | lpar t -> do
            (term, ts) <- go ts
            case ts of
              [] -> Left errEOF
              t:ts
                | rpar t -> pure (term, ts)
                | otherwise -> Left $ errToken t
          | otherwise ->
            case unOp t of
              Just (op, pred) -> apply1 op $ parseOp pred ts
              Nothing -> parseAtom t ts
                   --
    parseBin e1 pred =
      \case
        [] -> pure (e1, [])
        t:ts
          | rpar t -> pure (e1, t : ts)
          | otherwise ->
            case binOp t of
              Nothing -> pure (e1, t : ts)
              Just (op, lp, rp)
                | pred > lp -> pure (e1, t : ts)
                | otherwise -> do
                  (e2, ts) <- parseOp rp ts
                  parseBin (op e1 e2) pred ts

--
-- Helpers, TODO: maybe also move partially to other module
--
peak :: [Token] -> String -> PRes (String, Pos)
peak ts msg =
  case ts of
    [] -> perrGen $ "expected " ++ msg ++ " but found EOF"
    t:_ -> pure (tval t, tpos t)

consume :: [Token] -> [Token]
consume =
  \case
    [] -> error "assert: you should not be here"
    _:ts -> ts

next :: [Token] -> String -> PRes (String, Pos, [Token])
next ts msg =
  case ts of
    [] -> perrGen $ "expected " ++ msg ++ " but found EOF"
    t:tr -> pure (tval t, tpos t, tr)

exact :: [Token] -> String -> PRes [Token]
exact ts res = do
  (str, p, ts) <- next ts $ "\"" ++ res ++ "\""
  when (str /= res) $ expectErr p str $ "\"" ++ res ++ "\""
  pure ts

expectErr :: Pos -> String -> String -> PRes a
expectErr p found exp = perr p $ "expected " ++ exp ++ " but found \"" ++ found ++ "\""

apply1 :: (a -> b) -> PRes (a, t) -> PRes (b, t)
apply1 f =
  \case
    Left err -> Left err
    Right (a, t) -> Right (f a, t)

apply2 :: (a -> b -> c) -> PRes (a, b, t) -> PRes (c, t)
apply2 f =
  \case
    Left err -> Left err
    Right (a, b, t) -> Right (f a b, t)

apply3 :: (a -> b -> c -> d) -> PRes (a, b, c, t) -> PRes (d, t)
apply3 f =
  \case
    Left err -> Left err
    Right (a, b, c, t) -> Right (f a b c, t)
