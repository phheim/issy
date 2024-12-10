{-# LANGUAGE LambdaCase #-}

module Compiler.Parser
  ( parse
  ) where

import Control.Monad (unless, when)
import Data.Bifunctor (second)
import Data.Ratio ((%))
import Text.Read (readMaybe)

import Compiler.Base
import Compiler.Lexer

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
    "input" -> apply2 (AstVar AInput) $ parseVar ts
    "state" -> apply2 (AstVar AState) $ parseVar ts
    "logic" -> apply1 AstLogic $ parseLogic ts
    "game" -> apply3 AstGame $ parseGame ts
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

parseLogic :: [Token] -> PRes ([AstLogicStm], [Token])
parseLogic ts = exact ts "{" >>= go
  where
    go ts = do
      (str, p, ts) <- next ts "closing }"
      case str of
        "assert" -> do
          (e, ts) <- apply1 AstAssert $ parseRPLTL ts
          apply1 (e :) $ go ts
        "assume" -> do
          (e, ts) <- apply1 AstAssume $ parseRPLTL ts
          apply1 (e :) $ go ts
        "}" -> pure ([], ts)
        _ -> expectErr p str "assert, assume, or closing }"

parseGame :: [Token] -> PRes (AstWC, String, [AstGameStm], [Token])
parseGame ts = do
  (str, p, ts) <- next ts "winning condition"
  wc <-
    if str `elem` ["Safety", "Reachability", "Buechi", "CoBuechi", "ParityMaxOdd"]
      then pure $ AstWC str
      else expectErr p str "winning condition"
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
          (e, ts) <- apply3 ALoc $ parseLoc ts
          apply1 (e :) $ go ts
        "from" -> do
          (e, ts) <- apply3 ATrans $ parseTrans ts
          apply1 (e :) $ go ts
        "}" -> pure ([], ts)
        _ -> expectErr p str "location, transition, or closing }"

parseLoc :: [Token] -> PRes (String, Integer, AstTerm, [Token])
parseLoc ts = do
  (id, p, ts) <- next ts "identifier"
  checkID p id
  (str, p) <- peak ts "}"
  (num, ts) <-
    if str `elem` ["[", "trans", "loc", "}"]
      then pure (0, ts)
      else do
        n <- parseInteger p str
        pure (n, consume ts)
  (str, _) <- peak ts "}"
  (term, ts) <-
    if str == "["
      then parseFOL ts
      else pure (AConstBool True, ts)
  pure (id, num, term, ts)

parseTrans :: [Token] -> PRes (String, String, AstTerm, [Token])
parseTrans ts = do
  (id1, p, ts) <- next ts "identifier"
  checkID p id1
  ts <- exact ts "to"
  (id2, p, ts) <- next ts "identifier"
  checkID p id2
  ts <- exact ts "with"
  (term, ts) <- parseFOL ts
  pure (id1, id2, term, ts)

--
-- Parse basics
--
check :: (String -> Bool) -> String -> Pos -> String -> PRes ()
check pred name p id = unless (pred id) $ perr p $ "Found illegal " ++ name ++ " \"" ++ id ++ "\""

checkID :: Pos -> String -> PRes ()
checkID = check isProperID "identifier"

isProperID :: String -> Bool
isProperID =
  \case
    [] -> False
    c:s ->
      (c `elem` ['a' .. 'z'] ++ ['A' .. 'Z'])
        && all (`elem` ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ ['_']) s

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
    ((== "(") . tval, (== ")") . tval)
    (\t ts ->
       case tval t of
         "true" -> pure (LBConst True, ts)
         "false" -> pure (LBConst False, ts)
         _ -> apply1 LAp (parseFOL (t : ts)))
    (\t ->
       if tval t `elem` ["!", "X", "G", "F"]
         then Just (LUExpr (LUOp (tval t)), 12)
         else Nothing)
    (\t ->
       let op = LBExpr (LBOp (tval t))
        in case tval t of
             "&&" -> Just (op, 10, 11)
             "||" -> Just (op, 8, 9)
             "->" -> Just (op, 7, 6)
             "<->" -> Just (op, 7, 6)
             "W" -> Just (op, 5, 4)
             "U" -> Just (op, 3, 2)
             "R" -> Just (op, 0, 1)
             _ -> Nothing)
    -- TODO: seprate in base
    (\t ->
       "Compiler error ["
         ++ show (lineNum (tpos t))
         ++ ":"
         ++ show (pos (tpos t))
         ++ "] : Found bad token while parsing operators")
    "Compiler Error : Found EOF while parsing primary operators"

-- TODO Move to own module!
parseOps ::
     (Eq t)
  => (t -> Bool, t -> Bool)
  -> (t -> [t] -> PRes (e, [t]))
  -> (t -> Maybe (e -> e, Word))
  -> (t -> Maybe (e -> e -> e, Word, Word))
  -> (t -> String)
  -> String
  -> [t]
  -> PRes (e, [t])
parseOps (lpar, rpar) parseAtom unOp binOp errToken errEOF = go
  where
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

parseFOL :: [Token] -> PRes (AstTerm, [Token])
parseFOL ts = do
  ts <- exact ts "["
  (t, ts) <- parseTerm ts
  ts <- exact ts "]"
  pure (t, ts)

parseTerm :: [Token] -> PRes (AstTerm, [Token])
parseTerm =
  parseOps
    ((== "(") . tval, (== ")") . tval)
    (\t ts ->
       case tval t of
         "true" -> pure (AConstBool True, ts)
         "false" -> pure (AConstBool False, ts)
         name ->
           case parseInteger (tpos t) name of
             Right n -> pure (AConstInt n, ts)
             _ ->
               case parseRat (tpos t) name of
                 Right n -> pure (AConstReal n, ts)
                 _ -> do
                   check isId name (tpos t) "identifier"
                   pure (ATermVar name, ts))
    (\t ->
       let op = ATUexpr (TUP (tval t))
        in case tval t of
             "!" -> Just (op, 8)
             "-" -> Just (op, 16)
             "abs" -> Just (op, 17)
             _ -> Nothing)
    (\t ->
       let op = ATBexpr (TBOP (tval t))
        in case tval t of
             "<->" -> Just (op, 1, 0)
             "->" -> Just (op, 3, 2)
             "||" -> Just (op, 4, 5)
             "&&" -> Just (op, 6, 7)
             "=" -> Just (op, 8, 9)
             "<" -> Just (op, 8, 9)
             ">" -> Just (op, 8, 9)
             ">=" -> Just (op, 8, 9)
             "<=" -> Just (op, 8, 9)
             "mod" -> Just (op, 10, 11)
             "/" -> Just (op, 12, 13)
             "*" -> Just (op, 12, 13)
             "+" -> Just (op, 14, 15)
             "-" -> Just (op, 14, 15)
             _ -> Nothing)
    -- TODO: seprate in base
    (\t ->
       "Compiler error ["
         ++ show (lineNum (tpos t))
         ++ ":"
         ++ show (pos (tpos t))
         ++ "] : Found bad token while parsing operators")
    "Compiler Error : Found EOF while parsing primary operators"

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
