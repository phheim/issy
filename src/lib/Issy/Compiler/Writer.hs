---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Compiler.Writer
-- Description : Writer for the issy-format to llissy-format compiler
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module prints the AST of a issy specification as a llissy formatted string. This
-- corresponds to the code-generation-phase of a more traditional compiler.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Compiler.Writer
  ( write
  ) where

---------------------------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Ratio (denominator, numerator)

import Issy.Compiler.Base

---------------------------------------------------------------------------------------------------
-- | 'write' prints the AST of an issy-specification in the llissy format
write :: AstSpec -> String
write spec =
  let defs = getDefs spec
   in ps [chainWs writeVar spec, chainWs (writeLogicSpec defs) spec, chainWs (writeGame defs) spec]

data Defs = Defs
  { vars :: Map String (AstIO, AstSort)
  , macros :: Map String AstTerm
  }

getDefs :: [AstDef] -> Defs
getDefs = go $ Defs {vars = Map.empty, macros = Map.empty}
  where
    go acc =
      \case
        [] -> acc
        AstMacro _ name term:sr -> go (acc {macros = Map.insert name term (macros acc)}) sr
        AstVar _ io sort name:sr -> go (acc {vars = Map.insert name (io, sort) (vars acc)}) sr
        _:sr -> go acc sr

writeVar :: AstDef -> Maybe String
writeVar =
  \case
    AstVar _ var sort name -> Just $ sexpr [iTs var, sTs sort, name] ++ "\n"
    _ -> Nothing
  where
    iTs AInput = "input"
    iTs AState = "state"
    sTs ABool = "Bool"
    sTs AInt = "Int"
    sTs AReal = "Real"

writeLogicSpec :: Defs -> AstDef -> Maybe String
writeLogicSpec defs =
  \case
    AstLogic _ fs -> Just $ ps [chainWs (writeAssumes defs) fs, chainWs (writeAsserts defs) fs]
    _ -> Nothing

writeGame :: Defs -> AstDef -> Maybe String
writeGame defs =
  \case
    AstGame _ wc init stm ->
      Just
        $ ps
            [ chainWs (writeLocs defs) stm
            , chainWs (writeTrans defs) stm
            , sexpr [init, writeWC wc] ++ "\n"
            ]
    _ -> Nothing

writeWC :: AstWC -> String
writeWC =
  \case
    ASafety -> "Safety"
    AReachability -> "Reachability"
    ABuechi -> "Buechi"
    ACoBuechi -> "CoBuechi"
    AParityMaxOdd -> "ParityMaxOdd"

writeAssumes :: Defs -> AstLogicStm -> Maybe String
writeAssumes defs =
  \case
    AstAssume _ f -> Just (writeFormula defs f)
    _ -> Nothing

writeAsserts :: Defs -> AstLogicStm -> Maybe String
writeAsserts defs =
  \case
    AstAssert _ f -> Just (writeFormula defs f)
    _ -> Nothing

writeLocs :: Defs -> AstGameStm -> Maybe String
writeLocs defs =
  \case
    ALoc _ name acc dom -> Just $ sexpr [name, show acc, writeTerm id defs dom]
    _ -> Nothing

writeTrans :: Defs -> AstGameStm -> Maybe String
writeTrans defs =
  \case
    ATrans _ l1 l2 delta -> Just $ sexpr [l1, l2, writeTerm id defs delta]
    _ -> Nothing

writeFormula :: Defs -> AstTF -> String
writeFormula defs =
  \case
    AFAtom _ atom -> writeAtom (\ap -> sexpr ["ap", ap]) defs atom
    AFUexp _ (UOP op) f ->
      let sop =
            case op of
              "!" -> "not"
              "F" -> "F"
              "G" -> "G"
              "X" -> "X"
              _ -> error "assert: this should have been already checked!"
       in sexpr [sop, writeFormula defs f]
    AFBexp _ (BOP op) f1 f2 ->
      let s1 = writeFormula defs f1
          s2 = writeFormula defs f2
          mk ops = sexpr [ops, s1, s2]
       in case op of
            "&&" -> mk "and"
            "||" -> mk "or"
            "U" -> mk "U"
            "W" -> mk "W"
            "R" -> mk "R"
            "->" -> sexpr ["or", sexpr ["not", s1], s2]
            "<->" ->
              sexpr
                ["and", sexpr ["or", sexpr ["not", s1], s2], sexpr ["or", sexpr ["not", s2], s1]]
            _ -> error "assert: this should have been already checked!"

writeTerm :: (String -> String) -> Defs -> AstTerm -> String
writeTerm pref defs =
  \case
    ATAtom _ atom -> writeAtom pref defs atom
    ATUexp _ (UOP "!") t -> sexpr ["not", writeTerm pref defs t]
    ATUexp {} -> error "assert: this should have been already checked!"
    ATBexp _ (BOP op) t1 t2 ->
      let s1 = writeTerm pref defs t1
          s2 = writeTerm pref defs t2
          mk ops = sexpr [ops, s1, s2]
       in case op of
            "&&" -> mk "and"
            "||" -> mk "or"
            "->" -> mk "=>"
            "<->" -> sexpr ["and", sexpr ["=>", s1, s2], sexpr ["=>", s1, s2]]
            _ -> error "assert: this should have been already checked!"

writeAtom :: (String -> String) -> Defs -> AstAtom -> String
writeAtom pref defs =
  \case
    AAGround _ pred -> pref $ writeGround defs pred
    AABool _ True -> "true"
    AABool _ False -> "false"
    AAVar _ name ->
      case macros defs !? name of
        Nothing -> pref $ changeName name
        Just t -> writeTerm pref (defs {macros = Map.delete name (macros defs)}) t
    AAKeep pos ids -> writeTerm pref defs $ keepTerm pos ids
    AAHavoc pos ids ->
      writeTerm pref defs
        $ keepTerm pos
        $ filter (`notElem` ids)
        $ Map.keys
        $ Map.filter ((== AState) . fst)
        $ vars defs

keepTerm :: Pos -> [String] -> AstTerm
keepTerm pos =
  \case
    [] -> ATAtom pos $ AABool pos True
    [x] -> keepVar x
    x:xr -> ATBexp pos (BOP "&&") (keepVar x) (keepTerm pos xr)
  where
    keepVar x =
      ATAtom pos $ AAGround pos $ AGBexp pos (BOP "=") (AGVar pos x) (AGVar pos (x ++ "'"))

writeGround :: Defs -> AstGround -> String
writeGround defs =
  \case
    AConstBool _ b
      | b -> "true"
      | otherwise -> "false"
    AConstInt _ n -> show n
    AConstReal _ n -> sexpr ["/", show (numerator n), show (denominator n)]
    AGVar _ name ->
      case macros defs !? name of
        Just (ATAtom _ (AAGround _ pred)) ->
          writeGround (defs {macros = Map.delete name (macros defs)}) pred
        _ -> changeName name
    AGUexp _ (UOP "-") t -> sexpr ["-", "0", writeGround defs t]
    AGUexp _ (UOP "abs") t -> sexpr ["abs", writeGround defs t]
    AGUexp _ (UOP "!") t -> sexpr ["not", writeGround defs t]
    AGUexp {} -> error "assert: this should have been already checked!"
    AGBexp _ (BOP op) t1 t2
      | op == "&&" -> sexpr ["and", writeGround defs t1, writeGround defs t2]
      | op == "||" -> sexpr ["or", writeGround defs t1, writeGround defs t2]
      | op `elem` [">", "<", "=", "<=", ">=", "+", "-", "*", "/", "mod"] ->
        sexpr [op, writeGround defs t1, writeGround defs t2]
      | otherwise -> error "assert: this should have been already checked!"

changeName :: String -> String
changeName =
  map $ \c ->
    if c == '\''
      then '~'
      else c

--
-- Helpers
--
chainWs :: (a -> Maybe String) -> [a] -> String
chainWs f = ps . mapMaybe f

sexpr :: [String] -> String
sexpr =
  \case
    [] -> "()"
    s:sr -> "(" ++ s ++ concatMap (" " ++) sr ++ ")"

ps :: [String] -> String
ps subs =
  case subs of
    [] -> "()\n"
    es -> "(\n" ++ indent (concat es) ++ ")\n"

indent :: String -> String
indent = unlines . map ("  " ++) . lines
---------------------------------------------------------------------------------------------------
