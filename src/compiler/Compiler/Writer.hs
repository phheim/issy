{-# LANGUAGE LambdaCase #-}

module Compiler.Writer
  ( write
  ) where

import Data.Maybe (mapMaybe)
import Data.Ratio (denominator, numerator)

import Compiler.Base

write :: AstSpec -> String
write spec = ps [chainWs writeVar spec, chainWs writeLogicSpec spec, chainWs writeGame spec]

writeVar :: AstDef -> Maybe String
writeVar =
  \case
    AstVar var sort name -> Just $ sexpr [iTs var, sTs sort, name] ++ "\n"
    _ -> Nothing
  where
    iTs AInput = "input"
    iTs AState = "state"
    sTs ABool = "Bool"
    sTs AInt = "Int"
    sTs AReal = "Real"

writeLogicSpec :: AstDef -> Maybe String
writeLogicSpec =
  \case
    AstLogic fs -> Just $ ps [chainWs writeAssumes fs, chainWs writeAsserts fs]
    _ -> Nothing

writeGame :: AstDef -> Maybe String
writeGame =
  \case
    AstGame (AstWC wc) init stm ->
      Just $ ps [chainWs writeLocs stm, chainWs writeTrans stm, sexpr [init, wc] ++ "\n"]
    _ -> Nothing

writeAssumes :: AstLogicStm -> Maybe String
writeAssumes =
  \case
    AstAssume f -> Just (writeFormula f)
    _ -> Nothing

writeAsserts :: AstLogicStm -> Maybe String
writeAsserts =
  \case
    AstAssert f -> Just (writeFormula f)
    _ -> Nothing

writeLocs :: AstGameStm -> Maybe String
writeLocs =
  \case
    ALoc name acc dom -> Just $ sexpr [name, show acc, writeTerm dom]
    _ -> Nothing

writeTrans :: AstGameStm -> Maybe String
writeTrans =
  \case
    ATrans l1 l2 delta -> Just $ sexpr [l1, l2, writeTerm delta]
    _ -> Nothing

writeFormula :: AstTF -> String
writeFormula =
  \case
    LAp term -> sexpr ["ap", writeTerm term]
    LBConst True -> "true"
    LBConst False -> "false"
    LUExpr (LUOp op) f ->
      let sop =
            case op of
              "!" -> "not"
              "F" -> "F"
              "G" -> "G"
              "X" -> "X"
              _ -> error "assert: this should have been already checked!"
       in sexpr [sop, writeFormula f]
    LBExpr (LBOp op) f1 f2 ->
      let s1 = writeFormula f1
          s2 = writeFormula f2
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

writeTerm :: AstTerm -> String
writeTerm =
  \case
    AConstBool True -> "true"
    AConstBool False -> "false"
    AConstInt n -> show n
    AConstReal n -> sexpr [show (numerator n), "/", show (denominator n)]
    ATermVar name -> changeName name
    ATBexpr (TBOP op) t1 t2 ->
      let s1 = writeTerm t1
          s2 = writeTerm t2
          mk ops = sexpr [ops, s1, s2]
       in case op of
            "&&" -> mk "and"
            "||" -> mk "or"
            "->" -> mk "=>"
            "<->" -> sexpr ["and", sexpr ["=>", s1, s2], sexpr ["=>", s1, s2]]
            op
              | op `elem` [">", "<", "=", "<=", ">=", "+", "-", "*", "/", "mod"] -> mk op
              | otherwise -> error "assert: this should have been already checked!"
    ATUexpr (TUP op) t ->
      let s = writeTerm t
       in case op of
            "!" -> sexpr ["not", s]
            "-" -> sexpr ["-", "0", s]
            "abs" -> sexpr ["abs", s]
            _ -> error "assert: this should have been already checked!"

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
