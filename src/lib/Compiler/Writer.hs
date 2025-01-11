{-# LANGUAGE LambdaCase #-}

module Compiler.Writer
  ( write
  ) where

import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Ratio (denominator, numerator)

import Compiler.Base

write :: AstSpec -> String
write spec =
  let defs = getDefs spec
   in ps [chainWs writeVar spec, chainWs (writeLogicSpec defs) spec, chainWs (writeGame defs) spec]

type Defs = Map String AstTerm

getDefs :: [AstDef] -> Defs
getDefs = go Map.empty
  where
    go acc =
      \case
        [] -> acc
        AstDef name term:sr -> go (Map.insert name term acc) sr
        _:sr -> go acc sr

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

writeLogicSpec :: Defs -> AstDef -> Maybe String
writeLogicSpec defs =
  \case
    AstLogic fs -> Just $ ps [chainWs (writeAssumes defs) fs, chainWs (writeAsserts defs) fs]
    _ -> Nothing

writeGame :: Defs -> AstDef -> Maybe String
writeGame defs =
  \case
    AstGame (AstWC wc) init stm ->
      Just
        $ ps [chainWs (writeLocs defs) stm, chainWs (writeTrans defs) stm, sexpr [init, wc] ++ "\n"]
    _ -> Nothing

writeAssumes :: Defs -> AstLogicStm -> Maybe String
writeAssumes defs =
  \case
    AstAssume f -> Just (writeFormula defs f)
    _ -> Nothing

writeAsserts :: Defs -> AstLogicStm -> Maybe String
writeAsserts defs =
  \case
    AstAssert f -> Just (writeFormula defs f)
    _ -> Nothing

writeLocs :: Defs -> AstGameStm -> Maybe String
writeLocs defs =
  \case
    ALoc name acc dom -> Just $ sexpr [name, show acc, writeTerm defs dom]
    _ -> Nothing

writeTrans :: Defs -> AstGameStm -> Maybe String
writeTrans defs =
  \case
    ATrans l1 l2 delta -> Just $ sexpr [l1, l2, writeTerm defs delta]
    _ -> Nothing

writeFormula :: Defs -> AstTF -> String
writeFormula defs =
  \case
    AFAtom atom -> writeAtom (\ap -> sexpr ["ap", ap]) defs atom
    AFUexp (UOP op) f ->
      let sop =
            case op of
              "!" -> "not"
              "F" -> "F"
              "G" -> "G"
              "X" -> "X"
              _ -> error "assert: this should have been already checked!"
       in sexpr [sop, writeFormula defs f]
    AFBexp (BOP op) f1 f2 ->
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

writeTerm :: Defs -> AstTerm -> String
writeTerm defs =
  \case
    ATAtom atom -> writeAtom id defs atom
    ATUexp (UOP "!") t -> sexpr ["not", writeTerm defs t]
    ATUexp _ _ -> error "assert: this should have been already checked!"
    ATBexp (BOP op) t1 t2 ->
      let s1 = writeTerm defs t1
          s2 = writeTerm defs t2
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
    AAGround pred -> pref $ writeGround defs pred
    AABool True -> "true"
    AABool False -> "false"
    AAVar name ->
      case defs !? name of
        Nothing -> pref $ changeName name
        Just t -> writeTerm (Map.delete name defs) t

writeGround :: Defs -> AstGround -> String
writeGround defs =
  \case
    AConstInt n -> show n
    AConstReal n -> sexpr [show (numerator n), "/", show (denominator n)]
    AGVar name ->
      case defs !? name of
        Just (ATAtom (AAGround pred)) -> writeGround (Map.delete name defs) pred
        _ -> changeName name
    AGUexp (UOP "-") t -> sexpr ["-", "0", writeGround defs t]
    AGUexp (UOP "abs") t -> sexpr ["abs", writeGround defs t]
    AGUexp _ _ -> error "assert: this should have been already checked!"
    AGBexp (BOP op) t1 t2
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
