--
-- Update := "(" ("(" ID TERM ")")* ")" ID
--
-- Transition := "if" Formula "then" Transition "else" Transition
--             | "sys" "(" Update+ ")"
--             | Location
--
--
-- GameItem :=
--     "input" ID SORT
--   | "output" ID SORT
--   | "init" ID
--   | "type" WC
--   | "loc" ID RANK 
--   | "trans" ID Transition 
--
--  GameDescipition := GameItem*
--
{-# LANGUAGE LambdaCase #-}

module Issy.Parsers.RPG
  ( parseRPG
  ) where

import Data.Map.Strict (Map, (!), (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Read (readMaybe)

import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import Issy.Logic.FOL (Sort(..), Symbol, Term, quantifierFree)
import Issy.Parsers.SMTLib (parseTerm, sortValue)
import Issy.Parsers.SMTLibLexer (Token(..), tokenize)
import Issy.RPG

type PRes a = Either String a

perr :: String -> String -> PRes a
perr func msg = Left ("GameParser." ++ func ++ ": " ++ msg)

data PState = PState
  { wcPS :: Maybe WinningCondition
  , rankP :: Map Loc Word
  , namesL :: Map String Loc
  , setInit :: Maybe Loc
  }

uniqueFirsts :: Ord a => [(a, b)] -> Bool
uniqueFirsts fs = length fs == Set.size (Set.fromList (map fst fs))

pList :: ([Token] -> PRes (a, [Token])) -> [Token] -> PRes ([a], [Token])
pList pelem =
  \case
    TLPar:tr -> pList' tr
    _ -> perr "pList" "Expected opening ')'"
  where
    pList' =
      \case
        [] -> perr "pList" "Expected closing ')' but found EOF"
        TRPar:tr -> Right ([], tr)
        ts -> do
          (e, tr) <- pelem ts
          (er, tr') <- pList' tr
          Right (e : er, tr')

pExpect :: String -> String -> [Token] -> PRes [Token]
pExpect nm str =
  \case
    TId n:tr
      | n == str -> Right tr
      | otherwise -> perr nm ("Expected '" ++ str ++ "' found '" ++ n ++ "'")
    [] -> perr nm ("Expected '" ++ str ++ "' found EOF")
    TLPar:_ -> perr nm ("Expected '" ++ str ++ "' found '(' ")
    TRPar:_ -> perr nm ("Expected '" ++ str ++ "' found '(' ")

pUpd :: Game -> [Token] -> PRes ((Symbol, Term), [Token])
pUpd g =
  \case
    TLPar:TId n:ts ->
      if n `elem` outputs g
        then do
          (t, tr) <- parseTerm (trySortOf g) ts
          case tr of
            TRPar:tr' -> Right ((n, t), tr')
            _ -> perr "pUpd" "Expected closing ')'"
        else perr "pUpd" ("Updating '" ++ n ++ "' which is not an output")
    _ -> perr "pUpd" "Unkown pattern while parsing update found"

pSelect :: (Game, PState) -> [Token] -> PRes ((Map Symbol Term, Loc), [Token])
pSelect (g, pst) ts = do
  (upds, tr) <- pList (pUpd g) ts
  if uniqueFirsts upds
    then case tr of
           TId n:tr' ->
             case namesL pst !? n of
               Just l -> Right ((Map.fromList upds, l), tr')
               Nothing -> perr "pSelect" ("Location '" ++ n ++ "' not found")
           _ -> perr "pSelect" "Expected location identifer after update list"
    else perr "pSelect" "cells cannot be update twice"

pTrans :: (Game, PState) -> [Token] -> PRes (Transition, [Token])
pTrans (g, pst) =
  \case
    TId "if":ts -> do
      (cond, ts') <- parseTerm (trySortOf g) ts
      ts1 <- pExpect "pTrans" "then" ts'
      (thn, ts1') <- pTrans (g, pst) ts1
      ts2 <- pExpect "pTrans" "else" ts1'
      (els, tsf) <- pTrans (g, pst) ts2
      if quantifierFree cond
        then Right (TIf cond thn els, tsf)
        else perr "pTrans" "Only quantifier-free formulas are allowed"
    --
    TId "sys":ts -> do
      (choices, tr) <- pList (pSelect (g, pst)) ts
      if null choices
        then perr "pTrans" "At least one selection necessary"
        else if not (uniqueFirsts choices)
               then perr "pTrans" "Same choices are not allowed twice"
               else Right (TSys choices, tr)
    --
    TId n:ts ->
      case namesL pst !? n of
        Nothing -> perr "pTrans" ("Location '" ++ n ++ "' not found")
        Just l -> Right (TSys [(Map.empty, l)], ts)
    --
    _ -> perr "pTrans" "Unkown pattern while parsing transition"

pWC :: String -> PRes WinningCondition
pWC =
  \case
    "Buechi" -> Right (Buechi Set.empty)
    "coBuechi" -> Right (CoBuechi Set.empty)
    "Parity" -> Right (Parity Map.empty)
    "Reach" -> Right (Reachability Set.empty)
    "Safety" -> Right (Safety Set.empty)
    s -> perr "pWC" ("Unkown winning condition \"" ++ s ++ "\"")

extractPos :: Map Loc Word -> Set Loc
extractPos rank = Set.filter (\l -> (rank ! l) > 0) (Map.keysSet rank)

pAssert :: Bool -> String -> String -> PRes ()
pAssert c func msg
  | c = Right ()
  | otherwise = perr func msg

pAnnotatedType :: String -> PRes (Sort, Bool)
pAnnotatedType =
  \case
    "Bool" -> return (SBool, True)
    "BInt" -> return (SInt, True)
    "Int" -> return (SInt, False)
    "BReal" -> return (SReal, True)
    "Real" -> return (SReal, False)
    s -> perr "pAnnotatedType" ("Unkown type '" ++ s ++ "'")

pGame :: (Game, PState) -> [Token] -> PRes (Game, Objective)
pGame (g, pst) =
  \case
    [] -> do
      pAssert (all (isJust . tryTrans g) (locations g)) "pGame" "Not all locations with transition"
      case (wcPS pst, setInit pst) of
        (Nothing, _) -> perr "pGame" "Winning condition not set"
        (_, Nothing) -> perr "pGame" "Initial location not set"
        (Just w, Just init) ->
          let wc =
                case w of
                  Buechi _ -> Buechi (extractPos (rankP pst))
                  CoBuechi _ -> CoBuechi (extractPos (rankP pst))
                  Safety _ -> Safety (extractPos (rankP pst))
                  Reachability _ -> Reachability (extractPos (rankP pst))
                  Parity _ -> Parity (rankP pst)
              obj = Objective {initialLoc = init, winningCond = wc}
           in Right (g, obj)
    --
    TId "input":TId n:TId s:tr -> do
      sv <- sortValue s
      case addInput g n sv of
        Nothing -> perr "pGame" ("Input '" ++ n ++ "' already found")
        Just g' -> pGame (g', pst) tr
    --
    TId "output":TId n:TId s:tr -> do
      (sv, bound) <- pAnnotatedType s
      case addOutput g n sv bound of
        Nothing -> perr "pGame" ("Output '" ++ n ++ "' already found")
        Just g' -> pGame (g', pst) tr
    --
    TId "type":TId w:tr -> do
      wc <- pWC w
      case wcPS pst of
        Just _ -> perr "pGame" "Winning condtion already defined"
        Nothing -> pGame (g, pst {wcPS = Just wc}) tr
    --
    TId "init":TId i:tr ->
      case (setInit pst, namesL pst !? i) of
        (Just _, _) -> perr "pGame" "Initial location already set"
        (_, Nothing) -> perr "pGame" ("Initial location '" ++ i ++ "' unkown")
        (_, Just l) -> pGame (g, pst {setInit = Just l}) tr
    --
    TId "loc":TId n:TId r:tr ->
      case (namesL pst !? n, readMaybe r :: Maybe Word) of
        (Just _, _) -> perr "pGame" ("Location '" ++ n ++ "' already defined")
        (_, Nothing) -> perr "pGame" "Could not parse location rank"
        (_, Just rn) ->
          let (g', l) = addLocation g n
           in pGame
                ( g'
                , pst {rankP = Map.insert l rn (rankP pst), namesL = Map.insert n l (namesL pst)})
                tr
    --
    TId "trans":TId n:tr ->
      case namesL pst !? n of
        Nothing -> perr "pGame" ("Location '" ++ n ++ "' not found")
        Just l -> do
          (t, tr') <- pTrans (g, pst) tr
          case addTransition g l t of
            Nothing -> perr "pGame" ("Transition for location '" ++ n ++ "' already defined")
            Just g' -> pGame (g', pst) tr'
    --
    TId s:_ -> Left ("GameParser.pGame: Error parsing '" ++ s ++ "'")
    TLPar:_ -> perr "pGame" "Found '(' instead of keyword"
    TRPar:_ -> perr "pGame" "Found ')' instead of keyword"

parseRPG :: String -> Either String (Game, Objective)
parseRPG str =
  let emptyPSt = PState {wcPS = Nothing, rankP = Map.empty, namesL = Map.empty, setInit = Nothing}
   in pGame (emptyGame, emptyPSt) (tokenize str)
