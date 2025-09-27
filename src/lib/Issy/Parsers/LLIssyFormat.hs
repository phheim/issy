{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Parsers.LLIssyFormat
  ( parseLLIssyFormat
  ) where

import Control.Monad (foldM, unless, when)
import Data.Map.Strict (Map, (!), (!?))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Text.Read (readMaybe)

import Issy.Base.Locations (Loc)
import Issy.Base.Objectives (Objective)
import qualified Issy.Base.Objectives as Obj
import Issy.Base.Variables (Type, Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Logic.FOL (Sort(..), Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.Temporal as TL
import Issy.Parsers.SExpression (PRes, Pos, SExpr(..), getPos, parse, perr)
import qualified Issy.Parsers.SMTLib as SMTLib (parseFuncName, tryParseInt, tryParseRat)
import Issy.Specification (Specification)
import qualified Issy.Specification as Spec
import Issy.SymbolicArena (Arena)
import qualified Issy.SymbolicArena as SG

--
-- Main method
--
parseLLIssyFormat :: String -> Either String Specification
parseLLIssyFormat input = do
  sexpr <- parse input
  case sexpr of
    SPar _ [svars, SPar _ sforms, SPar _ sgames] -> do
      vars <- parseVarDecs svars
      let spec = Spec.empty vars
      spec <- foldM (addF vars) spec sforms
      foldM (addG vars) spec sgames
    _ -> perr (getPos sexpr) "Top level structure does not contain all three parts"
  where
    addF vars spec s = do
      f <- parseSpec vars s
      case Spec.addFormula spec f of
        Right spec -> pure spec
        Left err -> perr (getPos s) err
    addG vars spec s = do
      (arena, obj) <- parseGame vars s
      case Spec.addGame spec arena obj of
        Right spec -> pure spec
        Left err -> perr (getPos s) err

--
-- Variable Declaration
--
keywords :: [String]
keywords = ["true", "false", "and", "or", "not", "distinct", "ite", "abs", "mod", "div", "to_real"]

parseVarDecs :: SExpr -> PRes Variables
parseVarDecs =
  \case
    SPar _ decls -> foldM addDec Vars.empty decls
    s -> perr (getPos s) "Expected list of variable declarations"
  where
    addDec vars d = do
      (name, varType) <- parseVarDec d
      when (name `elem` keywords) $ perr (getPos d) "Keyword not allowed as variable"
      unless (isVarName name) $ perr (getPos d) $ "\"" ++ name ++ "\" is not a legal variable name"
      when (name `elem` Vars.allSymbols vars)
        $ perr (getPos d)
        $ "Duplicate or illegal instance of " ++ name
      pure (Vars.addVariable vars name varType)

parseVarDec :: SExpr -> PRes (String, Type)
parseVarDec =
  \case
    SPar _ [SId _ "input", sortExpr, SId _ name] -> do
      sort <- parseSort sortExpr
      pure (name, Vars.TInput sort)
    SPar _ [SId _ "state", sortExpr, SId _ name] -> do
      sort <- parseSort sortExpr
      pure (name, Vars.TState sort)
    s -> perr (getPos s) "Expected variable declaration"

parseSort :: SExpr -> PRes Sort
parseSort =
  \case
    SId _ "Bool" -> pure SBool
    SId _ "Int" -> pure SInt
    SId _ "Real" -> pure SReal
    s -> perr (getPos s) "Expected sort"

isVarName :: String -> Bool
isVarName =
  \case
    [] -> False
    c:sr -> c `elem` idStarts && all (`elem` idSymbols) sr
  where
    idStarts = ['a' .. 'z'] ++ ['A' .. 'Z']
    idSymbols = idStarts ++ ['0' .. '9'] ++ ['\'', '_']

--
-- Formula
--
parseSpec :: Variables -> SExpr -> PRes (TL.Spec Term)
parseSpec vars =
  \case
    SPar _ [SPar _ sasp, SPar _ sgar] -> do
      asmpt <- mapM (parseFormula vars) sasp
      guar <- mapM (parseFormula vars) sgar
      pure $ TL.Spec {TL.variables = vars, TL.assumptions = asmpt, TL.guarantees = guar}
    s -> perr (getPos s) "Expected RP-LTL specification pattern"

parseFormula :: Variables -> SExpr -> PRes (TL.Formula Term)
parseFormula vars = go
  where
    go =
      \case
        SPar _ [SId _ "ap", sub] -> TL.Atom <$> parseTerm vars sub
        SPar _ [SId _ "not", sub] -> TL.Not <$> go sub
        SPar _ (SId _ "and":subs) -> TL.And <$> mapM go subs
        SPar _ (SId _ "or":subs) -> TL.Or <$> mapM go subs
        SPar _ [SId _ "X", sub] -> TL.UExp TL.Next <$> go sub
        SPar _ [SId _ "F", sub] -> TL.UExp TL.Eventually <$> go sub
        SPar _ [SId _ "G", sub] -> TL.UExp TL.Globally <$> go sub
        SPar _ [SId _ "W", sub1, sub2] -> do
          f1 <- go sub1
          f2 <- go sub2
          pure $ TL.BExp TL.WeakUntil f1 f2
        SPar _ [SId _ "U", sub1, sub2] -> do
          f1 <- go sub1
          f2 <- go sub2
          pure $ TL.BExp TL.Until f1 f2
        SPar _ [SId _ "R", sub1, sub2] -> do
          f1 <- go sub1
          f2 <- go sub2
          pure $ TL.BExp TL.Release f1 f2
        s -> perr (getPos s) "Expected RP-LTL formula"

--
-- Game
--
parseGame :: Variables -> SExpr -> PRes (Arena, Objective)
parseGame vars =
  \case
    SPar _ [SPar _ slocs, SPar _ strans, sobj] -> do
      (arena, toLoc, toRank) <- parseLocs (SG.empty vars) slocs
      arena <- parseTrans toLoc arena strans
      obj <- parseObj toLoc toRank sobj
      pure (arena, obj)
    s -> perr (getPos s) "Expected symbolic game pattern"

parseLocs :: Arena -> [SExpr] -> PRes (Arena, Map String Loc, Map String Word)
parseLocs arena = foldM go (arena, Map.empty, Map.empty)
  where
    go (arena, toLoc, toRank) =
      \case
        SPar _ [SId p name, SId pr rank, sdom] -> do
          when (name `Map.member` toLoc) $ perr p $ "Location \"" ++ name ++ "\" already defined"
          (arena, loc) <- pure $ SG.addLoc arena name
          rank <-
            case readMaybe rank of
              Nothing -> perr pr "Could not parse acceptance number"
              Just num -> pure num
          arena <- SG.setDomain arena loc <$> parseTerm (SG.variables arena) sdom
          pure (arena, Map.insert name loc toLoc, Map.insert name rank toRank)
        s -> perr (getPos s) "Expected location definition"

parseTrans :: Map String Loc -> Arena -> [SExpr] -> PRes Arena
parseTrans toLoc = foldM go
  where
    go arena =
      \case
        SPar _ [SId p1 ls1, SId p2 ls2, sterm] -> do
          l1 <- lookupLoc toLoc p1 ls1
          l2 <- lookupLoc toLoc p2 ls2
          term <- parseTerm (SG.variables arena) sterm
          pure $ SG.setTrans arena l1 l2 term
        s -> perr (getPos s) "Expected transition definition"

parseObj :: Map String Loc -> Map String Word -> SExpr -> PRes Objective
parseObj toLoc toRank =
  \case
    SPar _ [SId pl loc, SId pw wc] -> do
      loc <- lookupLoc toLoc pl loc
      let greaterZero = Set.map (toLoc !) $ Map.keysSet $ Map.filter (> 0) toRank
      let rankMap = Map.mapKeys (toLoc !) toRank
      wc <-
        case wc of
          "Safety" -> pure $ Obj.Safety greaterZero
          "Reachability" -> pure $ Obj.Reachability greaterZero
          "Buechi" -> pure $ Obj.Buechi greaterZero
          "CoBuechi" -> pure $ Obj.CoBuechi greaterZero
          "ParityMaxOdd" -> pure $ Obj.Parity rankMap
          s -> perr pw $ "Found unkown winning condition \"" ++ s ++ "\""
      pure $ Obj.Objective {Obj.initialLoc = loc, Obj.winningCond = wc}
    s -> perr (getPos s) "Expected objective defintion"

lookupLoc :: Map String a -> Pos -> String -> PRes a
lookupLoc strTo pos str =
  case strTo !? str of
    Just a -> pure a
    Nothing -> perr pos $ "\"" ++ str ++ "\" not found"

--
-- Term
--
parseTerm :: Variables -> SExpr -> PRes Term
parseTerm vars = go
  where
    go =
      \case
        SId p name
          | name == "true" -> pure FOL.true
          | name == "false" -> pure FOL.false
          | name `elem` Vars.allSymbols vars -> pure $ Vars.mk vars name
          | otherwise ->
            case SMTLib.tryParseInt 0 name of
              Just n -> pure $ FOL.Const $ FOL.CInt n
              Nothing ->
                case SMTLib.tryParseRat 1 0 name of
                  Just r -> pure $ FOL.Const $ FOL.CReal r
                  Nothing -> perr p $ "Found undeclared variables or constant \"" ++ name ++ "\""
        SPar _ (SId p name:args) ->
          case SMTLib.parseFuncName name of
            Just func -> mapM go args >>= func
            Nothing -> perr p $ "Found unkown function while parsing term: \"" ++ name ++ "\""
        s -> perr (getPos s) "Found unkown pattern while parsing term"
