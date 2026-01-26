---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Parsers.TSLMT
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

module Issy.Parsers.TSLMT
  ( parseTSL
  ) where

import Data.Char (isAsciiLower, isAsciiUpper)

import TSL
  ( Formula(..)
  , FunctionTerm(..)
  , PredicateTerm(..)
  , SignalTerm(..)
  , Specification(symboltable)
  , SymbolTable(stName)
  , fromTSL
  )
import qualified TSL (Specification(assumptions, guarantees))

import Issy.Games.Variables (Type(..), Variables)
import qualified Issy.Games.Variables as Vars
import Issy.Logic.FOL (Constant(..), Sort(..), Symbol, Term(..))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.TSLMT as TSLMT
import qualified Issy.Logic.Temporal as TL
import Issy.Parsers.SMTLib (tryParseInt, tryParseRat)

-- Declarations have the form
--  [inp | var] SORT ID
--
parseID :: String -> Either String String
parseID =
  \case
    [] -> Right ""
    ' ':_ -> Right ""
    c:cr
      | isAsciiUpper c || isAsciiLower c || (c >= '0' || c <= '9') || c == '_' ->
        (c :) <$> parseID cr
      | otherwise -> Left "illegal id character"

parseType :: String -> Either String (Type, String)
parseType =
  \case
    'i':'n':'p':' ':'I':'n':'t':' ':sr -> Right (TInput SInt, sr)
    'i':'n':'p':' ':'R':'e':'a':'l':' ':sr -> Right (TInput SReal, sr)
    'i':'n':'p':' ':'B':'o':'o':'l':' ':sr -> Right (TInput SBool, sr)
    'v':'a':'r':' ':'I':'n':'t':' ':sr -> Right (TState SInt, sr)
    'v':'a':'r':' ':'R':'e':'a':'l':' ':sr -> Right (TState SReal, sr)
    'v':'a':'r':' ':'B':'o':'o':'l':' ':sr -> Right (TState SBool, sr)
    decl -> Left $ "illegal type declaration: " ++ decl

parseDecls :: String -> Either String (Variables, String)
parseDecls = go Vars.empty . lines
  where
    go vars =
      \case
        [] -> Right (vars, "")
        "SPECIFICATION":s -> Right (vars, unlines s)
        "":s -> go vars s
        s:sr -> do
          (typ, s) <- parseType s
          id <- parseID s
          if id `elem` Vars.allSymbols vars
            then Left $ "double variable declaration: " ++ id
            else go (Vars.addVariable vars id typ) sr

translateSignalTerm :: (a -> Sort) -> (a -> Symbol) -> SignalTerm a -> Term
translateSignalTerm typ toStr =
  \case
    Signal a -> Var (toStr a) (typ a)
    FunctionTerm ft -> translateFuncTerm typ toStr ft
    PredicateTerm pt -> translatePredTerm typ toStr pt

parseFunc :: String -> [Term] -> Term
parseFunc name =
  case name of
    "and" -> FOL.andf
    "or" -> FOL.orf
    "not" -> uop FOL.neg
    "ite" -> top FOL.ite
    "add" -> FOL.addT
    "sub" -> FOL.minusT
    "mul" -> FOL.multT
    "div" -> bop FOL.intdivT
    "mod" -> bop FOL.modT
    "abs" -> uop FOL.absT
    "to_real" -> uop FOL.toRealT
    "eq" -> bop FOL.equal
    "lt" -> bop FOL.ltT
    "gt" -> bop FOL.gtT
    "lte" -> bop FOL.leqT
    "gte" -> bop FOL.geqT
    str -> error $ "found unkown function : " ++ str
  where
    uop op [a] = op a
    uop _ _ = error $ "found \'" ++ name ++ "\' with not one argument"
    bop op [a, b] = op a b
    bop _ _ = error $ "found \'" ++ name ++ "\' with not two arguments"
    top op [a, b, c] = op a b c
    top _ _ = error $ "found \'" ++ name ++ "\' with not three arguments"

parseConst :: String -> Constant
parseConst =
  \case
    "true" -> CBool True
    "false" -> CBool False
    'i':str ->
      case tryParseInt 0 str of
        Just n -> CInt n
        Nothing -> error $ "could not parse " ++ str ++ " as interger"
    'r':str ->
      case tryParseRat 1 0 str of
        Just r -> CReal r
        Nothing -> error $ "could not parse " ++ str ++ " as rational"
    str -> error $ "found unkown constat: " ++ str

translateFuncTerm :: (a -> Sort) -> (a -> Symbol) -> FunctionTerm a -> Term
translateFuncTerm typ toStr ft =
  case ft of
        -- here we have a constant
    FunctionSymbol constf -> Const $ parseConst (toStr constf)
        -- here we have a proper function
    _ ->
      let (func, args) = go ft
       in func args
  where
    go =
      \case
        FunctionSymbol func -> (parseFunc (toStr func), [])
        FApplied ft st ->
          let (func, args) = go ft
           in (func, args ++ [translateSignalTerm typ toStr st])

translatePredTerm :: (a -> Sort) -> (a -> Symbol) -> PredicateTerm a -> Term
translatePredTerm typ toStr =
  \case
    BooleanTrue -> FOL.true
    BooleanFalse -> FOL.false
    BooleanInput a
      | typ a == SBool -> Var (toStr a) SBool
      | otherwise -> error "found boolean input with non-boolean sort"
    PredicateSymbol constp -> Const $ parseConst (toStr constp)
    term ->
      let (func, args) = go term
       in func args
  where
    go =
      \case
        PredicateSymbol pred -> (parseFunc (toStr pred), [])
        PApplied pt st ->
          let (func, args) = go pt
           in (func, args ++ [translateSignalTerm typ toStr st])
        _ -> error "found illegal predicate structure"

translateFormula :: (a -> Sort) -> (a -> String) -> Formula a -> TL.Formula TSLMT.Atom
translateFormula typ toStr = go
  where
    go =
      \case
        TTrue -> TL.And []
        FFalse -> TL.Or []
        Check p -> TL.Atom $ TSLMT.Predicate $ translatePredTerm typ toStr p
        Update a u -> TL.Atom $ TSLMT.Update (toStr a) $ translateSignalTerm typ toStr u
        Not f -> TL.Not (go f)
        Implies f g -> go $ Or [Not f, g]
        Equiv f g -> go $ And [Implies f g, Implies g f]
        And fs -> TL.And $ map go fs
        Or fs -> TL.Or $ map go fs
        Next f -> TL.UExp TL.Next (go f)
        Globally f -> TL.UExp TL.Globally (go f)
        Finally f -> TL.UExp TL.Eventually (go f)
        Until f g -> TL.BExp TL.Until (go f) (go g)
        Release f g -> TL.BExp TL.Release (go f) (go g)
        Weak f g -> TL.BExp TL.WeakUntil (go f) (go g)
        _ -> error "Found not implemented operator"

translateSpec :: Variables -> Specification -> TL.Spec TSLMT.Atom
translateSpec vars spec =
  let toStr = stName (symboltable spec)
      transform = translateFormula (Vars.sortOf vars . toStr) toStr
   in TL.Spec
        { TL.variables = vars
        , TL.assumptions = transform <$> TSL.assumptions spec
        , TL.guarantees = transform <$> TSL.guarantees spec
        }

parseTSL :: String -> IO (TL.Spec TSLMT.Atom)
parseTSL s =
  case parseDecls s of
    Left err -> error $ "parseTSL" ++ err
    Right (vars, tslstr) -> do
      mSpec <- fromTSL tslstr
      case mSpec of
        Left err -> error $ show err
        Right spec -> pure $ translateSpec vars spec
---------------------------------------------------------------------------------------------------
