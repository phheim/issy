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

import Issy.Base.Variables hiding (empty)
import qualified Issy.Base.Variables as Vars (empty)
import Issy.Logic.FOL
import Issy.Logic.TSLMT (TSL, TSLAtom(..), TSLSpec(..))
import Issy.Logic.Temporal
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
    'v':'a':'r':' ':'I':'n':'t':' ':sr -> Right (TOutput SInt, sr)
    'v':'a':'r':' ':'R':'e':'a':'l':' ':sr -> Right (TOutput SReal, sr)
    'v':'a':'r':' ':'B':'o':'o':'l':' ':sr -> Right (TOutput SBool, sr)
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
          if id `elem` allSymbols vars
            then Left $ "double variable declaration: " ++ id
            else go (addVariable vars id typ) sr

translateSignalTerm :: (a -> Sort) -> (a -> Symbol) -> SignalTerm a -> Term
translateSignalTerm typ toStr =
  \case
    Signal a -> Var (toStr a) (typ a)
    FunctionTerm ft -> translateFuncTerm typ toStr ft
    PredicateTerm pt -> translatePredTerm typ toStr pt

parseFunc :: String -> Function
parseFunc str =
  PredefF
    $ case str of
        "and" -> "and"
        "or" -> "or"
        "not" -> "not"
        "ite" -> "ite"
        "add" -> "+"
        "sub" -> "-"
        "mul" -> "*"
        "div" -> "/"
        "mod" -> "mod"
        "abs" -> "abs"
        "to_real" -> "to_real"
        "eq" -> "="
        "lt" -> "<"
        "gt" -> ">"
        "lte" -> "<="
        "gte" -> ">="
        str -> error $ "found unkown function : " ++ str

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
    _ -> uncurry Func (go ft)
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
    BooleanTrue -> true
    BooleanFalse -> false
    BooleanInput a
      | typ a == SBool -> Var (toStr a) SBool
      | otherwise -> error "found boolean input with non-boolean sort"
            -- TODO: this might actually be not complete!
    PredicateSymbol constp -> Const $ parseConst (toStr constp)
    term -> uncurry Func $ go term
  where
    go =
      \case
        PredicateSymbol pred -> (parseFunc (toStr pred), [])
        PApplied pt st ->
          let (func, args) = go pt
           in (func, args ++ [translateSignalTerm typ toStr st])
        _ -> error "found illegal predicate structure"

translateFormula :: (a -> Sort) -> (a -> String) -> Formula a -> TSL
translateFormula typ toStr = go
  where
    go =
      \case
        TTrue -> TLAnd []
        FFalse -> TLOr []
        Check p -> TLAtomic $ TSLPredicate $ translatePredTerm typ toStr p
        Update a u -> TLAtomic $ TSLUpdate (toStr a) $ translateSignalTerm typ toStr u
        Not f -> TLNot (go f)
        Implies f g -> go $ Or [Not f, g]
        Equiv f g -> go $ And [Implies f g, Implies g f]
        And fs -> TLAnd $ map go fs
        Or fs -> TLOr $ map go fs
        Next f -> TLUnaryOp TLNext (go f)
        Globally f -> TLUnaryOp TLGlobally (go f)
        Finally f -> TLUnaryOp TLEventually (go f)
        Until f g -> TLBinaryOp TLUntil (go f) (go g)
        Release f g -> TLBinaryOp TLRelease (go f) (go g)
        Weak f g -> TLBinaryOp TLWeakUntil (go f) (go g)
        _ -> error "Found not implemented operator"

translateSpec :: Variables -> Specification -> TSLSpec
translateSpec vars spec =
  let toStr = stName (symboltable spec)
      transform = translateFormula (sortOf vars . toStr) toStr
   in TSLSpec
        { variables = vars
        , assumptions = transform <$> TSL.assumptions spec
        , guarantees = transform <$> TSL.guarantees spec
        }

parseTSL :: String -> IO TSLSpec
parseTSL s =
  case parseDecls s of
    Left err -> error $ "parseTSL" ++ err
    Right (vars, tslstr) -> do
      mSpec <- fromTSL Nothing tslstr
      case mSpec of
        Left err -> error $ show err
        Right spec -> pure $ translateSpec vars spec
