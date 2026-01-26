---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Parsers.SMTLib
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Parsers.SMTLib where

-------------------------------------------------------------------------------
import Data.Char (digitToInt, isDigit)
import qualified Data.Map.Strict as Map
import Data.Map.Strict ((!?))
import Data.Ratio ((%))
import Data.Set (Set)

import Issy.Logic.FOL (Function(CustomF), Model, Sort(..), Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import Issy.Parsers.SMTLibLexer (Token(..), tokenize)

-------------------------------------------------------------------------------
type PRes a = Either String a

perr :: String -> String -> PRes a
perr func msg = Left ("TermParser." ++ func ++ ": " ++ msg)

data TermExpr
  = EVar String
  | EList [TermExpr]
  deriving (Eq, Ord, Show)

parseTermExpr :: [Token] -> PRes (TermExpr, [Token])
parseTermExpr =
  \case
    TId n:tr -> Right (EVar n, tr)
    TLPar:tr -> do
      (es, tr') <- pTermExprs [] tr
      Right (EList es, tr')
    _ -> perr "parseTermExpr" "Invalid pattern"
  where
    pTermExprs args =
      \case
        [] -> perr "parseTermExpr" "Expected ')' found EOF"
        TRPar:tr -> Right (reverse args, tr)
        ts -> do
          (term, tr) <- parseTermExpr ts
          pTermExprs (term : args) tr

parseLet :: (String -> Maybe Sort) -> [TermExpr] -> PRes Term
parseLet ty =
  \case
    [EList asgn, t] -> do
      asgnT <- mapM pLt asgn
      let m = Map.fromListWith (error "No duplicates!") asgnT
      e <-
        exprToTerm
          (\s ->
             if s `elem` Map.keysSet m
               then Just SBool
               else ty s)
          t
      Right $ FOL.mapTermM m e
    _ -> perr "parseLet" "Invaild pattern"
  where
    pLt =
      \case
        EList [EVar n, t] -> do
          e <- exprToTerm ty t
          Right (n, e)
        _ -> perr "parseLet" "Invalid assignment pattern"

exprToTerm :: (String -> Maybe Sort) -> TermExpr -> PRes Term
exprToTerm ty =
  \case
    EVar n -> parseConstTerm ty n
    EList (EVar "forall":r) -> exprToQuant (\s -> FOL.forAll [s]) ty r
    EList (EVar "exists":r) -> exprToQuant (\s -> FOL.exists [s]) ty r
    EList (EVar "let":r) -> parseLet ty r
    EList [EVar "not", r] -> FOL.neg <$> exprToTerm ty r
    EList (EVar n:r) -> do
      args <- mapM (exprToTerm ty) r
      case parseFuncName n of
        Just pfunc -> pfunc args
        Nothing ->
          case ty n of
            Just (SFunc argT retT) -> Right $ FOL.Func (CustomF n argT retT) args
            Just _ -> perr "exprToTerm" "Expected function sort"
            Nothing -> perr "exprToTerm" ("Undefined function: " ++ n)
    EList [t] -> exprToTerm ty t
    _ -> perr "exprToTerm" "Unknown pattern"

parseFuncName :: String -> Maybe ([Term] -> PRes Term)
parseFuncName fname =
  case fname of
    "and" -> Just $ Right . FOL.andf
    "or" -> Just $ Right . FOL.orf
    "not" -> Just $ liftUOp FOL.neg
    "distinct" -> Just $ Right . FOL.distinct
    "=>" -> Just $ liftBOp FOL.implyT
    "ite" -> Just $ liftTOp FOL.ite
    "+" -> Just $ Right . FOL.addT
    "-" -> Just $ Right . FOL.minusT
    "*" -> Just $ Right . FOL.multT
    "/" -> Just $ liftBOp FOL.realdivT
    "=" -> Just $ liftBOp FOL.equal
    "<" -> Just $ liftBOp FOL.ltT
    ">" -> Just $ liftBOp FOL.gtT
    "<=" -> Just $ liftBOp FOL.leqT
    ">=" -> Just $ liftBOp FOL.geqT
    "abs" -> Just $ liftUOp FOL.absT
    "to_real" -> Just $ liftUOp FOL.toRealT
    "mod" -> Just $ liftBOp FOL.modT
    "div" -> Just $ liftBOp FOL.intdivT
    _ -> Nothing
  where
    liftUOp op [t] = Right $ op t
    liftUOp _ _ = perr "parseFuncName" $ "\'" ++ fname ++ "\' expects only one argument"
    liftBOp op [t1, t2] = Right $ op t1 t2
    liftBOp _ _ = perr "parseFuncName" $ "\'" ++ fname ++ "\' expects exactly two arguments"
    liftTOp op [t1, t2, t3] = Right $ op t1 t2 t3
    liftTOp _ _ = perr "parseFuncName" $ "\'" ++ fname ++ "\' expects exactly three arguments"

parseConstTerm :: (String -> Maybe Sort) -> String -> PRes Term
parseConstTerm types =
  \case
    "true" -> Right $ FOL.boolConst True
    "false" -> Right $ FOL.boolConst False
    "0" -> Right $ FOL.intConst 0
    s ->
      case tryParseInt 0 s of
        Just n -> Right $ FOL.intConst n
        Nothing ->
          case tryParseRat 1 0 s of
            Just r -> Right $ FOL.realConst r
            Nothing ->
              case types s of
                Just t -> Right $ FOL.var s t
                Nothing ->
                  perr "parseConstTerm" ("'" ++ s ++ "' is no constant term or declared constant")

tryParseInt :: Integer -> String -> Maybe Integer
tryParseInt n =
  \case
    [] -> Just n
    c:s
      | isDigit c -> tryParseInt (10 * n + toEnum (digitToInt c)) s
      | otherwise -> Nothing

tryParseRat :: Integer -> Rational -> String -> Maybe Rational
tryParseRat level r =
  \case
    [] -> Just r
    c:s
      | c == '.' -> tryParseRat 10 r s
      | isDigit c && level == 1 -> tryParseRat 1 (10 * r + toEnum (digitToInt c)) s
      | isDigit c -> tryParseRat (level * 10) (r + toEnum (digitToInt c) % level) s
      | otherwise -> Nothing

sortValue :: String -> PRes Sort
sortValue =
  \case
    "Bool" -> Right SBool
    "Int" -> Right SInt
    "Real" -> Right SReal
    s -> perr "sortValue" ("Unkown sort '" ++ s ++ "'")

exprToQuant :: (Symbol -> Term -> Term) -> (String -> Maybe Sort) -> [TermExpr] -> PRes Term
exprToQuant qw ty =
  \case
    [EList ((EList [EVar v, EVar t]):br), tr] -> do
      s <- sortValue t
      qw v
        <$> exprToQuant
              qw
              (\x ->
                 if x == v
                   then Just s
                   else ty x)
              [EList br, tr]
    [EList [], tr] -> exprToTerm ty tr
    _ -> perr "exprToQuant" "Expected binding list"

parseTerm :: (String -> Maybe Sort) -> [Token] -> PRes (Term, [Token])
parseTerm ty ts = do
  (e, tr) <- parseTermExpr ts
  t <- exprToTerm ty e
  Right (t, tr)

pread :: Token -> [Token] -> String -> PRes [Token]
pread ref ts func =
  case ts of
    [] -> perr func "Expected token to read"
    t:tr
      | t == ref -> Right tr
      | otherwise -> perr func ("Expected " ++ show ref)

preadID :: [Token] -> String -> PRes (String, [Token])
preadID ts func =
  case ts of
    [] -> perr func "Expected token to read"
    TId s:tr -> Right (s, tr)
    TLPar:_ -> perr func "Expected idenfifier token, found '('"
    TRPar:_ -> perr func "Expected idenfifier token, found ')'"

psort :: [Token] -> PRes (Sort, [Token])
psort =
  \case
    TId "Bool":ts -> Right (SBool, ts)
    TId "Int":ts -> Right (SInt, ts)
    TId "Real":ts -> Right (SReal, ts)
    _ -> perr "psort" "not a sort patterns"

psexpr :: (a -> [Token] -> PRes (a, [Token])) -> a -> [Token] -> PRes (a, [Token])
psexpr sub acc ts = pread TLPar ts "psexpr" >>= rec acc
  where
    rec acc =
      \case
        [] -> perr "psexpr" "found EOL before closing ')'"
        TRPar:ts -> Right (acc, ts)
        ts -> sub acc ts >>= uncurry rec

extractModel :: Set Symbol -> String -> Model
extractModel frees str =
  case parseModel frees (tokenize str) of
    Right m -> FOL.sanitizeModel frees m
    Left err -> error $ err ++ " in \"" ++ str ++ "\""

parseModel :: Set Symbol -> [Token] -> PRes Model
parseModel frees ts = fst . fst <$> psexpr pFunDef (FOL.emptyModel, []) ts
  where
    pFunDef :: (Model, [(Symbol, Sort)]) -> [Token] -> PRes ((Model, [(Symbol, Sort)]), [Token])
    pFunDef (m, auxF) ts = do
      ts <- pread TLPar ts "parseModel"
      ts <- pread (TId "define-fun") ts "parseModel"
      (name, ts) <- preadID ts "parseModel"
      (svars, ts) <- psexpr pSortedVar [] ts
      (ret, ts) <- psort ts
      (body, ts) <- parseTerm (Map.fromList (auxF ++ svars) !?) ts
      ts <- pread TRPar ts "parseModel"
      let func = foldr (uncurry FOL.lambda) body svars
      let ftype = SFunc (map snd svars) ret
      let auxF' =
            if name `notElem` frees
              then auxF ++ [(name, ftype)]
              else auxF
      Right ((FOL.modelAddT name func m, auxF'), ts)
    pSortedVar :: [(Symbol, Sort)] -> [Token] -> PRes ([(Symbol, Sort)], [Token])
    pSortedVar acc ts = do
      ts <- pread TLPar ts "pSortedVar"
      (v, ts) <- preadID ts "pSortedVar"
      (s, ts) <- psort ts
      ts <- pread TRPar ts "pSortedVar"
      Right (acc ++ [(v, s)], ts)
---------------------------------------------------------------------------------------------------
