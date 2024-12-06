-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Parsers.SMTLib where

-------------------------------------------------------------------------------
import Data.Char (digitToInt, isDigit)
import qualified Data.Map as Map (fromList)
import Data.Map ((!?))
import Data.Map.Strict (fromListWith, keysSet)
import Data.Ratio ((%))
import Data.Set (Set)

import Issy.Logic.FOL
import Issy.Parsers.SMTLibLexer

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
      let m = fromListWith (error "No duplicates!") asgnT
      e <-
        exprToTerm
          (\s ->
             if s `elem` keysSet m
               then Just SBool
               else ty s)
          t
      Right (mapTermM m e)
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
    EList (EVar "forall":r) -> exprToQuant (\s -> forAll [s]) ty r
    EList (EVar "exists":r) -> exprToQuant (\s -> exists [s]) ty r
    EList (EVar "let":r) -> parseLet ty r
    EList [EVar "not", r] -> neg <$> exprToTerm ty r
    EList (EVar n:r) -> do
      args <- mapM (exprToTerm ty) r
      if n `elem` predefined
        then Right $ Func (PredefF n) args
        else case ty n of
               Just (SFunc argT retT) -> Right $ Func (CustomF n argT retT) args
               Just _ -> perr "exprToTerm" "Expected function sort"
               Nothing -> perr "exprToTerm" ("Undefined function: " ++ n)
    EList [t] -> exprToTerm ty t
    _ -> perr "exprToTerm" "Unknown pattern"

parseConstTerm :: (String -> Maybe Sort) -> String -> PRes Term
parseConstTerm types =
  \case
    "true" -> (Right . Const . CBool) True
    "false" -> (Right . Const . CBool) False
    "0" -> (Right . Const . CInt) 0
    s ->
      case tryParseInt 0 s of
        Just n -> (Right . Const . CInt) n
        Nothing ->
          case tryParseRat 1 0 s of
            Just r -> (Right . Const . CReal) r
            Nothing ->
              case types s of
                Just t -> Right (Var s t)
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
    _ -> perr func "Expected idenfifier token"

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

--TODO: Include into parser
extractModel :: Set Symbol -> String -> Model
extractModel frees str =
  case parseModel frees (tokenize str) of
    Right m -> sanitizeModel frees m
    Left err -> error err

parseModel :: Set Symbol -> [Token] -> PRes Model
parseModel frees ts = fst . fst <$> psexpr pFunDef (emptyModel, []) ts
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
      let func = foldr (uncurry lambda) body svars
      let ftype = SFunc (map snd svars) ret
      let auxF' =
            if name `notElem` frees
              then auxF ++ [(name, ftype)]
              else auxF
      Right ((modelAddT name func m, auxF'), ts)
    pSortedVar :: [(Symbol, Sort)] -> [Token] -> PRes ([(Symbol, Sort)], [Token])
    pSortedVar acc ts = do
      ts <- pread TLPar ts "pSortedVar"
      (v, ts) <- preadID ts "pSortedVar"
      (s, ts) <- psort ts
      ts <- pread TRPar ts "pSortedVar"
      Right (acc ++ [(v, s)], ts)
{-
parseValueList :: String -> Model
parseValueList s =
  case tokenize s of
    TLPar:tr -> parseVPs emptyModel tr
    _ -> error "Assertion: expected other pattern"
  where
    parseVPs :: Model -> [Token] -> Model
    parseVPs m =
      \case
        [TRPar] -> m
        TLPar:TId s:tr ->
          case parseTerm (error "Assertion: expected constant term") tr of
            Left err -> error ("Assertion: " ++ err)
            Right (t, TRPar:tr') -> parseVPs (modelAddT s t m) tr'
            Right _ -> error "Assertion: Expected closing ')'"
        _ -> error "Assertion: expected other pattern"
-}
