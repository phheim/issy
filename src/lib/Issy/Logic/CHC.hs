---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.CHC
  ( fromTerm
  , check
  , computeMax
  , computeFP
  ) where

---------------------------------------------------------------------------------------------------
import Data.Bifunctor (first)
import Data.Char (isDigit)
import Data.List (isPrefixOf)
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Process (readProcessWithExitCode)
import Text.Read (readMaybe)

---------------------------------------------------------------------------------------------------
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, chcMaxScript, chcMaxTimeOut, chcTimeout, z3cmd)
import Issy.Logic.FOL (Sort(SBool, SInt), Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Utils.Extra (runTO)
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- Conversion
---------------------------------------------------------------------------------------------------
-- Translation from normal FOL formula to CHC from, is not complete!
fromTerm :: Term -> ([Term], Term)
fromTerm = go . FOL.toNNF
  where
    go =
      \case
        FOL.Func FOL.FOr [arg] -> go arg
        FOL.Func FOL.FOr (a:args) ->
          case FOL.toNNF (FOL.neg a) of
            FOL.Func FOL.FAnd andArgs -> first (andArgs ++) $ go $ FOL.orf args
            a -> first (a :) $ go $ FOL.orf args
        conc -> ([], conc)

---------------------------------------------------------------------------------------------------
-- CHC solving
---------------------------------------------------------------------------------------------------
check :: Config -> Symbol -> [Sort] -> [([Term], Term)] -> IO (Maybe Bool)
check conf invPred sorts constraints = do
  let query = chcEncode invPred sorts constraints
  callCHCSolver conf query

chcEncode :: Symbol -> [Sort] -> [([Term], Term)] -> String
chcEncode invPred sorts constr =
  unlines
    $ [ "(set-logic HORN)"
      , "(declare-fun "
          ++ invPred
          ++ "("
          ++ concatMap ((' ' :) . SMTLib.sortToString) sorts
          ++ " ) Bool)"
      ]
        ++ map enc constr
        ++ ["(check-sat)"]
  where
    enc :: ([Term], Term) -> String
    enc (prem, conc) =
      let implication = FOL.func FOL.FImply [FOL.andf prem, conc]
          qimplication = FOL.forAll (Set.toList (FOL.frees implication)) implication
       in "(assert " ++ SMTLib.toString qimplication ++ "))"

callCHCSolver :: Config -> String -> IO (Maybe Bool)
callCHCSolver conf query = do
  lgd conf ["CHC solver start running"]
  res <- runTO (Just (chcTimeout conf)) (z3cmd conf) ["-in", "-smt2"] query
  lgd conf ["CHC solver terminated"]
  case res of
    Just ('s':'a':'t':_) -> pure $ Just True
    Just ('u':'n':'s':'a':'t':_) -> pure $ Just False
    _ -> pure Nothing

---------------------------------------------------------------------------------------------------
-- MaxCHC
---------------------------------------------------------------------------------------------------
computeMax :: Config -> Variables -> Symbol -> [([Term], Term)] -> IO (Either String Term)
computeMax config vars invName constraints
  | invalidSorts constraints = pure $ Left "found non-integers"
  | otherwise =
    fmap (parseFP vars invName)
      $ callCHCMax config
      $ encodeFP vars invName
      $ map encodeConstr constraints

--TODO: this is somewhat ugly and should be removed
computeFP :: Config -> Variables -> Symbol -> Term -> Term -> IO (Maybe Term)
computeFP cfg vars fpPred init trans
  | invalidSorts [([init], trans)] = do
    lg cfg ["CHCMax", "found non ints!"]
    pure Nothing
  | otherwise = do
    let query = encodeFP vars fpPred [init, trans]
    lg cfg ["CHCMax", "running"]
    res <- callCHCMax cfg query
    case parseFP vars fpPred res of
      Left err -> do
        lg cfg ["CHCMax returned error:", err]
        pure Nothing
      Right term -> do
        lg cfg ["CHCMax returned result:", SMTLib.toString term]
        pure (Just term)

invalidSorts :: [([Term], Term)] -> Bool
invalidSorts terms =
  let sorts = Set.unions $ map FOL.sorts $ concatMap (\(preds, conc) -> conc : preds) terms
   in FOL.SReal `elem` sorts

callCHCMax :: Config -> String -> IO String
callCHCMax cfg query = do
  lgd cfg ["CHCMax-query", query]
  (_, stdout, _) <- readProcessWithExitCode (chcMaxScript cfg) [show (chcMaxTimeOut cfg)] query
  pure stdout

encodeConstr :: ([Term], Term) -> Term
encodeConstr (prems, conc) =
  let horn = FOL.func FOL.FImply [FOL.andf prems, conc]
   in FOL.forAll (Set.toList (FOL.frees horn)) horn

encodeFP :: Variables -> Symbol -> [Term] -> String
encodeFP vars invName constraints =
  unlines
    $ [ "(set-logic HORN)"
      , "(declare-fun "
          ++ invName
          ++ "("
          ++ concatMap ((" " ++) . SMTLib.sortToString . Vars.sortOf vars) (Vars.stateVarL vars)
          ++ ") Bool)"
      ]
        ++ map (\f -> "(assert " ++ SMTLib.toString f ++ ")") constraints
        ++ ["(check-sat)"]

data FPExpr
  = FPBop String FPExpr FPExpr
  | FPID String
  deriving (Eq, Ord, Show)

parseID :: String -> (String, String)
parseID = span (`notElem` [' ', '\n', '\t', ')', '(', ':'])

parseFPExpr :: String -> Either String (FPExpr, String)
parseFPExpr =
  \case
    [] -> Left "empty string while parsing FPExpr"
    '(':sr -> do
      (expr1, sr) <- parseFPExpr sr
      case sr of
        ')':sr -> Right (expr1, sr)
        ' ':sr -> do
          (op, sr) <- pure $ parseID sr
          case sr of
            ' ':sr -> do
              (expr2, sr) <- parseFPExpr sr
              case sr of
                ')':sr -> pure (FPBop op expr1 expr2, sr)
                _ -> Left $ "Expected closing ')' after binary expression, found" ++ sr
            _ -> Left $ "Expected whitespace after operator, found " ++ sr
        _ -> Left $ "Expected whitespace or cosing ')' after expression, found " ++ sr
    ' ':sr -> parseFPExpr sr
    '\n':sr -> parseFPExpr sr
    '\t':sr -> parseFPExpr sr
    '\r':sr -> parseFPExpr sr
    sr -> do
      (ident, sr) <- pure $ parseID sr
      pure (FPID ident, sr)

fpExprToTerm :: Map String (Symbol, Sort) -> FPExpr -> Either String Term
fpExprToTerm varMap = go
  where
    go =
      \case
        FPID [] -> Left "Found empty identifier"
        FPID "true" -> pure FOL.true
        FPID "false" -> pure FOL.false
        FPID ('-':cs) ->
          case readMaybe cs of
            Just k -> pure $ FOL.Const $ FOL.CInt (-k)
            Nothing -> Left $ "Found illegal identifier: " ++ cs
        FPID (c:cs)
          | isDigit c ->
            case readMaybe (c : cs) of
              Just k -> pure $ FOL.Const $ FOL.CInt k
              Nothing -> Left $ "Found illegal identifier: " ++ (c : cs)
          | otherwise ->
            case varMap !? (c : cs) of
              Just (v, sort) -> pure $ FOL.Var v sort
              Nothing -> Left $ "Found unknown identifier: " ++ (c : cs)
        FPBop op e1 e2 -> do
          t1 <- go e1
          t2 <- go e2
          case op of
            "/\\" -> pure $ FOL.andf [t1, t2]
            "\\/" -> pure $ FOL.orf [t1, t2]
            "!=" -> pure $ FOL.neg $ FOL.equal t1 t2
            "+" -> pure $ FOL.func FOL.FAdd [t1, t2]
            "-" -> pure $ FOL.func FOL.FSub [t1, t2]
            "=" -> pure $ FOL.func FOL.FEq [t1, t2]
            "<=" -> pure $ FOL.func FOL.FLte [t1, t2]
            ">=" -> pure $ FOL.func FOL.FGte [t1, t2]
            "*" -> pure $ FOL.func FOL.FMul [t1, t2]
            _ -> Left $ "Found illegal operator: " ++ op

parseFPHead :: Variables -> String -> String -> Either String (Map String (Symbol, Sort), String)
parseFPHead vars fpPred sr = do
  sr <- pure $ dropWhile (`elem` [' ', '\n', '\t', '\r']) sr
  sr <-
    if fpPred `isPrefixOf` sr
      then pure $ drop (length fpPred) sr
      else Left "Predicate is not the right one"
  case sr of
    '(':sr -> do
      (decls, sr) <- parseDecls (Vars.stateVarL vars) sr
      pure (Map.fromList decls, sr)
    _ -> Left "Expected opening '('"
  where
    parseDecls :: [Symbol] -> String -> Either String ([(String, (Symbol, Sort))], String)
    parseDecls states sr =
      case (states, sr) of
        ([], ')':sr) -> pure ([], sr)
        ([], _) -> Left $ "Expected closing ')' found " ++ sr
        (st:states, sr) -> do
          (decl, sr) <- parseDecl st (Vars.sortOf vars st) sr
          (decls, sr) <- parseDecls states sr
          pure (decl : decls, sr)
    --
    parseDecl :: Symbol -> Sort -> String -> Either String ((Symbol, (Symbol, Sort)), String)
    parseDecl var sort sr = do
      sr <- expectChar '(' (removeWS sr)
      (ident, sr) <- pure $ parseID sr
      sr <- expectChar ':' (removeWS sr)
      sr <-
        case removeWS sr of
          'i':'n':'t':sr
            | sort == SInt -> pure sr
            | otherwise -> Left "Expected int sort"
          'b':'o':'o':'l':sr
            | sort == SBool -> pure sr
            | otherwise -> Left "Expected bool sort"
          _ -> Left $ "Expected sort found " ++ sr
      sr <- expectChar ')' (removeWS sr)
      pure ((ident, (var, sort)), sr)

expectChar :: Char -> String -> Either String String
expectChar c =
  \case
    [] -> Left $ "Expected " ++ [c] ++ " found empty string"
    s:sr
      | c == s -> pure sr
      | otherwise -> Left $ "Expected " ++ [c] ++ " found " ++ sr

removeWS :: String -> String
removeWS = dropWhile (`elem` [' ', '\n', '\t', '\r'])

parseFP :: Variables -> String -> String -> Either String Term
parseFP vars fpPred sr =
  case gotoMaxsat sr of
    [] -> Left "No maxsat found"
    sr -> do
      (varMap, sr) <- parseFPHead vars fpPred sr
      sr <- pure $ gotoAssign sr
      (expr, _) <- parseFPExpr sr
      fpExprToTerm varMap expr
  where
    gotoMaxsat :: String -> String
    gotoMaxsat = unlines . drop 1 . dropWhile (not . isPrefixOf "Maxsat") . lines
     -- 
    gotoAssign :: String -> String
    gotoAssign =
      \case
        [] -> ""
        ':':'=':sr -> sr
        c:sr -> c : gotoAssign sr
---------------------------------------------------------------------------------------------------
