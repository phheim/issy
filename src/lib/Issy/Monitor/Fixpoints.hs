{-# LANGUAGE LambdaCase #-}

module Issy.Monitor.Fixpoints
  ( checkFPInclusion
  , computeFP
  ) where

import Data.Char (isDigit)
import Data.Fixed
import Data.List (isPrefixOf)
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))
import Data.Set (Set)
import qualified Data.Set as Set
import System.Process (readProcessWithExitCode)
import Text.Read (readMaybe)

import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, chcMaxScript, chcMaxTimeOut, muvalScript, muvalTimeOut)
import Issy.Logic.FOL
import Issy.Printers.SMTLib (s2Term, smtLib2)
import Issy.Utils.Extra (firstLine)
import Issy.Utils.Logging

encSort :: Sort -> String
encSort =
  \case
    SInt -> "int"
    SBool -> "int"
    SReal -> "real"
    SFunc _ _ -> error "Function types not supported"

encConst :: Bool -> Constant -> String
encConst ugly =
  \case
    CInt n -> show n
    CReal r -> addDot $ showFixed True (fromRational r :: Nano)
    CBool True
      | ugly -> "1"
      | otherwise -> "(0 = 0)"
    CBool False
      | ugly -> "0"
      | otherwise -> "(0 = 1)"
  where
    addDot :: String -> String
    addDot =
      \case
        [] -> ".0"
        '.':sr -> '.' : sr
        c:sr -> c : addDot sr

encOp :: (a -> String) -> String -> String -> [a] -> String
encOp encA op neut =
  \case
    [] -> neut
    [x] -> "(" ++ encA x ++ ")"
    x:xr -> "(" ++ encA x ++ " " ++ op ++ " " ++ encOp encA op neut xr ++ ")"

-- TODO: Rename ugly to something more understandable!
encTerm :: Symbol -> (String, Int, Set Int) -> Bool -> Term -> String
encTerm fpPred (qpref, qdepth, bvars) ugly =
  \case
    Var v s
      | s == SBool && not ugly -> "(" ++ v ++ " = 1)"
      | s == SBool && ugly -> v
      | otherwise -> v
    Const c -> encConst ugly c
    QVar k
      | qdepth - k - 1 `elem` bvars && not ugly -> "(" ++ qpref ++ show (qdepth - k - 1) ++ " = 1)"
      | otherwise -> qpref ++ show (qdepth - k - 1)
    Func f args ->
      case f of
        CustomF name _ _
          | name == fpPred -> fpPred ++ concatMap ((" " ++) . recT) args
          | otherwise -> error "assert: cannot use non-fixpoint uninterpreted function"
        PredefF n
          | n == "or" -> encOp rec "\\/" "false" args
          | n == "and" -> encOp rec "/\\" "true" args
          | n == "not" -> "(not " ++ rec (head args) ++ ")"
          | n == "+" -> encOp rec "+" "0" args
          | n == "-" && length args == 1 -> "(- " ++ rec (head args) ++ ")"
          | n `elem` ["-", "=", "<", ">", ">=", "<=", "*"] -> binOp n args
          | n == "/" ->
            case args of
              [Const (CInt c1), Const (CInt c2)] -> encConst ugly (CReal (c1 % c2))
              _ -> error (n ++ " only supported for constants")
          | otherwise -> error (n ++ " not supported yet")
    Quant Exists sort term ->
      "(exists ( "
        ++ qpref
        ++ show qdepth
        ++ " : "
        ++ encSort sort
        ++ "). "
        ++ recNest sort term
        ++ ")"
    Quant Forall sort term ->
      "(forall ( "
        ++ qpref
        ++ show qdepth
        ++ " : "
        ++ encSort sort
        ++ "). "
        ++ recNest sort term
        ++ ")"
    Lambda _ _ -> error "lambdas not supported"
  where
    rec = encTerm fpPred (qpref, qdepth, bvars) ugly
    recT = encTerm fpPred (qpref, qdepth, bvars) True
    recNest SBool = encTerm fpPred (qpref, qdepth + 1, Set.insert qdepth bvars) ugly
    recNest _ = encTerm fpPred (qpref, qdepth + 1, bvars) ugly
    --
    binOp :: String -> [Term] -> String
    binOp op =
      \case
        [o1, o2] -> "(" ++ recT o1 ++ " " ++ op ++ " " ++ recT o2 ++ ")"
        _ -> error (op ++ "is a binary operator")

encFPInclusion :: Variables -> Term -> Symbol -> Term -> String
encFPInclusion vars query fpPred fp =
  let qPref =
        uniquePrefix "qvar" (symbols query `Set.union` symbols fp `Set.union` Vars.allSymbols vars)
   in unlines
        [ encTerm fpPred (qPref, 0, Set.empty) False query
        , "s.t."
        , fpPred
            ++ concatMap
                 (\v -> "(" ++ v ++ " : " ++ encSort (Vars.sortOf vars v) ++ ")")
                 (Vars.stateVarL vars)
            ++ ": bool =mu "
            ++ encTerm fpPred (qPref, 0, Set.empty) False fp
            ++ ";"
        ]

checkFPInclusion :: Config -> Variables -> Term -> Symbol -> Term -> IO Bool
checkFPInclusion cfg vars query fpPred fp = do
  let muvalQuery = encFPInclusion vars query fpPred fp
  fromMaybe False <$> callMuval cfg muvalQuery

callMuval :: Config -> String -> IO (Maybe Bool)
callMuval cfg query = do
  lg cfg ["MuVal", "running"]
  (_, stdout, _) <- readProcessWithExitCode (muvalScript cfg) [show (muvalTimeOut cfg)] query
  lg cfg ["MuVal", "terminated with", firstLine stdout]
  case stdout of
    'i':'n':'v':'a':'l':'i':'d':_ -> pure $ Just False
    'v':'a':'l':'i':'d':_ -> pure $ Just True
    _ -> pure Nothing

--
-- Max CHC
--
-- TODO: assert only ints !!!
--
computeFP :: Config -> Variables -> Symbol -> Term -> Term -> IO (Maybe Term)
computeFP cfg vars fpPred init trans = do
  let query = encodeFP vars fpPred init trans
  lg cfg ["CHCMax", "running"]
  res <- callCHCMax cfg query
  case parseFP vars fpPred res of
    Left err -> do
      lg cfg ["CHCMax returned error:", err]
      pure Nothing
    Right term -> do
      lg cfg ["CHCMax returned result:", smtLib2 term]
      pure (Just term)

callCHCMax :: Config -> String -> IO String
callCHCMax cfg query = do
  (_, stdout, _) <- readProcessWithExitCode (chcMaxScript cfg) [show (chcMaxTimeOut cfg)] query
  pure stdout

encodeFP :: Variables -> Symbol -> Term -> Term -> String
encodeFP vars fpPred init rec =
  unlines
    [ "(set-logic HORN)"
    , "(declare-fun "
        ++ fpPred
        ++ "("
        ++ concatMap ((" " ++) . s2Term . Vars.sortOf vars) (Vars.stateVarL vars)
        ++ ") Bool)"
    , "(assert " ++ smtLib2 init ++ ")"
    , "(assert " ++ smtLib2 rec ++ ")"
    , "(check-sat)"
    ]

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
        FPID "true" -> pure true
        FPID "false" -> pure false
        FPID ('-':cs) ->
          case readMaybe cs of
            Just k -> pure $ Const (CInt (-k))
            Nothing -> Left $ "Found illegal identifier: " ++ cs
        FPID (c:cs)
          | isDigit c ->
            case readMaybe (c : cs) of
              Just k -> pure $ Const (CInt k)
              Nothing -> Left $ "Found illegal identifier: " ++ (c : cs)
          | otherwise ->
            case varMap !? (c : cs) of
              Just (v, sort) -> pure $ Var v sort
              Nothing -> Left $ "Found unknown identifier: " ++ (c : cs)
        FPBop op e1 e2 -> do
          t1 <- go e1
          t2 <- go e2
          case op of
            "/\\" -> pure $ andf [t1, t2]
            "\\/" -> pure $ orf [t1, t2]
            "=" -> pure $ equal t1 t2
            "!=" -> pure $ neg (equal t1 t2)
            "<=" -> pure $ leqT t1 t2
            ">=" -> pure $ geqT t1 t2
            "+" -> pure $ leqT t1 t2
                                        -- TODO: More operators
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
