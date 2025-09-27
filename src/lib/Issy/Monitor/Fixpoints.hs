{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Monitor.Fixpoints
  ( checkFPInclusion
  ) where

import Data.Fixed (Nano, showFixed)
import qualified Data.Set as Set
import Issy.Prelude
import System.Process (readProcessWithExitCode)

import qualified Issy.Base.Variables as Vars
import Issy.Config (muvalScript, muvalTimeOut)
import Issy.Logic.FOL (Constant(..), Quantifier(..), Sort(..), Term(..))
import qualified Issy.Logic.FOL as FOL
import Issy.Printers.SMTLib (funcToString)
import Issy.Utils.Extra (firstLine)

encSort :: Sort -> String
encSort =
  \case
    SInt -> "int"
    SBool -> "int"
    SReal -> "real"
    SFunc _ _ -> error "Function types not supported"

encConst :: Bool -> Constant -> String
encConst funarg =
  \case
    CInt n -> show n
    CReal r -> addDot $ showFixed True (fromRational r :: Nano)
    CBool True
      | funarg -> "1"
      | otherwise -> "(0 = 0)"
    CBool False
      | funarg -> "0"
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

encTerm :: Symbol -> (String, Int, Set Int) -> Bool -> Term -> String
encTerm fpPred (qpref, qdepth, bvars) funarg =
  \case
    Var v s
      | s == SBool && not funarg -> "(" ++ v ++ " = 1)"
      | s == SBool && funarg -> v
      | otherwise -> v
    Const c -> encConst funarg c
    QVar k
      | qdepth - k - 1 `elem` bvars && not funarg ->
        "(" ++ qpref ++ show (qdepth - k - 1) ++ " = 1)"
      | otherwise -> qpref ++ show (qdepth - k - 1)
    Func f args ->
      case f of
        FOL.CustomF name _ _
          | name == fpPred -> fpPred ++ concatMap ((" " ++) . recT) args
          | otherwise -> error "assert: cannot use non-fixpoint uninterpreted function"
        FOL.FOr -> encOp rec "\\/" "false" args
        FOL.FAnd -> encOp rec "/\\" "true" args
        FOL.FNot -> "(not " ++ rec (head args) ++ ")"
        FOL.FAdd -> encOp rec "+" "0" args
        FOL.FDivReal ->
          case args of
            [Const (CInt c1), Const (CInt c2)] -> encConst funarg (CReal (c1 % c2))
            _ -> error "'/' only supported for constants"
        f
          | f `elem` [FOL.FMul, FOL.FEq, FOL.FLt, FOL.FLte] -> binOp (funcToString f) args
          | otherwise -> error (funcToString f ++ " not supported yet")
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
    rec = encTerm fpPred (qpref, qdepth, bvars) funarg
    recT = encTerm fpPred (qpref, qdepth, bvars) True
    recNest SBool = encTerm fpPred (qpref, qdepth + 1, Set.insert qdepth bvars) funarg
    recNest _ = encTerm fpPred (qpref, qdepth + 1, bvars) funarg
    --
    binOp :: String -> [Term] -> String
    binOp op =
      \case
        [o1, o2] -> "(" ++ recT o1 ++ " " ++ op ++ " " ++ recT o2 ++ ")"
        _ -> error (op ++ "is a binary operator")

encFPInclusion :: Variables -> Term -> Symbol -> Term -> String
encFPInclusion vars query fpPred fp =
  let qPref =
        FOL.uniquePrefix "qvar"
          $ Set.unions [FOL.symbols query, FOL.symbols fp, Vars.allSymbols vars]
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
