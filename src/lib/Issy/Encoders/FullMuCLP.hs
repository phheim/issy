{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Encoders.FullMuCLP
  ( fpToMuCLP
  ) where

import Data.Fixed (Nano, showFixed)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Encoders.ToFixpoints (FPSystem(..), FPTerm(..), FPType(..))
import Issy.Logic.FOL (Constant(..), Quantifier(..), Sort(..), Term(..))
import qualified Issy.Logic.FOL as FOL
import Issy.Printers.SMTLib (funcToString)

fpToMuCLP :: FPSystem -> String
fpToMuCLP fpSystem =
  unlines
    $ encTerm (systemTerm fpSystem)
        : "s.t."
        : map (uncurry encFPTerm) (Map.toList (fpTerms fpSystem))

encFPTerm :: Symbol -> FPTerm -> String
encFPTerm name fpeq =
  let fpop =
        case fpType fpeq of
          GFP -> "nu"
          LFP -> "mu"
   in name ++ ": bool =" ++ fpop ++ " " ++ encTerm (term fpeq) ++ ";"

encTerm :: Term -> String
encTerm = error "TODO: copy, adapt, and improve from Monitor.Fixpoint"

encTermF :: Symbol -> (String, Int, Set Int) -> Bool -> Term -> String
encTermF fpPred (qpref, qdepth, bvars) funarg =
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
    rec = encTermF fpPred (qpref, qdepth, bvars) funarg
    recT = encTermF fpPred (qpref, qdepth, bvars) True
    recNest SBool = encTermF fpPred (qpref, qdepth + 1, Set.insert qdepth bvars) funarg
    recNest _ = encTermF fpPred (qpref, qdepth + 1, bvars) funarg
    --
    binOp :: String -> [Term] -> String
    binOp op =
      \case
        [o1, o2] -> "(" ++ recT o1 ++ " " ++ op ++ " " ++ recT o2 ++ ")"
        _ -> error (op ++ "is a binary operator")

-- TODO: duplicate in Monitor.Fixpoints
encOp :: (a -> String) -> String -> String -> [a] -> String
encOp encA op neut =
  \case
    [] -> neut
    [x] -> "(" ++ encA x ++ ")"
    x:xr -> "(" ++ encA x ++ " " ++ op ++ " " ++ encOp encA op neut xr ++ ")"

-- TODO: duplicate in Monitor.Fixpoints
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

-- TODO: duplicate in Monitor.Fixpoints
encSort :: Sort -> String
encSort =
  \case
    SInt -> "int"
    SBool -> "int"
    SReal -> "real"
    SFunc _ _ -> error "Function types not supported"
