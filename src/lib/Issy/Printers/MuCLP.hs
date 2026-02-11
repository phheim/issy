---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Printers.MuCLP
-- Description : MuCLP format printer
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements printing to the nested-fixpoint-equations format by MuVal/Coar.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Printers.MuCLP
  ( printMuCLP
  ) where

---------------------------------------------------------------------------------------------------
import Data.Fixed (Nano, showFixed)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Encoders.ToFixpoints (FPSystem(..), FPTerm(..), FPType(..))
import Issy.Logic.FOL (Constant(..), Quantifier(..), Sort(..), Term(..))
import qualified Issy.Logic.FOL as FOL
import Issy.Printers.SMTLib (funcToString)

---------------------------------------------------------------------------------------------------
-- | Prints a fixpoint system into MuVals/Coars MuCLP fixpoint format (.hes files). Since of
-- now this format does not support all kinds of functions Issy does, this method my be
-- undefined in some cases, that might change pretty quickly. Furthermore, as the MuCLP format
-- does not have booleans, those are currenlty encoded with integers. Overall, this methods
-- should not be considered to be very stable.
printMuCLP :: FPSystem -> String
printMuCLP fpSystem =
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
   in name
        ++ concatMap (\(v, s) -> "(" ++ v ++ ": " ++ encSort s ++ ")") (fpSignature fpeq)
        ++ ": bool ="
        ++ fpop
        ++ " "
        ++ encTerm (term fpeq)
        ++ ";"

encTerm :: Term -> String
encTerm term =
  let qpref = FOL.unusedPrefix "qvar" term
   in encTermF (qpref, 0, Set.empty) False term

encTermF :: (String, Int, Set Int) -> Bool -> Term -> String
encTermF (qpref, qdepth, bvars) funarg =
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
        FOL.CustomF name _ _ -> "(" ++ name ++ concatMap ((" " ++) . recT) args ++ ")"
        FOL.FOr -> encOp rec "\\/" "false" args
        FOL.FAnd -> encOp rec "/\\" "true" args
        FOL.FNot -> "(not " ++ rec (head args) ++ ")"
        FOL.FAdd -> encOp rec "+" "0" args
        FOL.FMul -> encOp rec "*" "1" args
        FOL.FDivReal ->
          case args of
            [Const (CInt c1), Const (CInt c2)] -> encConst funarg (CReal (c1 % c2))
            _ -> error "'/' only supported for constants"
        FOL.FIte
          | funarg -> error "ite in function argument not supported yet"
          | otherwise ->
            case args of
              [c, t, e] -> rec $ FOL.orf [FOL.andf [c, t], FOL.andf [FOL.neg c, e]]
              _ -> error "assert: 'ite' should have exactly three arguments"
        f
          | f `elem` [FOL.FEq, FOL.FLt, FOL.FLte] -> binOp (funcToString f) args
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
    rec = encTermF (qpref, qdepth, bvars) funarg
    recT = encTermF (qpref, qdepth, bvars) True
    recNest SBool = encTermF (qpref, qdepth + 1, Set.insert qdepth bvars) funarg
    recNest _ = encTermF (qpref, qdepth + 1, bvars) funarg
    --
    binOp :: String -> [Term] -> String
    binOp op =
      \case
        [o1, o2] -> "(" ++ recT o1 ++ " " ++ op ++ " " ++ recT o2 ++ ")"
        _ -> error (op ++ "is a binary operator")

encOp :: (a -> String) -> String -> String -> [a] -> String
encOp encA op neut =
  \case
    [] -> neut
    [x] -> "(" ++ encA x ++ ")"
    x:xr -> "(" ++ encA x ++ " " ++ op ++ " " ++ encOp encA op neut xr ++ ")"

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

encSort :: Sort -> String
encSort =
  \case
    SInt -> "int"
    SBool -> "int"
    SReal -> "real"
    SFunc _ _ -> error "Function types not supported"
---------------------------------------------------------------------------------------------------
