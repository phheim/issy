---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Encoders.Sweap
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Encoders.Sweap
  ( specToSweap
  ) where

import Issy.Prelude

import Issy.Encoders.ToFormula (toFormula)
import qualified Issy.Games.Variables as Vars
import Issy.Logic.FOL (Constant(..), Function(..), Sort(..), Term(..))
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.Temporal (BOp(..), Formula(..), UOp(..))
import qualified Issy.Logic.Temporal as TL
import Issy.Specification (Specification)
import Issy.Utils.Extra (enclose, paraInbetween)

specToSweap :: Specification -> String
specToSweap = uncurry formulaToSweap . toFormula

formulaToSweap :: Variables -> TL.Formula Term -> String
formulaToSweap vars formula =
  unlines
    $ concat
        [ ["program encoded {"]
        , encStates vars
        , envEvents
        , sysEvents
        , encVarDec vars
        , encTrans vars
        , encFormula vars formula
        , ["}"]
        ]

encStates :: Variables -> [String]
encStates vars =
  ["STATES {", "evaled: init,", "eval_soon,", "fail_sys,", "fail_env,"]
    ++ map ((++ ",") . stateChangeVar) (Vars.inputL vars ++ Vars.stateVarL' vars)
    ++ ["}"]

stateChangeVar :: Symbol -> String
stateChangeVar = ("change_" ++) . Vars.unprime

envEvents :: [String]
envEvents = ["ENVIRONMENT EVENTS {", "eval_env, next_var_env, add_var_env", "}"]

sysEvents :: [String]
sysEvents = ["CONTROLLER EVENTS {", "eval_sys, next_var_sys, add_var_sys", "}"]

encVarDec :: Variables -> [String]
encVarDec vars =
  ["VALUATION {"]
    ++ map enc (Vars.inputL vars)
    ++ map enc (Vars.stateVarL vars)
    ++ map enc (Vars.stateVarL' vars)
    ++ ["}"]
  where
    enc var = encVar vars var ++ encSort (Vars.sortOf vars var)
    encSort :: Sort -> String
    encSort =
      \case
        SBool -> " : bool := true;"
        SInt -> " : integer := 0;"
        _ -> error "only bools and integers work in sweap"

encVar :: Variables -> Symbol -> String
encVar vars var
  | Vars.isInput vars var = "i_" ++ var
  | Vars.isStateVar vars var = "s_" ++ var
  | Vars.isStateVar vars (Vars.unprime var) = "sp_" ++ Vars.unprime var
  | otherwise = error "assert: unkown variable"

encTrans :: Variables -> [String]
encTrans vars =
  [ "TRANSITIONS {"
  , tenc "eval_soon" "evaled" "eval_sys & eval_env" ""
  , tenc "eval_soon" "fail_sys" "!eval_sys" ""
  , tenc "eval_soon" "fail_env" "eval_sys & !eval_env" ""
  , tenc "evaled" first_state "!eval_sys & !eval_env" encCopy
  , tenc "evaled" "fail_sys" "eval_sys" ""
  , tenc "evaled" "fail_env" "!eval_sys & eval_env" ""
  ]
    ++ concatMap (uncurry (encTransFor vars)) (zip varsToEncode nextStates)
    ++ ["fail_sys -> fail_sys [],", "fail_env -> fail_env []"]
    ++ ["}"]
  where
    varsToEncode = Vars.inputL vars ++ Vars.stateVarL' vars
    first_state = stateChangeVar $ head varsToEncode
    nextStates = map stateChangeVar (tail varsToEncode) ++ ["eval_soon"]
    encCopy = concatMap encCopyVar $ Vars.stateVarL vars
    encCopyVar var = encVar vars var ++ " := " ++ encVar vars (Vars.prime var) ++ ";"

encTransFor :: Variables -> Symbol -> String -> [String]
encTransFor vars var next_state =
  [ tenc state state (noteval ++ " &  " ++ addvar ++ "& !" ++ nextvar) addVar
  , tenc state state (noteval ++ " & !" ++ addvar ++ "& !" ++ nextvar) subVar
  , tenc state next_state (noteval ++ " & " ++ nextvar) ""
  , tenc state ("fail" ++ moveOf) ("eval" ++ moveOf) ""
  ]
  where
    noteval = "!eval" ++ moveOf
    addvar = "add_var" ++ moveOf
    nextvar = "next_var" ++ moveOf
    moveOf
      | Vars.isInput vars var = "_env"
      | otherwise = "_sys"
    state = stateChangeVar var
    varEnc = encVar vars var
    sort = Vars.sortOf vars var
    addVar
      | sort == FOL.SBool = varEnc ++ " := true"
      | otherwise = varEnc ++ " := " ++ varEnc ++ " + 1"
    subVar
      | sort == FOL.SBool = varEnc ++ " := false"
      | otherwise = varEnc ++ " := " ++ varEnc ++ " - 1"

-- | Generic transition encoding function
tenc :: String -> String -> String -> String -> String
tenc src trg cond effect = src ++ " -> " ++ trg ++ " [ " ++ cond ++ " $ " ++ effect ++ " ],"

encFormula :: Variables -> TL.Formula Term -> [String]
encFormula vars formula =
  [ "SPECIFICATION {"
  , "((F fail_env) || (F G !eval_env) || ((G !fail_sys) && (G F eval_sys) && "
  , encFormulaTerm vars formula
  , "))"
  , "}"
  ]

-- Boolean are applied pointwise
-- [ap]     := !eval U (eval && [ap])
-- [X t]    := !eval U (eval && X [t])
-- [a U b]  := (!eval || a) U (eval && b)
-- [F t]    := F (eval && t)
-- [G t]    := G (!eval || t)
encFormulaTerm :: Variables -> TL.Formula Term -> String
encFormulaTerm vars = go
  where
    eval = "(eval_sys && eval_env)"
    notEvalU t = "((!" ++ eval ++ ") U (" ++ eval ++ "&&(" ++ t ++ ")))"
    go =
      \case
        Atom t -> notEvalU $ encTerm vars t
        And [] -> "true"
        And [f] -> go f
        And fs -> paraInbetween " && " $ map go fs
        Or [] -> "false"
        Or [f] -> go f
        Or fs -> paraInbetween " || " $ map go fs
        Not f -> enclose '(' $ "! " ++ go f
        UExp Next f -> notEvalU $ "X " ++ go f
        UExp Globally f -> "(G (!" ++ eval ++ ") || " ++ go f ++ ")"
        UExp Eventually f -> "(F " ++ eval ++ " && " ++ go f ++ ")"
        BExp Until f g ->
          "(((!" ++ eval ++ ") || " ++ go f ++ ") U (" ++ eval ++ " && " ++ go g ++ "))"
        BExp WeakUntil f g -> go $ Or [BExp Until f g, UExp Globally f]
        BExp Release f g -> go $ BExp WeakUntil g (And [f, g])

encTerm :: Variables -> Term -> String
encTerm vars = go
  where
    go =
      \case
        Var var _ -> encVar vars var
        Const (CInt n) -> show n
        Const (CBool b)
          | b -> "true"
          | otherwise -> "false"
        Const _ -> error "only ints and bools supported"
        Func FAdd fs -> paraInbetween " + " $ map go fs
        Func FMul [Const (CInt a), Const (CInt b)] -> show $ a * b
        Func FMul [t, Const (CInt c)] -> go $ Func FMul [Const (CInt c), t]
        Func FMul [Const (CInt c), t]
          | c == 0 -> "0"
          | c < 0 -> "(0 - " ++ go (Func FMul [Const (CInt (-c)), t]) ++ ")"
          | otherwise -> go $ Func FAdd [t, Func FMul [Const (CInt (c - 1)), t]]
        Func FMul _ -> error "asser: other forms of multiplication are not supported here"
        Func FAnd fs -> paraInbetween " && " $ map go fs
        Func FOr fs -> paraInbetween " || " $ map go fs
        Func FNot [f] -> "(!" ++ go f ++ ")"
        Func FEq [a, b] -> "(" ++ go a ++ " == " ++ go b ++ ")"
        Func FLt [a, b] -> "(" ++ go a ++ " < " ++ go b ++ ")"
        Func FLte [a, b] -> "(" ++ go a ++ " <= " ++ go b ++ ")"
        Func _ _ -> error "assert: other function patterns are not supported for sweap"
        QVar _ -> error "for now we do not support quantifiers here"
        Quant {} -> error "for now we do not support quantifiers here"
        Lambda _ _ -> error "for now we do not support lambdas here"
---------------------------------------------------------------------------------------------------
