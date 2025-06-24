---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Printers.SMTLib
  ( toString
  , toQuery
  , funcToString
  , sortToString
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map as Map (toList)
import Data.Ratio (denominator, numerator)

import Issy.Logic.FOL (Constant(..), Function(..), Quantifier(..), Sort(..), Term(..))
import qualified Issy.Logic.FOL as FOL

---------------------------------------------------------------------------------------------------
-- Quantified Variable Naming
--
-- To name quantified variables we track the current nesting depth DEPTH 
-- of the quantifiers and a unique name prefix. For each quantifier 
-- the variable is names PREFIX ++ DEPTH. So given a de-Brunijn index I
-- the variables name is PREFIX ++ (DEPTH - I)
---------------------------------------------------------------------------------------------------
toString :: Term -> String
toString f = t2Term (FOL.unusedPrefix "qv" f ++ "x", 0) f

toQuery :: Term -> String
toQuery f =
  concatMap
    (\(v, t) ->
       case t of
         SFunc sargs starg ->
           "(declare-fun "
             ++ v
             ++ " ("
             ++ concatMap ((" " ++) . sortToString) sargs
             ++ " ) "
             ++ sortToString starg
             ++ ")"
         _ -> "(declare-const " ++ v ++ " " ++ sortToString t ++ ")")
    (Map.toList (FOL.bindings f))
    ++ "(assert "
    ++ toString f
    ++ ")"

---------------------------------------------------------------------------------------------------
sortToString :: Sort -> String
sortToString =
  \case
    SBool -> "Bool"
    SInt -> "Int"
    SReal -> "Real"
    _ -> error "No real sorttype for functions exists"

t2Term :: (String, Int) -> Term -> String
t2Term a =
  \case
    Var v _ -> v
    QVar n ->
      let i = snd a - n - 1 -- -1 as we are nested inside the quantifier
       in if i < 0
            then error "Assertion: Unknown deBrunijn index"
            else fst a ++ show i
    Quant Forall t f -> "(forall ((" ++ hQwant t f
    Quant Exists t f -> "(exists ((" ++ hQwant t f
    Lambda t f -> "(lambda ((" ++ hQwant t f --FIXME: This is non-standard!
    Func f args -> "(" ++ funcToString f ++ concatMap ((" " ++) . t2Term a) args ++ ")"
    Const (CInt n)
      | n >= 0 -> show n
      | otherwise -> "(- " ++ show (-n) ++ ")"
    Const (CReal r) -> "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    Const (CBool b)
      | b -> "true"
      | otherwise -> "false"
  where
    hQwant t f =
      fst a ++ show (snd a) ++ " " ++ sortToString t ++ ")) " ++ t2Term (fst a, snd a + 1) f ++ ")"

funcToString :: Function -> String
funcToString =
  \case
    CustomF name _ _ -> name
    FAnd -> "and"
    FOr -> "or"
    FNot -> "not"
    FDistinct -> "distinct"
    FImply -> "=>"
    FIte -> "ite"
    FAdd -> "+"
    FSub -> "-"
    FMul -> "*"
    FDivReal -> "/"
    FEq -> "="
    FLt -> "<"
    FGt -> ">"
    FLte -> "<="
    FGte -> ">="
    FAbs -> "abs"
    FToReal -> "to_real"
    FMod -> "mod"
    FDivInt -> "div"
---------------------------------------------------------------------------------------------------
