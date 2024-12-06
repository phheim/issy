{-# LANGUAGE LambdaCase #-}

module Issy.Printers.SMTLib
  ( smtLib2
  , toSMTLib2
  , s2Term
  ) where

import qualified Data.Map as Map (toList)
import Data.Ratio (denominator, numerator)

import Issy.Logic.FOL

--
-- Quantified Variable Naming
--
-- To name quantified variables we track the current nesting depth DEPTH 
-- of the quantifiers and a unique name prefix. For each quantifier 
-- the variable is names PREFIX ++ DEPTH. So given a de-Brunijn index I
-- the variables name is PREFIX ++ (DEPTH - I)
--
s2Term :: Sort -> String
s2Term =
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
    Func f args ->
      let fun =
            case f of
              UnintF name -> name
              PredefF name -> name
              CustomF name _ _ -> name
       in "(" ++ fun ++ concatMap ((" " ++) . t2Term a) args ++ ")"
    Const (CInt n)
      | n >= 0 -> show n
      | otherwise -> "(- " ++ show (-n) ++ ")"
    Const (CReal r) -> "(/ " ++ show (numerator r) ++ " " ++ show (denominator r) ++ ")"
    Const (CBool b)
      | b -> "true"
      | otherwise -> "false"
  where
    hQwant t f =
      fst a ++ show (snd a) ++ " " ++ s2Term t ++ ")) " ++ t2Term (fst a, snd a + 1) f ++ ")"

smtLib2 :: Term -> String
smtLib2 f = t2Term (unusedPrefix "qv" f ++ "x", 0) f

toSMTLib2 :: Term -> String
toSMTLib2 f =
  concatMap
    (\(v, t) ->
       case t of
         SFunc sargs starg ->
           "(declare-fun "
             ++ v
             ++ " ("
             ++ concatMap ((" " ++) . s2Term) sargs
             ++ " ) "
             ++ s2Term starg
             ++ ")"
         _ -> "(declare-const " ++ v ++ " " ++ s2Term t ++ ")")
    (Map.toList (bindings f))
    ++ "(assert "
    ++ smtLib2 f
    ++ ")"
