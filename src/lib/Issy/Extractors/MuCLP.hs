{-# LANGUAGE LambdaCase #-}

module Issy.Extractors.MuCLP
  ( rpgToMuCLP
  ) where

import Data.Fixed (Nano, showFixed)
import Data.Map ((!?))
import Data.Ratio ((%))
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Locations (Loc)
import qualified Issy.Base.Locations as Locs
import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import qualified Issy.Base.Variables as Vars
import Issy.Logic.FOL (Constant(..), Function(..), Sort(..), Symbol, Term(..))
import Issy.RPG (Game, Transition(..))
import qualified Issy.RPG as RPG

outputs :: Game -> [Symbol]
outputs = Vars.stateVarL . RPG.variables

inputs :: Game -> [Symbol]
inputs = Vars.inputL . RPG.variables

sortOf :: Game -> Symbol -> Sort
sortOf = Vars.sortOf . RPG.variables

encSort :: Sort -> String
encSort =
  \case
    SInt -> "int"
    SBool -> "int"
    SReal -> "real"
    SFunc _ _ -> error "Function types not supported"

encConst :: Bool -> Constant -> String
encConst upd =
  \case
    CInt n -> show n
    CReal r -> addDot $ showFixed True (fromRational r :: Nano)
    CBool True
      | upd -> "1"
      | otherwise -> "true"
    CBool False
      | upd -> "0"
      | otherwise -> "false"
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

encTerm :: Bool -> Term -> String
encTerm upd =
  \case
    Var v s
      | s == SBool && not upd -> "(" ++ v ++ " = 1)"
      | s == SBool && upd -> v
      | otherwise -> v
    Const c -> encConst upd c
    QVar _ -> error "Not supported"
    Func f args ->
      case f of
        CustomF {} -> error "Not supported"
        PredefF n
          | n == "or" -> encOp (encTerm upd) "\\/" "false" args
          | n == "and" -> encOp (encTerm upd) "/\\" "true" args
          | n == "not" -> "(not " ++ encTerm upd (head args) ++ ")"
          | n == "+" -> encOp (encTerm upd) "+" "0" args
          | n == "-" && length args == 1 -> "(- " ++ encTerm upd (head args) ++ ")"
          | n `elem` ["-", "=", "<", ">", ">=", "<=", "*"] -> binOp n args
          | n == "/" ->
            case args of
              [Const (CInt c1), Const (CInt c2)] -> encConst upd (CReal (c1 % c2))
              _ -> error (n ++ " only supported for constants")
          | otherwise -> error (n ++ " not supported yet")
    Quant {} -> error "Not supported"
    Lambda _ _ -> error "Not supported"
  where
    binOp :: String -> [Term] -> String
    binOp op =
      \case
        [o1, o2] -> "(" ++ encTerm upd o1 ++ " " ++ op ++ " " ++ encTerm upd o2 ++ ")"
        _ -> error (op ++ "is a binary operator")

encPred :: Game -> String -> (Symbol -> String) -> [Symbol] -> Loc -> String
encPred _ name sToStr syms l =
  name ++ show (Locs.toNumber l) ++ concatMap (\v -> " (" ++ sToStr v ++ ")") syms

encTrans :: String -> Game -> Transition -> String
encTrans pname g =
  \case
    TIf p tt tf ->
      let pred = encTerm False p
       in "(("
            ++ pred
            ++ " /\\ "
            ++ encTrans pname g tt
            ++ ") \\/ ((not "
            ++ pred
            ++ ") /\\ "
            ++ encTrans pname g tf
            ++ "))"
    TSys upds ->
      encOp
        (\(u, l) ->
           encPred g pname (\s -> maybe s (encTerm True) (u !? s)) (outputs g) l
        )
        "\\/"
        "false"
        upds

encFullTrans :: String -> Game -> Loc -> String
encFullTrans pname g l =
  "("
    ++ (if not (null (inputs g))
          then "forall"
                 ++ concatMap (\s -> " (" ++ s ++ ": " ++ encSort (sortOf g s) ++ ")") (inputs g)
                 ++ "."
          else "")
    ++ encTrans pname g (RPG.trans g l)
    ++ ");"

encReach :: Game -> Set Loc -> Loc -> String
encReach g reach l =
  let head =
        encPred g "APred" (\s -> s ++ ": " ++ encSort (sortOf g s)) (outputs g) l ++ ": bool =mu "
   in head
        ++ (if l `elem` reach
              then "true;"
              else encPred g "APred" id (outputs g) l ++ " \\/ " ++ encFullTrans "APred" g l)

encSafe :: Game -> Set Loc -> Loc -> String
encSafe g safe l =
  let head =
        encPred g "APred" (\s -> s ++ ": " ++ encSort (sortOf g s)) (outputs g) l ++ ": bool =nu "
   in head
        ++ (if l `elem` safe
              then encPred g "APred" id (outputs g) l ++ " /\\ " ++ encFullTrans "APred" g l
              else "false;")

encBuech :: Game -> Set Loc -> Loc -> (String, String)
encBuech g fset l =
  let headGFP =
        encPred g "GPred" (\s -> s ++ ": " ++ encSort (sortOf g s)) (outputs g) l ++ ": bool =nu "
      headLFP =
        encPred g "LPred" (\s -> s ++ ": " ++ encSort (sortOf g s)) (outputs g) l ++ ": bool =mu "
   in ( headGFP ++ encPred g "LPred" id (outputs g) l ++ ";"
      , headLFP
          ++ if l `elem` fset
               then encFullTrans "GPred" g l
               else encFullTrans "LPred" g l)

encAll :: String -> Game -> Loc -> String
encAll pname g init =
  "forall "
    ++ concatMap (\s -> "(" ++ s ++ ": " ++ encSort (sortOf g s) ++ ")") (outputs g)
    ++ ". "
    ++ encPred g pname id (outputs g) init

encReachable :: Game -> Loc -> Set Loc -> String
encReachable g init reach =
  unlines (encAll "APred" g init : "s.t." : map (encReach g reach) (Set.toList (RPG.locations g)))

encSafety :: Game -> Loc -> Set Loc -> String
encSafety g init safe =
  unlines (encAll "APred" g init : "s.t." : map (encSafe g safe) (Set.toList (RPG.locations g)))

encBuechi :: Game -> Loc -> Set Loc -> String
encBuechi g init fset =
  let (gs, ls) = unzip (encBuech g fset <$> Set.toList (RPG.locations g))
   in unlines $ encAll "LPred" g init : "s.t." : gs ++ ls

rpgToMuCLP :: Game -> Objective -> String
rpgToMuCLP g obj =
  case winningCond obj of
    Reachability reach -> encReachable g (initialLoc obj) reach
    Safety safe -> encSafety g (initialLoc obj) safe
    Buechi fset -> encBuechi g (initialLoc obj) fset
    _ -> error "Winning condition not supported"
