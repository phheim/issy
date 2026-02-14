---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Encoders.TSLT
-- Description : Encode to Raboniel's TSLT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements an encoding of
-- a reactive program game to TSLMT and print it as Raboniels TSLT format variant.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Encoders.TSLT
  ( rpgToTSLT
  ) where

---------------------------------------------------------------------------------------------------
import Data.Fixed (Nano, showFixed)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Games.Locations (Loc)
import qualified Issy.Games.Locations as Locs
import Issy.Games.Objectives (Objective(..), WinningCondition(..))
import Issy.Games.ReactiveProgramArena (RPArena, Transition(..))
import qualified Issy.Games.ReactiveProgramArena as RPG
import qualified Issy.Games.Variables as Vars
import Issy.Logic.FOL (Constant(..), Function(..), Sort(..), Symbol, Term(..))

---------------------------------------------------------------------------------------------------
sortOf :: RPArena -> Symbol -> Sort
sortOf = Vars.sortOf . RPG.variables

encConst :: Bool -> Constant -> String
encConst upd =
  \case
    CInt n
      | n < 0 -> "(sub i0() " ++ encConst upd (CInt (-n)) ++ ")"
      | otherwise -> "i" ++ show n ++ "()"
    CReal r
      | r < 0 -> "(sub r0.0() " ++ encConst upd (CReal (-r)) ++ ")"
      | otherwise -> "r" ++ showFixed True (fromRational r :: Nano) ++ "()"
    CBool True
      | upd -> "i1()"
      | otherwise -> "true"
    CBool False
      | upd -> "i0()"
      | otherwise -> "false"

encOp :: (a -> String) -> String -> String -> [a] -> String
encOp encA op neut =
  \case
    [] -> neut
    [x] -> "(" ++ encA x ++ ")"
    x:xr -> "(" ++ encA x ++ " " ++ op ++ " " ++ encOp encA op neut xr ++ ")"

encVar :: Bool -> Symbol -> Sort -> String
encVar check v =
  \case
    SBool
      | check -> "(eq i_" ++ v ++ " i1())"
      | otherwise -> "i_" ++ v
    SInt -> "i_" ++ v
    SReal -> "r_" ++ v
    _ -> error "Not supported"

encTerm :: Bool -> Term -> String
encTerm upd =
  \case
    QVar _ -> error "Not supported"
    Quant {} -> error "Not supported"
    Lambda _ _ -> error "Not supported"
    Var v s -> encVar True v s
    Const c -> encConst upd c
    Func n args
      | n == FOr && not upd -> encOp (encTerm upd) "||" "false" args
      | n == FAnd && not upd -> encOp (encTerm upd) "&&" "true" args
      | n == FNot && not upd -> "(! " ++ encTerm upd (head args) ++ ")"
      | n == FAdd ->
        if length args <= 2
          then op "add" args
          else "(add "
                 ++ encTerm upd (head args)
                 ++ " "
                 ++ encTerm upd (Func FAdd (tail args))
                 ++ ")"
      | n == FEq -> op "eq" args
      | n == FLt -> op "lt" args
      | n == FLte -> op "le" args
      | n == FMul -> op "mul" args
      | otherwise -> error (show n ++ " not supported yet")
  where
    op name args = "(" ++ name ++ concatMap ((" " ++) . encTerm upd) args ++ ")"

encLoc :: RPArena -> Loc -> String
encLoc _ l = "[loc  <- i" ++ show (Locs.toNumber l) ++ "()]"

encTrans :: RPArena -> Transition -> String
encTrans g =
  \case
    TIf p tt tf ->
      let encP = encTerm False p
       in "("
            ++ encP
            ++ " -> "
            ++ encTrans g tt
            ++ ") && ((! "
            ++ encP
            ++ " ) -> "
            ++ encTrans g tf
            ++ ")"
    TSys upds -> concatMap ((++ " || ") . encUpd) upds ++ "false"
  where
    encUpd (u, l) =
      "("
        ++ concatMap
             (\(v, t) -> "[" ++ encVar False v (sortOf g v) ++ " <- " ++ encTerm True t ++ "] && ")
             (Map.toList u)
        ++ "X "
        ++ encLoc g l
        ++ ")"

encState :: RPArena -> String
encState g =
  "//-- State: "
    ++ concatMap (\v -> encVar False v (sortOf g v) ++ ", ") (Vars.stateVarL (RPG.variables g))
    ++ "loc"

encInputs :: RPArena -> String
encInputs g =
  case Vars.inputL (RPG.variables g) of
    [] -> ""
    i:ir -> "//-- Inputs: " ++ encV i ++ concatMap ((", " ++) . encV) ir
  where
    encV v = encVar False v (sortOf g v)

encGame :: Loc -> RPArena -> String
encGame init g =
  unlines
    $ [ encState g
      , encInputs g
      , "guarantee {"
      , encTerm False (RPG.inv g init)
      , " -> "
      , encLoc g init ++ ";"
      ]
        ++ map
             (\l ->
                "G ("
                  ++ encLoc g l
                  ++ " -> "
                  ++ encTerm False (RPG.inv g l)
                  ++ " && ("
                  ++ encTrans g (RPG.trans g l)
                  ++ "));")
             (Set.toList (RPG.locations g))
        ++ ["}"]

encCond :: RPArena -> String -> Set Loc -> String
encCond g op loc =
  let locs = Set.toList loc
   in "guarantee { " ++ op ++ "(" ++ concatMap (\l -> encLoc g l ++ " || ") locs ++ "false);}"

-- | Encode an reactive program game to TSLMT and print it in Raboniel's format variant.
rpgToTSLT :: RPArena -> Objective -> String
rpgToTSLT g obj =
  unlines
    [ encGame (initialLoc obj) g
    , case winningCond obj of
        Reachability reach -> encCond g "F" reach
        Safety safe -> encCond g "G" safe
        Buechi fset -> encCond g "G F" fset
        CoBuechi fset -> encCond g "F G" fset
        _ -> error "Not supported"
    ]
---------------------------------------------------------------------------------------------------
