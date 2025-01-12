{-# LANGUAGE LambdaCase #-}

module Issy.Printers.RPG
  ( printRPG
  ) where

import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Issy.Base.Locations as Locs
import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import qualified Issy.Base.Variables as Vars
import Issy.Logic.FOL
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.RPG

printSort :: Sort -> String
printSort =
  \case
    SInt -> "Int"
    SBool -> "Bool"
    SReal -> "Real"
    SFunc _ _ -> error "function sort not allowed for game writing"

printWC :: WinningCondition -> String
printWC =
  \case
    Safety _ -> "Safety"
    Reachability _ -> "Reach"
    Buechi _ -> "Buechi"
    CoBuechi _ -> "coBuechi"
    Parity _ -> "Parity"

printTrans :: (Loc -> String) -> Transition -> String
printTrans wl =
  \case
    TIf p tt tf ->
      "if " ++ SMTLib.toString p ++ " then " ++ printTrans wl tt ++ " else " ++ printTrans wl tf
    TSys choices -> "sys( " ++ concatMap wSys choices ++ ")"
  where
    wUpd (s, t) = "(" ++ s ++ " " ++ SMTLib.toString t ++ ")"
    wSys (upd, l) = "(" ++ concatMap wUpd (Map.toList upd) ++ ") " ++ wl l ++ " "

printRPG :: (Game, Objective) -> String
printRPG (g, obj) =
  unlines
    $ ["type " ++ printWC (winningCond obj), ""]
        ++ ["output " ++ o ++ " " ++ wty o | o <- Vars.stateVarL (variables g)]
        ++ ["input " ++ i ++ " " ++ wty i | i <- Vars.inputL (variables g)]
        ++ [""]
        ++ ["loc " ++ ln l ++ " " ++ ac l ++ " ; " ++ show l | l <- locl]
        ++ [""]
        ++ ["init " ++ ln (initialLoc obj)]
        ++ [""]
        ++ ["trans " ++ ln l ++ " " ++ printTrans ln (trans g l) | l <- locl]
  where
    locl = Set.toList (locations g)
    wty x = " " ++ printSort (Vars.sortOf (variables g) x)
    ln = Locs.toString (locationSet g)
    em s l
      | l `elem` s = "1"
      | otherwise = "0"
    ac =
      case winningCond obj of
        Safety s -> em s
        Reachability s -> em s
        Buechi s -> em s
        CoBuechi s -> em s
        Parity rank -> show . (rank !)
