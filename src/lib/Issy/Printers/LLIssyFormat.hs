{-# LANGUAGE LambdaCase #-}

module Issy.Printers.LLIssyFormat
  ( printLLIssyFormat
  ) where

import Data.Map.Strict ((!))

import Issy.Base.Locations (Loc)
import qualified Issy.Base.Locations as Locs
import Issy.Base.Objectives (Objective)
import qualified Issy.Base.Objectives as Obj
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.Temporal as TL
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Specification (Specification)
import qualified Issy.Specification as Spec
import qualified Issy.SymbolicArena as SG

printLLIssyFormat :: Specification -> String
printLLIssyFormat spec =
  ps
    [ printVars (Spec.variables spec)
    , mps printFSpec (Spec.formulas spec)
    , mps printGame (Spec.games spec)
    ]

printVars :: Variables -> String
printVars vars =
  mps
    (\v ->
       case Vars.typeOf vars v of
         Vars.TInput sort -> "(input " ++ printSort sort ++ " " ++ v ++ ")\n"
         Vars.TOutput sort -> "(state " ++ printSort sort ++ " " ++ v ++ ")\n")
    $ Vars.inputL vars ++ Vars.stateVarL vars

printSort :: FOL.Sort -> String
printSort =
  \case
    FOL.SBool -> "Bool"
    FOL.SInt -> "Int"
    FOL.SReal -> "Real"
    _ -> error "assert: function types should not appear here"

printFSpec :: TL.Spec FOL.Term -> String
printFSpec spec =
  ps
    [ mps (("\n" ++) . printFormula) (TL.assumptions spec)
    , mps (("\n" ++) . printFormula) (TL.guarantees spec)
    ]

printFormula :: TL.Formula FOL.Term -> String
printFormula = go
  where
    ops op =
      \case
        [] -> "(" ++ op ++ ")"
        [x] -> "(" ++ op ++ " " ++ go x ++ ")"
        x:xr -> "(" ++ op ++ " " ++ go x ++ concatMap ((" " ++) . go) xr ++ ")"
    go =
      \case
        TL.Atom ap -> "(ap " ++ printTerm ap ++ ")"
        TL.And fs -> ops "and" fs
        TL.Or fs -> ops "or" fs
        TL.Not f -> ops "not" [f]
        TL.UExp TL.Next f -> ops "X" [f]
        TL.UExp TL.Globally f -> ops "G" [f]
        TL.UExp TL.Eventually f -> ops "F" [f]
        TL.BExp TL.Until f g -> ops "U" [f, g]
        TL.BExp TL.WeakUntil f g -> ops "W" [f, g]
        TL.BExp TL.Release f g -> ops "R" [f, g]

printGame :: (SG.Arena, Objective) -> String
printGame (arena, obj) =
  let locs = SG.locations arena
   in ps
        [ mps
            (\l ->
               "("
                 ++ Locs.toString locs l
                 ++ " "
                 ++ printRank obj l
                 ++ " "
                 ++ printTerm (SG.domain arena l)
                 ++ ")\n")
            $ Locs.toList locs
        , mps
            (\(l, l', term) ->
               "("
                 ++ Locs.toString locs l
                 ++ " "
                 ++ Locs.toString locs l'
                 ++ " "
                 ++ printTerm term
                 ++ ")\n")
            $ SG.transList arena
        , "(" ++ Locs.toString locs (Obj.initialLoc obj) ++ " " ++ printWC obj ++ ")"
        ]

printWC :: Objective -> String
printWC obj =
  case Obj.winningCond obj of
    Obj.Safety _ -> "Safety"
    Obj.Reachability _ -> "Reachability"
    Obj.Buechi _ -> "Buechi"
    Obj.CoBuechi _ -> "CoBuechi"
    Obj.Parity _ -> "ParityMaxOdd"

printRank :: Objective -> Loc -> String
printRank obj l =
  case Obj.winningCond obj of
    Obj.Safety fs -> toNum fs
    Obj.Reachability fs -> toNum fs
    Obj.Buechi fs -> toNum fs
    Obj.CoBuechi fs -> toNum fs
    Obj.Parity col -> show $ col ! l
  where
    toNum fs
      | l `elem` fs = "1"
      | otherwise = "0"

printTerm :: FOL.Term -> String
printTerm = SMTLib.toString

mps :: (a -> String) -> [a] -> String
mps f = ps . map f

ps :: [String] -> String
ps subs =
  case subs of
    [] -> "()\n"
    es -> "(\n" ++ indent (concat es) ++ ")\n"

indent :: String -> String
indent = unlines . map ("  " ++) . lines
