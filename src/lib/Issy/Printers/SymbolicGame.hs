{-# LANGUAGE Safe #-}

module Issy.Printers.SymbolicGame
  ( printSG
  ) where

import Issy.Games.Objectives (Objective)
import qualified Issy.Games.SymbolicArena as SG
import Issy.Printers.LLIssyFormat (printLLIssyFormat)
import qualified Issy.Specification as Spec

printSG :: (SG.Arena, Objective) -> String
printSG = printLLIssyFormat . uncurry Spec.specFromSymbolicGame
