{-# LANGUAGE Safe #-}

module Issy.Printers.SymbolicGame
  ( printSG
  ) where

import Issy.Games.Objectives (Objective)
import qualified Issy.Games.SymbolicArena as SG
import Issy.Printers.LLIssyFormat (printLLIssyFormat)
import qualified Issy.Specification as Spec

printSG :: (SG.Arena, Objective) -> String
printSG (arena, obj) =
  case Spec.addGame (Spec.empty (SG.variables arena)) arena obj of
    Left err -> error "assert: found impossible error: " ++ err
    Right spec -> printLLIssyFormat spec
