{-# LANGUAGE Safe #-}

module Issy.Printers.SymbolicGame
  ( printSG
  ) where

import Issy.Base.Objectives (Objective)
import Issy.Printers.LLIssyFormat (printLLIssyFormat)
import qualified Issy.Specification as Spec
import qualified Issy.SymbolicArena as SG

printSG :: (SG.Arena, Objective) -> String
printSG (arena, obj) =
  case Spec.addGame (Spec.empty (SG.variables arena)) arena obj of
    Left err -> error "assert: found impossible error: " ++ err
    Right spec -> printLLIssyFormat spec
