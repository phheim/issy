---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy
-- Description : Top-level module of the issy's tool library
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy
  ( Config(..)
  , AccelLevel(..)
  , defaultConfig
  , -- Statistics
    Stats
  , emptyStats
  , printStats
  , -- Solving
    solve
  , fromRPG
  , fromSG
  , -- Translation
    tslToRPG
  , specToSG
  , -- Printing
    printLLIssyFormat
  , printRPG
  , printSG
  , -- Parsing
    parseRPG
  , parseTSL
  , parseLLIssyFormat
  , -- Sanitizing
    checkSpecification
  , -- Encoding
    rpgToMuCLP
  , rpgToTSLT
  ) where

---------------------------------------------------------------------------------------------------
-- Config and Statistics
import Issy.Config (AccelLevel(..), Config(..), defaultConfig)
import Issy.Statistics (Stats, emptyStats, printStats)

-- Extractors
import Issy.Extractors.MuCLP (rpgToMuCLP)
import Issy.Extractors.TSLT (rpgToTSLT)

-- Parsers 
import Issy.Parsers.LLIssyFormat (parseLLIssyFormat)
import Issy.Parsers.RPG (parseRPG)
import Issy.Parsers.TSLMT (parseTSL)

-- Printers
import Issy.Printers.LLIssyFormat (printLLIssyFormat)
import Issy.Printers.RPG (printRPG)
import Issy.Printers.SymbolicGame (printSG)

-- Solvers
import Issy.Solver.GameInterface (fromRPG, fromSG)
import Issy.Solver.ObjectiveSolver (solve)

-- Translation (with and without pruning)
import Issy.Translation (specToSG, tslToRPG)

-- Checking
import Issy.Specification (checkSpecification)
---------------------------------------------------------------------------------------------------
