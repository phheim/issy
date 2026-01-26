---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy
-- Description : Top-level module of the issy's tool library
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy
  ( issyVersion
  , -- Compilation
    compile
  , -- Data
    Specification
  , -- Config
    Config(..)
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
  , tslToRPLTL
  , specToSG
  , -- Printing
    printLLIssyFormat
  , printRPG
  , printSG
  , -- Parsing
    parseRPG
  , parseTSL
  , parseLLIssyFormat
  , -- Converting
    specFromRPLTL
  , specFromSymbolicGame
  , -- Sanitizing
    checkSpecification
  , -- Encoding
    specToLTLMT
  , specToSweap
  , rpgToMuCLP
  , fpToMuCLP
  , rpgToSG
  , rpgToTSLT
  , gameToFP
  ) where

---------------------------------------------------------------------------------------------------
-- Compilation
import Issy.Compiler (compile)

-- Config and Statistics
import Issy.Config (Config(..), defaultConfig)
import Issy.Statistics (Stats, emptyStats, printStats)

-- Encoding
import Issy.Encoders.FullMuCLP (fpToMuCLP)
import Issy.Encoders.LTLMT (specToLTLMT)
import Issy.Encoders.MuCLP (rpgToMuCLP)
import Issy.Encoders.Sweap (specToSweap)
import Issy.Encoders.TSLT (rpgToTSLT)
import Issy.Encoders.ToFixpoints (gameToFP)

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
import Issy.Translation (rpgToSG, specToSG, tslToRPG, tslToRPLTL)

-- Checking
import Issy.Specification (Specification, checkSpecification, specFromRPLTL, specFromSymbolicGame)

issyVersion :: Word
issyVersion = 2
---------------------------------------------------------------------------------------------------
