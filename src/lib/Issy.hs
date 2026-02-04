---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy
-- Description : Top-level module of the issy's tool library
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy
  ( issyVersion
  , -- Compilation
    compile
  , -- Data
    Specification
  , Objective
  , Arena
  , RPArena
  , FPSystem
  , -- Config
    Config(..)
  , defaultConfig
  , -- Statistics
    Stats
  , emptyStats
  , printStats
  , -- Solving
    solveSpec
  , solveSG
  , solveRPG
  , -- Translation
    tslToRPG
  , tslToRPLTL
  , specToSG
  , rpgToFP
  , sgToFP
  , specToFP
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
  , fpToMuCLP
  , rpgToSG
  , rpgToTSLT
  ) where

---------------------------------------------------------------------------------------------------
-- Data Structures
import Issy.Games.Objectives (Objective)
import Issy.Games.ReactiveProgramArena (RPArena)
import Issy.Games.SymbolicArena (Arena)

-- Compilation
import Issy.Compiler (compile)

-- Config and Statistics
import Issy.Config (Config(..), defaultConfig)
import Issy.Statistics (Stats, emptyStats, printStats)

-- Encoding
import Issy.Encoders.FullMuCLP (fpToMuCLP) -- TODO: This is more of a printer
import Issy.Encoders.LTLMT (specToLTLMT)
import Issy.Encoders.Sweap (specToSweap)
import Issy.Encoders.TSLT (rpgToTSLT)
import Issy.Encoders.ToFixpoints (FPSystem, gameToFP) -- TODO: This is more of a translator

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

---------------------------------------------------------------------------------------------------
-- | current version of issy
issyVersion :: Word
issyVersion = 2

---------------------------------------------------------------------------------------------------
-- Wrappers
---------------------------------------------------------------------------------------------------
-- | Apply 'solve' to specifications with new statistics
solveSpec :: Config -> Specification -> IO (Bool, Stats, Maybe (IO String))
solveSpec config spec = specToSG config spec >>= solveSG config

-- | Apply 'solve' to symbolic games
solveSG :: Config -> (Arena, Objective) -> IO (Bool, Stats, Maybe (IO String))
solveSG config = solve config (emptyStats config) . fromSG

-- | Apply 'solve' to reactive program games
solveRPG :: Config -> (RPArena, Objective) -> IO (Bool, Stats, Maybe (IO String))
solveRPG config
  | removeRPGs config = solveSG config . rpgToSG
  | otherwise = solve config (emptyStats config) . fromRPG

-- | Translate an reactive program game into a fixpoint system
rpgToFP :: (RPArena, Objective) -> FPSystem
rpgToFP = uncurry gameToFP . fromRPG

-- | Translate an symbolic game into a fixpoint system
sgToFP :: (Arena, Objective) -> FPSystem
sgToFP = uncurry gameToFP . fromSG

-- | Translate a generic specification into a fixpoint system. This might include
-- translating temporal logic to games
specToFP :: Config -> Specification -> IO FPSystem
specToFP config spec = sgToFP <$> specToSG config spec
---------------------------------------------------------------------------------------------------
