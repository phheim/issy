---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy
-- Description : Top-level library bindings of Issy
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- Issy is a tool for symbolic infinite-state game solving and synthesis. It supports both
-- temporal logics (RPLTL, TSLMT) as well as games (symbolic games, reactive program games) with
-- different winning conditions including parity conditions. This module implements the library
-- bindings for Issy. Issy was first presented at CAV'25 in the paper
-- ["Issy: A Comprehensive Tool for Specification and Synthesis of Infinite-State Reactive Systems"]
-- (https://arxiv.org/pdf/2502.03013) by Philippe Heim and Rayna Dimitrova.
-- Furthermore, the techniques implemented here, are also based on the following papers:
--
--  - ["Solving Infinite-State Games via Acceleration"]
--      (https://arxiv.org/pdf/2305.16118);
--      by P. Heim and R. Dimitrova at POPL'24
--  - ["Translation of Temporal Logic for Efficient Infinite-State Reactive Synthesis"]
--      (https://arxiv.org/pdf/2411.07078)
--      by P. Heim and R. Dimitrova at POPL'25
--  - ["Modular Attractor Acceleration in Infinite-State Games"]
--      (https://arxiv.org/pdf/2601.14068)
--      by P. Heim and R. Dimitrova at TACAS'26
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
  , printMuCLP
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
import Issy.Encoders.LTLMT (specToLTLMT)
import Issy.Encoders.Sweap (specToSweap)
import Issy.Encoders.TSLT (rpgToTSLT)
import Issy.Encoders.ToFixpoints (FPSystem, gameToFP)

-- Parsers
import Issy.Parsers.LLIssyFormat (parseLLIssyFormat)
import Issy.Parsers.RPG (parseRPG)
import Issy.Parsers.TSLMT (parseTSL)

-- Printers
import Issy.Printers.LLIssyFormat (printLLIssyFormat, printSG)
import Issy.Printers.MuCLP (printMuCLP)
import Issy.Printers.RPG (printRPG)

-- Solvers
import Issy.Solver.GameInterface (fromRPG, fromSG)
import Issy.Solver.ObjectiveSolver (solve)

-- Translation (with and without pruning)
import Issy.Translation (rpgToSG, specToSG, tslToRPG, tslToRPLTL)

-- Checking
import Issy.Specification (Specification, checkSpecification, specFromRPLTL, specFromSymbolicGame)

---------------------------------------------------------------------------------------------------
-- | Current version of issy.
issyVersion :: Word
issyVersion = 3

---------------------------------------------------------------------------------------------------
-- Wrappers
---------------------------------------------------------------------------------------------------
-- | Apply 'solve' to specifications with new statistics.
solveSpec :: Config -> Specification -> IO (Bool, Stats, Maybe (IO String))
solveSpec config spec = specToSG config spec >>= solveSG config

-- | Apply 'solve' to symbolic games.
solveSG :: Config -> (Arena, Objective) -> IO (Bool, Stats, Maybe (IO String))
solveSG config = solve config (emptyStats config) . fromSG

-- | Apply 'solve' to reactive program games.
solveRPG :: Config -> (RPArena, Objective) -> IO (Bool, Stats, Maybe (IO String))
solveRPG config
  | removeRPGs config = solveSG config . rpgToSG
  | otherwise = solve config (emptyStats config) . fromRPG

-- | Translate an reactive program game into a fixpoint system.
rpgToFP :: (RPArena, Objective) -> FPSystem
rpgToFP = uncurry gameToFP . fromRPG

-- | Translate an symbolic game into a fixpoint system.
sgToFP :: (Arena, Objective) -> FPSystem
sgToFP = uncurry gameToFP . fromSG

-- | Translate a generic specification into a fixpoint system. This might include
-- translating temporal logic formulas to games if those are present.
specToFP :: Config -> Specification -> IO FPSystem
specToFP config spec = sgToFP <$> specToSG config spec
---------------------------------------------------------------------------------------------------
