---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Config
-- Description : Central configuration for Issy.
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
-- This module contains all runtime configuration options that Issy offers.
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Config
  ( Config(..)
  , defaultConfig
  , setName
  ) where

---------------------------------------------------------------------------------------------------
-- | 'Config' is the data type for the different configuration options of Issy
data Config = Config
  { logName :: String
  -- ^ Prefix for log messages indicating the current subpart.
  , logLevel :: Word
  -- ^ Amount of logging written to 'STDOUT'. Higher means more logging and zero means no logging.
  , statToStdout :: Bool
  -- ^ Indicates if the statistics collected should be written to 'STDOUT' instead 'STDERR'
    --
    -- Formula to game translation
    --  
  , pruneGame :: Bool
  -- ^ Indicates if monitor-pruning should be used to reduce games translated from logic formulas.
  , rulesDeduction :: Bool
  -- ^ Enables the monitor-pruning deduction rules on fixpoint computations.
  , rulesSaturation :: Bool
  -- ^ Enables the monitor-pruning saturation rules.
  , rulesSubsitution :: Bool
  -- ^ Enables the monitor-pruning substitution rules.
  , rulesUnsatChecks :: Bool
  -- ^ Enables the monitor-pruning UNSAT rules.
  , rulesDeductionPrecise :: Bool
  -- ^ Enables the monitor-pruning precise-deduction rule base on MaxCHC.
  , propagationLevel :: Int
  -- ^ Amount of predicates that are propagated during monitor construction (higher means more).
    --
    -- Game solving
    -- 
  , accelerate :: Bool
  -- ^ Indicates if acceleration is enabled at all.
  , accelerateObjective :: Bool
  -- ^ Indicates if acceleration is enabled not only for attractors
  -- but also for outer-fixpoint objectives like Büchi or parity.
  , genGeomAccel :: Bool
  -- ^ Indicates if polyhedra-based acceleration is enabled
  , ufAcceleration :: Bool
  -- ^ Indicates if polyhedra-based acceleration is enabled
  , extendAcceleration :: Bool
  -- ^ Indicates if the acceleration-technique should use extended techniques like nesting.
  , accelerationLevel :: Word
  -- ^ if this is set, depending if is set ufAcceleration, we nest or use chc 
  , enforcementSummaries :: Bool
  -- ^ Indicates if enforcement summaries are used.
    --
    -- Synthesis
    --  
  , generateProgram :: Bool
  -- ^ Enables program generation.
    --
    -- External tools
    --  
  , z3cmd :: String
  -- ^ Path to binary that should be used to call z3.
  , ltl2tgba :: String
  -- ^ Path to binary that should be used to call Spot's ltl2tgba.
  , muvalScript :: String
  -- ^ Path to script that should be used to call MuVal (part of the coar toolsuite)
  , chcMaxScript :: String
  -- ^ Path to script that should be used to call CHCMax (part of the coar toolsuite)
    --
    -- Fixed constants
    -- 
  , muvalTimeOut :: Int
  -- ^ Fixed timeout for MuVal calls in seconds.
  , chcMaxTimeOut :: Int
  -- ^ Fixed timeout for CHCMax calls in seconds.
  , chcTimeout :: Int
  -- ^ Fixed timeout for CHC calls (to z3) in seconds.
  --
  -- Debug
  --
  , debug :: Bool
  -- ^ Enables different validation techniques and double checks
  }

---------------------------------------------------------------------------------------------------
-- | 'defaultConfig' is the default 'Configuration' of Issy which contains sane defaults and 
-- should be used if no requested otherwise by the user.
defaultConfig :: Config
defaultConfig =
  Config
    { logName = "[Issy]"
    , logLevel = 1
    , statToStdout = False
    -- Formula to game translation
    , pruneGame = False
    , rulesSaturation = True
    , rulesSubsitution = True
    , rulesUnsatChecks = True
    , rulesDeduction = True
    , rulesDeductionPrecise = False
    , propagationLevel = 2
    -- Game solving
    , accelerate = True
    , accelerateObjective = False
    , genGeomAccel = True
    , ufAcceleration = False
    , extendAcceleration = False
    , accelerationLevel = 1
    , enforcementSummaries = False
    -- Synthesis
    , generateProgram = False
    -- External tools
    , z3cmd = "z3"
    , ltl2tgba = "ltl2tgba"
    , muvalScript = "call-muval.sh"
    , chcMaxScript = "call-maxsat.sh"
    -- Constants
    , chcTimeout = 10
    , muvalTimeOut = 5
    , chcMaxTimeOut = 15
    -- Debug
    , debug = False
    }

---------------------------------------------------------------------------------------------------
-- 'setName' changes the current sub-part for logging. It should be called by the respective 
-- sub-part of the code.
setName :: String -> Config -> Config
setName name conf =
  let padName = "[" ++ name ++ "]" ++ replicate (12 - length name) ' '
   in conf {logName = padName}
---------------------------------------------------------------------------------------------------
