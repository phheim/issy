---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Config
-- Description : Module containing all possibilities for configuring Issy
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
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
  -- ^ 'logName' is the prefix for log messages indicating the current subpart.
  , logLevel :: Word
  -- ^ 'logLevel' is the amount of logging as exposed to the outer tool. The higher
  -- the more logging and zero means no logging.
  , statToStdout :: Bool
  -- ^ DOCUMENT
    --
    -- Formula to game translation
    --  
  , pruneGame :: Bool
  -- ^ DOCUMENT
  , rulesDeduction :: Bool
  -- ^ DOCUMENT
  , rulesSaturation :: Bool
  -- ^ DOCUMENT
  , rulesSubsitution :: Bool
  -- ^ DOCUMENT
  , rulesUnsatChecks :: Bool
  -- ^ DOCUMENT
  , rulesDeductionPrecise :: Bool
  -- ^ DOCUMENT
  , propagationLevel :: Int
  -- ^ DOCUMENT
    --
    -- Game solving
    -- 
  , accelerate :: Bool
  -- ^ 'acclerate' indicates if acceleration is enabled at all.
  , accelerateObjective :: Bool
  -- ^ 'acclerate' indicates if accleration is enabled not only for attractors
  -- but also for outer-fixpoint objectives like Büchi or parity.
  , genGeomAccel :: Bool
  -- ^ 'genGeomAccel' indicates if general geometric acceleration is enabled
  , ufAcceleration :: Bool
  -- ^ DOCUMENT
  , extendAcceleration :: Bool
  -- ^ DOCUMENT
  , accelerationLevel :: Word
  -- ^ if this is set, depending if is set ufAcceleration, we nest or use chc 
  , enforcementSummaries :: Bool
  -- ^ 'enforcementSummaries' indicates if enforcment summaires are used 
    --
    -- Synthesis
    --  
  , generateProgram :: Bool
  -- ^ DOCUMENT
    --
    -- External tools
    --  
  , z3cmd :: String
  -- ^ DOCUMENT
  , ltl2tgba :: String
  -- ^ DOCUMENT
  , muvalScript :: String
  -- ^ DOCUMENT
  , chcMaxScript :: String
  -- ^ DOCUMENT
    --
    -- Fixed constants
    -- 
  , muvalTimeOut :: Int
  -- ^ DOCUMENT
  , chcMaxTimeOut :: Int
  -- ^ DOCUMENT
  , chcTimeout :: Int
  -- ^ DOCUMENT
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
    , genGeomAccel = False
    , ufAcceleration = False
    , extendAcceleration = False
    , accelerationLevel = 1
    , enforcementSummaries = True
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
    }

---------------------------------------------------------------------------------------------------
-- 'setName' changes the current sub-part for logging. It should be called by the respective 
-- sub-part of the code.
setName :: String -> Config -> Config
setName name conf =
  let padName = "[" ++ name ++ "]" ++ replicate (5 - length name) ' '
   in conf {logName = padName}
---------------------------------------------------------------------------------------------------
