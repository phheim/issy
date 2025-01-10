module Issy.Config
  ( Config(..)
  , defaultConfig
  , setName
  ) where

data Config = Config
  { logName :: String
  , logLevel :: Word
    -- Formula to game translation
  , pruneGame :: Bool
  , rulesDeduction :: Bool
  , rulesSaturation :: Bool
  , rulesSubsitution :: Bool
  , rulesUnsatChecks :: Bool
  , rulesDeductionPrecise :: Bool
  , propagationLevel :: Int
    -- Game solving
  , accelerate :: Bool
  , accelerateObjective :: Bool
  , ufAcceleration :: Bool
  , extendAcceleration :: Bool
  -- ^ if this is set, depending if is set ufAcceleration, we nest or use chc 
  , invariantIterations :: Int
  , manhattenTermCount :: Int
    -- Synthesis
  , generateProgram :: Bool
    -- External tools
  , z3cmd :: String
  , ltl2tgba :: String
  , muvalScript :: String
  , chcMaxScript :: String
    -- Fixed constants
  , muvalTimeOut :: Int
  , chcMaxTimeOut :: Int
  , chcTimeout :: Int
  }

defaultConfig :: Config
defaultConfig =
  Config
    { logName = "[Issy]"
    , logLevel = 1
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
    , ufAcceleration = False
    , extendAcceleration = False
    , invariantIterations = 3
    , manhattenTermCount = 2
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

setName :: String -> Config -> Config
setName name cfg = cfg {logName = "[" ++ name ++ "]"}
