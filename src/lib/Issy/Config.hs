module Issy.Config
  ( Config(..)
  , defaultConfig
  , setName
  ) where

data Config = Config
  { logging :: Bool
  , logName :: String
    -- SMT solving
  , smtQueryLogging :: Bool
    -- Game Solving
  , generateProgram :: Bool
  , accelerate :: Bool
  , nestAcceleration :: Bool
  , invariantIterations :: Int --TODO options
  , manhattenTermCount :: Int --TODO options
  , ufAcceleration :: Bool
  , geomCHCAcceleration :: Bool
    -- Formula to Game translation
  , ltl2tgba :: String -- TODO options
  , muvalScript :: String
  , muvalTimeOut :: Int
  , chcMaxScript :: String
  , chcMaxTimeOut :: Int
  , chcTimeout :: Int
  , pruneGame :: Bool
  , rulesDeduction :: Bool
  , rulesSaturation :: Bool
  , rulesSubsitution :: Bool
  , rulesUnsatChecks :: Bool
  , rulesDeductionPrecise :: Bool
  , propagationLevel :: Int
  }

defaultConfig :: Config
defaultConfig =
  Config
    { logging = True
    , logName = "[Issy]"
    , smtQueryLogging = False
    , accelerate = True
    , nestAcceleration = False
    , ufAcceleration = False
    , geomCHCAcceleration = False
    , invariantIterations = 3
    , manhattenTermCount = 2
    , generateProgram = False
    , ltl2tgba = "ltl2tgba"
    , pruneGame = False
    , rulesDeduction = True
    , rulesSaturation = True
    , rulesSubsitution = True
    , rulesUnsatChecks = True
    , rulesDeductionPrecise = True
    , muvalScript = "call-muval.sh"
    , muvalTimeOut = 5
    , chcMaxScript = "call-maxsat.sh"
    , chcMaxTimeOut = 15
    , chcTimeout = 10
    , propagationLevel = 2
    }

setName :: String -> Config -> Config
setName name cfg = cfg {logName = "[" ++ name ++ "]"}
