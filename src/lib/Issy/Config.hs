module Issy.Config
  ( Config(..)
  , defaultConfig
  , setName
  ) where

data Config = Config
  { logging :: Bool
  , logName :: String
    -- SMT solving
  , smtModelGenCommand :: String
  , smtQueryLogging :: Bool
  , smtSimplifyZ3Tacs :: [String]
    -- Game Solving
  , generateProgram :: Bool
  , accelerate :: Bool
  , nestAcceleration :: Bool
  , invariantIterations :: Int --TODO options
  , manhattenTermCount :: Int --TODO options
  , ufAcceleration :: Bool
    -- Formula to Game translation
  , ltl2tgba :: String -- TODO options
  , muvalScript :: String
  , muvalTimeOut :: Int
  , chcMaxScript :: String
  , chcMaxTimeOut :: Int
  , chcCmd :: String --TODO: Inline
  , chcOpts :: [String] -- TODO: Inline
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
    , smtModelGenCommand = "(check-sat-using (and-then simplify default))"
    , smtQueryLogging = False
    , smtSimplifyZ3Tacs = z3Simplify
    , accelerate = True
    , nestAcceleration = False
    , ufAcceleration = False
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
    , chcCmd = "z3"
    , chcOpts = ["-in", "-smt2", "-T:10"]
    , propagationLevel = 2
    }

setName :: String -> Config -> Config
setName name cfg = cfg {logName = "[" ++ name ++ "]"}

z3Simplify :: [String]
z3Simplify =
  [ "simplify"
  , "propagate-ineqs"
  , "qe2"
  , "simplify"
  , "propagate-ineqs"
  , "ctx-solver-simplify"
  , "propagate-ineqs"
  , "solver-subsumption"
  , "unit-subsume-simplify"
  , "simplify"
  ]
--  , "nnf"
