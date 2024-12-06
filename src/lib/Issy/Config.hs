{-# LANGUAGE LambdaCase #-}

module Issy.Config
  ( Config(..)
  , SMTSolver(..)
  , defaultConfig
  , setName
  , argumentParser
  , argumentDescription
  ) where

import Text.Read (readMaybe)

data SMTSolver
  = SMTSolverZ3
  | SMTSolverCVC5
  deriving (Eq, Ord, Show)

data Config = Config
  { logging :: Bool
  , logName :: String
    -- SMT solving
  , smtSolver :: SMTSolver
  , smtModelGenCommand :: String
  , smtQueryLogging :: Bool
  , smtSimplifyZ3Tacs :: [String]
    -- Game Solving
  , skolemizeOnly :: Bool
  , generateProgram :: Bool
    -- Formula to Game translation
  , ltl2tgba :: String
  , pruneGame :: Bool
  , rulesDeduction :: Bool
  , rulesSaturation :: Bool
  , rulesSubsitution :: Bool
  , rulesUnsatChecks :: Bool
  , rulesDeductionPrecise :: Bool
  , muvalScript :: String
  , muvalTimeOut :: Int
  , chcMaxScript :: String
  , chcMaxTimeOut :: Int
  , chcCmd :: String
  , chcOpts :: [String]
  , propagationLevel :: Int
  }

defaultConfig :: Config
defaultConfig =
  Config
    { logging = True
    , logName = "[RPG]"
    , smtSolver = SMTSolverZ3
    , smtModelGenCommand = "(check-sat-using (and-then simplify (! default :macro-finder true)))"
    , smtQueryLogging = False
    , smtSimplifyZ3Tacs = z3Simplify
    , skolemizeOnly = False
    , generateProgram = False
    , ltl2tgba = "ltl2tgba"
    , pruneGame = False
    , rulesDeduction = True
    , rulesSaturation = True
    , rulesSubsitution = True
    , rulesUnsatChecks = True
    , rulesDeductionPrecise = True
    , muvalScript = "/home/cispa/rpg/other-tools/scripts/call-muval.sh"
    , muvalTimeOut = 5
    , chcMaxScript = "/home/cispa/rpg/other-tools/scripts/call-maxsat.sh"
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
  , "nnf"
  , "propagate-ineqs"
  , "ctx-solver-simplify"
  , "propagate-ineqs"
  , "unit-subsume-simplify"
  ]

-- TODO: Move this somewhere else, it does not really fit
argumentParser :: [String] -> Either String Config
argumentParser = go defaultConfig
  where
    go cfg =
      \case
        [] -> pure cfg
        "--quiet":ar -> go (cfg {logging = False}) ar
        "--verbose":ar -> go (cfg {logging = True, smtQueryLogging = True}) ar
        "--solver-z3":ar -> go (cfg {smtSolver = SMTSolverZ3}) ar
        "--solver-cvc5":ar -> go (cfg {smtSolver = SMTSolverCVC5}) ar
        "--generate-program":sr -> go (cfg {generateProgram = True}) sr
        "--skolemize-only":sr -> go (cfg {skolemizeOnly = True}) sr
        "--prune":ar -> go (cfg {pruneGame = True}) ar
        "--rules-disable-unsat-check":ar -> go (cfg {rulesUnsatChecks = False}) ar
        "--rules-disable-substitution":ar -> go (cfg {rulesSubsitution = False}) ar
        "--rules-disable-saturation":ar -> go (cfg {rulesSaturation = False}) ar
        "--rules-disable-deduction":ar -> go (cfg {rulesDeduction = False}) ar
        "--rules-disable-precise-deduction":ar -> go (cfg {rulesDeductionPrecise = False}) ar
        "--muval-caller":arg:ar -> go (cfg {muvalScript = arg}) ar
        "--muval-timeout":ar -> do
          (k, ar) <- readNumber ar
          go (cfg {muvalTimeOut = k}) ar
        "--chcmax-caller":arg:ar -> go (cfg {chcMaxScript = arg}) ar
        "--chcmax-timeout":ar -> do
          (k, ar) <- readNumber ar
          go (cfg {chcMaxTimeOut = k}) ar
        "--propagation-level":ar -> do
          (k, ar) <- readNumber ar
          go (cfg {propagationLevel = k}) ar
        s:_ -> Left $ "found invalid argument: " ++ s
    --
    readNumber :: [String] -> Either String (Int, [String])
    readNumber =
      \case
        [] -> Left "expected number after last argument"
        a:ar ->
          case readMaybe a of
            Nothing -> Left $ "expected number, found " ++ a
            Just k -> Right (k, ar)

argumentDescription :: String
argumentDescription =
  unlines
    [ "--------------------------------------------------------------------------------"
    , " Generic options:"
    , "  --quiet       : disables logging (default: logging enable)"
    , "  --verbose     : enables verbose logging (default: verbose logging disabled)"
    , "  --solver-z3   : sets z3 as the smt-solver for all operations (default: yes)"
    , "  --solver-cvc5 : set cvc5 as the smt-solver for model queries (default: no)"
    , "                  remark: z3 is still needed for executing queries"
    , ""
    , " Game solving options:"
    , "  --generate-program   : generated a program if realizable (default: disabled)"
    , "  --skolemize-only     : don't use QE but compute skolem functions directly "
    , "                         (default: disabled)"
    , ""
    , " Formula to game options:"
    , "  --prune                      : enables monitor-base pruning (default: no)"
    , "  --rules-disable-unsat-check  : disable the unsat rule (default: enabled)"
    , "  --rules-disable-substitution : disable the substitution rules"
    , "                                 (default: enabled)"
    , "  --rules-disable-saturation   : disable the saturation rules (default: enabled)"
    , "  --rules-disable-deduction    : disable the deduction rules (default: enabled)"
    , "  --rules-disable-precise-deduction :"
    , "                          disable the precise deduction rules (default: enabled)"
    , "  --muval-caller PATH     : sets the path to a script/binary that calls MuVal,"
    , "                            the script should take as argument a timeout and"
    , "                            read its input from STDIN"
    , "  --muval-timeout INT     : sets the timeout for MuVal in seconds"
    , "  --chcmax-caller PATH    : set the path a script/binary that calls the coar"
    , "                            CHCMax solver"
    , "  --chcmax-timeout INT    : sets the timeout for teh CHCMax solver in seconds"
    , "  --propagation-level INT : sets the proagation level, the higher the level the"
    , "                            more predicattes are generated (default: 2)"
    ]
