{-# LANGUAGE LambdaCase #-}

module Main
  ( main
  ) where

import Control.Monad (when)
import Data.Bifunctor (second)
import System.Environment (getArgs)
import System.Exit (die, exitSuccess)
import Text.Read (readMaybe)

import Compiler
import Issy

data Mode
  = Compile
  | Print
  | ToGame
  | Solve
  | EncodeTSLMT
  | EncodeMuCLP

data InputFormat
  = HighLevel
  | LowLevel
  | RPG
  | TSLMT

main :: IO ()
main = do
  (mode, inputFormat, cfg, input) <- argParser
  case (mode, inputFormat) of
    -- Compiling
    (Compile, HighLevel) -> liftErr (compile input) >>= putStrLn
    (Compile, _) -> die "invalid arguments: can only compile issy format"
    -- Printing
    (Print, LowLevel) -> do
      spec <- liftErr $ parseIssyFormat input
      checkSpecification cfg spec >>= liftErr
      putStrLn $ printIssyFormat spec
    (Print, RPG) -> do
      game <- liftErr $ parseRPG input
      putStrLn $ printRPG game
    (Print, _) -> die "invalid arguments: can only print low-level format and rpg-format"
    -- Game transformation
    (ToGame, LowLevel) -> do
      spec <- liftErr $ parseIssyFormat input
      checkSpecification cfg spec >>= liftErr
      game <- specToSG cfg spec
      putStrLn $ printSG game
    (ToGame, HighLevel) -> do
      input <- liftErr $ compile input
      spec <- liftErr $ parseIssyFormat input
      checkSpecification cfg spec >>= liftErr
      game <- specToSG cfg spec
      putStrLn $ printSG game
    (ToGame, RPG) -> do
      game <- liftErr $ parseRPG input
      putStrLn $ printRPG game
    (ToGame, TSLMT) -> do
      spec <- parseTSL input
      game <- tslToRPG cfg spec
      putStrLn $ printRPG game
    -- Solving
    (Solve, LowLevel) -> do
      spec <- liftErr $ parseIssyFormat input
      checkSpecification cfg spec >>= liftErr
      game <- specToSG cfg spec
      solve cfg (fromSG game)
    (Solve, HighLevel) -> do
      input <- liftErr $ compile input
      spec <- liftErr $ parseIssyFormat input
      checkSpecification cfg spec >>= liftErr
      game <- specToSG cfg spec
      solve cfg (fromSG game)
    (Solve, RPG) -> do
      game <- liftErr $ parseRPG input
      solve cfg (fromRPG game)
    (Solve, TSLMT) -> do
      spec <- parseTSL input
      game <- tslToRPG cfg spec
      solve cfg (fromRPG game)
    -- Encode
    (EncodeTSLMT, RPG) -> do
      game <- liftErr $ parseRPG input
      putStrLn $ uncurry rpgToTSLT game
    (EncodeTSLMT, _) -> die "invalid arguments: can only encode RPGs to TSLMT at the moment"
    (EncodeMuCLP, RPG) -> do
      game <- liftErr $ parseRPG input
      putStrLn $ uncurry rpgToMuCLP game
    (EncodeMuCLP, _) -> die "invalid arguments: can only encode RPGs to MuCLP at the moment"

liftErr :: Either String b -> IO b
liftErr res =
  case res of
    Left err -> die err
    Right res -> return res

---
-- Argument Parser
---
argParser :: IO (Mode, InputFormat, Config, String)
argParser = do
  args <- getArgs
  when (null args) $ die $ unlines shortHelp
  when ("--help" `elem` args) $ do
    putStrLn $ unlines help
    exitSuccess
  (mode, args) <- pure $ retriveArg getMode Solve args
  (inputFormat, args) <- pure $ retriveArg getInputFormat HighLevel args
  (filename, args) <- getFileName args
  cfg <- liftErr $ configParser args
  input <-
    case filename of
      "-" -> getContents
      _ -> readFile filename
  pure (mode, inputFormat, cfg, input)

getFileName :: [String] -> IO (String, [String])
getFileName =
  \case
    [] -> die "expected filename or '-'"
    [x] -> pure (x, [])
    a:ar -> second (a :) <$> getFileName ar

getMode :: String -> Maybe Mode
getMode =
  \case
    "--compile" -> Just Compile
    "--print" -> Just Print
    "--solve" -> Just Solve
    "--to-game" -> Just ToGame
    "--encode-tslmt" -> Just EncodeTSLMT
    "--encode-muclp" -> Just EncodeMuCLP
    _ -> Nothing

getInputFormat :: String -> Maybe InputFormat
getInputFormat =
  \case
    "--low-level" -> Just LowLevel
    "--rpg" -> Just RPG
    "--tslmt" -> Just TSLMT
    _ -> Nothing

retriveArg :: (String -> Maybe a) -> a -> [String] -> (a, [String])
retriveArg get val =
  \case
    [] -> (val, [])
    x:xr ->
      case get x of
        Nothing -> second (x :) $ retriveArg get val xr
        Just val -> retriveArg get val xr

---
-- Config Parser
--- 
configParser :: [String] -> Either String Config
configParser = go defaultConfig
  where
    go cfg =
      \case
        [] -> pure cfg
        "--quiet":ar -> go (cfg {logging = False}) ar
        "--verbose":ar -> go (cfg {logging = True, smtQueryLogging = True}) ar
        "--generate-program":sr -> go (cfg {generateProgram = True}) sr
        "--skolemize-only":sr -> go (cfg {skolemizeOnly = True}) sr
        "--disable-acceleration":sr -> go (cfg {accelerate = False}) sr
        "--nest-acceleration":sr -> go (cfg {nestAcceleration = True}) sr
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

---
-- Help descriptions
---
shortHelp :: [String]
shortHelp = ["no argument or filename found"]

help :: [String]
help =
  [ "--------------------------------------------------------------------------------"
  , " Generic options:"
  , "  --quiet       : disables logging (default: logging enable)"
  , "  --verbose     : enables verbose logging (default: verbose logging disabled)"
  , ""
  , " Game solving options:"
  , "  --generate-program     : generated a program if realizable (default: disabled)"
  , "  --disable-acceleration : disables acceleration (default: enabled)"
  , "  --nest-acceleration    : enables nested acceleration (default: disabled)"
  , "  --skolemize-only       : don't use QE but compute skolem functions directly "
  , "                           (default: disabled)"
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
