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
    "--issy" -> Just HighLevel
    "--llissy" -> Just LowLevel
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
        -- Logging
        "--quiet":ar -> go (cfg {logging = False}) ar
        "--info":ar -> go (cfg {logging = True, smtQueryLogging = False}) ar
        "--verbose":ar -> go (cfg {logging = True, smtQueryLogging = True}) ar
        -- Formula translation
        "--pruning":arg:ar ->
          case arg of
            "0" -> go (cfg {pruneGame = False}) ar
            "1" ->
              go
                (cfg
                   { pruneGame = True
                   , rulesDeduction = False
                   , rulesDeductionPrecise = False
                   , propagationLevel = 1
                   })
                ar
            "2" ->
              go
                (cfg
                   { pruneGame = True
                   , rulesDeduction = True
                   , rulesDeductionPrecise = False
                   , propagationLevel = 2
                   })
                ar
            "3" ->
              go
                (cfg
                   { pruneGame = True
                   , rulesDeduction = True
                   , rulesDeductionPrecise = True
                   , propagationLevel = 5
                   })
                ar
            _ -> Left $ "invalid pruning level: " ++ arg
        "--muval-caller":arg:ar -> go (cfg {muvalScript = arg}) ar
        "--muval-timeout":ar -> do
          (k, ar) <- readNumber ar
          go (cfg {muvalTimeOut = k}) ar
        "--chcmax-caller":arg:ar -> go (cfg {chcMaxScript = arg}) ar
        "--chcmax-timeout":ar -> do
          (k, ar) <- readNumber ar
          go (cfg {chcMaxTimeOut = k}) ar
        -- Game solving
        "--accel":arg:ar ->
          case arg of
            "no" -> go (cfg {accelerate = False}) ar
            "geom" -> go (cfg {accelerate = True, ufAcceleration = False}) ar
            "unint" ->
              go (cfg {accelerate = True, ufAcceleration = True, nestAcceleration = False}) ar
            "unint-nest" ->
              go (cfg {accelerate = True, ufAcceleration = True, nestAcceleration = True}) ar
            _ -> Left $ "found invalid acceleration mode: " ++ arg
        -- Synthesis
        "--synt":sr -> go (cfg {generateProgram = True}) sr
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
shortHelp =
  [ "no argument or filename found"
  , ""
  , " usage: issy OPTION* FILENAME"
  , ""
  , "  e.g.:"
  , "     issy input.issy"
  , "     issy --solve --acceleration none -"
  , "     issy --compile input.issy"
  , "     issy --llissy --to-game input.llissy"
  , "     issy --rpg --encode-muclp input.rpg"
  , ""
  , " to get a list of all possible options run 'issy --help'"
  ]

help :: [String]
help =
  [ "Usage: issy OPTION* [INPUTFILE | '-']"
  , ""
  , " The output is always writen to STDOUT. Errors and logging informations are"
  , " written to STDERR. If INPUTFILE is '-' the input is read from STDIN."
  , ""
  , " Input format:"
  , "   --issy   : input is a issy spec (default)"
  , "   --llissy : input is a llissy spec"
  , "   --rpg    : input is a RPG spec"
  , "   --tslmt  : input is a TSLMT spec a used by 'tsl2rpg'"
  , ""
  , " Modes:"
  , "   --solve   : solve the input spec (default)"
  , "   --compile : compiles a issy spec into the llissy format"
  , "   --to-game : translate the input specification to a game without temporal logic"
  , "   --print   : pretty print a llissy or RPG spec"
  , "   --encode-tslmt : encode a RPG spec to TSLMT"
  , "   --encode-muclp : encode a RPG spec to MuCLP used by 'muval'"
  , ""
  , " Log level:"
  , "   --quiet   : no logging at all"
  , "   --info    : enable standard log messages (default)"
  , "   --verbose : log almost everything, including SMT queries"
  , ""
  , " Formula translation:"
  , "   --pruning LEVEL"
  , "         0 : monitor based pruning disabled (default)"
  , "         1 : monitor based pruning without deduction rules and low propagation"
  , "         2 : monitor based pruning with deduction rules and normal propagation"
  , "         3 : monitor based pruning with precise deduction and high propagation"
  , ""
  , "   --muval-caller PATH     : path to a script that calls MuVal, it takes a"
  , "                             a timeout as argument and reads its input from STDIN"
  , "   --chcmax-caller PATH    : path to a script that calls the coar CHCMax solver"
  , "   --muval-timeout INT     : timeout for MuVal in seconds"
  , "   --chcmax-timeout INT    : timeout for the CHCMax solver in seconds"
  , ""
  , " Game solving:"
  , "   --accel TYPE"
  , "       no         : acceleration disabled"
  , "       geom       : geometric acceleration with invariant iteration (default)"
  , "       unint      : acceleration with uninterpreted lemmas"
  , "       unint-nest : acceleration with uninterpreted lemmas and nesting"
  , ""
  , " Synthesis:"
  , "   --synt         : generate program if spec is realizable (default: disabled)"
  ]
