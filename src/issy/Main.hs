{-# LANGUAGE LambdaCase #-}

module Main
  ( main
  ) where

import Control.Monad (when)
import Data.Bifunctor (second)
import System.Environment (getArgs)
import System.Exit (die, exitSuccess)

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
      spec <- liftErr $ parseLLIssyFormat input
      checkSpecification cfg spec >>= liftErr
      putStrLn $ printLLIssyFormat spec
    (Print, RPG) -> do
      game <- liftErr $ parseRPG input
      putStrLn $ printRPG game
    (Print, _) -> die "invalid arguments: can only print low-level format and rpg-format"
    -- Game transformation
    (ToGame, LowLevel) -> do
      spec <- liftErr $ parseLLIssyFormat input
      checkSpecification cfg spec >>= liftErr
      game <- specToSG cfg spec
      putStrLn $ printSG game
    (ToGame, HighLevel) -> do
      input <- liftErr $ compile input
      spec <- liftErr $ parseLLIssyFormat input
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
      spec <- liftErr $ parseLLIssyFormat input
      checkSpecification cfg spec >>= liftErr
      game <- specToSG cfg spec
      res <- solve cfg emptyStats (fromSG game)
      printRes cfg res
    (Solve, HighLevel) -> do
      input <- liftErr $ compile input
      spec <- liftErr $ parseLLIssyFormat input
      checkSpecification cfg spec >>= liftErr
      game <- specToSG cfg spec
      res <- solve cfg emptyStats (fromSG game)
      printRes cfg res
    (Solve, RPG) -> do
      game <- liftErr $ parseRPG input
      res <- solve cfg emptyStats (fromRPG game)
      printRes cfg res
    (Solve, TSLMT) -> do
      spec <- parseTSL input
      game <- tslToRPG cfg spec
      res <- solve cfg emptyStats (fromRPG game)
      printRes cfg res
    -- Encode
    (EncodeTSLMT, RPG) -> do
      game <- liftErr $ parseRPG input
      putStrLn $ uncurry rpgToTSLT game
    (EncodeTSLMT, _) -> die "invalid arguments: can only encode RPGs to TSLMT at the moment"
    (EncodeMuCLP, RPG) -> do
      game <- liftErr $ parseRPG input
      putStrLn $ uncurry rpgToMuCLP game
    (EncodeMuCLP, _) -> die "invalid arguments: can only encode RPGs to MuCLP at the moment"

printRes :: Config -> (Bool, Stats, Maybe (IO String)) -> IO ()
printRes conf (res, stats, printProg) = do
  printStats conf stats
  if res
    then putStrLn "Realizable"
    else putStrLn "Unrealizable"
  case printProg of
    Nothing -> pure ()
    Just printProg -> printProg >>= putStrLn

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
        "--quiet":ar -> go (cfg {logLevel = 0}) ar
        "--info":ar -> go (cfg {logLevel = 1}) ar
        "--detailed":ar -> go (cfg {logLevel = 2}) ar
        "--verbose":ar -> go (cfg {logLevel = 3}) ar
        "--stats-to-stdout":ar -> go (cfg {statToStdout = True}) ar
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
        -- Game solving
        "--accel":arg:ar ->
          case arg of
            "no" -> go (cfg {accelerate = False}) ar
            "attr" -> go (cfg {accelerate = True, accelerateObjective = False}) ar
            "full" -> go (cfg {accelerate = True, accelerateObjective = True}) ar
            _ -> Left $ "found invalid acceleration mode: " ++ arg
        "--accel-attr":arg:ar ->
          case arg of
            "geom" -> go (cfg {ufAcceleration = False, extendAcceleration = False}) ar
            "geom-chc" -> go (cfg {ufAcceleration = False, extendAcceleration = True}) ar
            "unint" -> go (cfg {ufAcceleration = True, extendAcceleration = False}) ar
            "unint-nest" -> go (cfg {ufAcceleration = True, extendAcceleration = True}) ar
            _ -> Left $ "found invalid attractor acceleration mode: " ++ arg
        "--accel-difficulty":arg:ar ->
          case arg of
            "easy" -> go (cfg {accelerationLevel = 0}) ar
            "medium" -> go (cfg {accelerationLevel = 1}) ar
            "hard" -> go (cfg {accelerationLevel = 2}) ar
            _ -> Left $ "found invalid attractor acceleration difficulty: " ++ arg
        -- Synthesis
        "--synt":sr -> go (cfg {generateProgram = True}) sr
        -- External tools
        "--caller-z3":arg:ar -> go (cfg {z3cmd = arg}) ar
        "--caller-aut":arg:ar -> go (cfg {ltl2tgba = arg}) ar
        "--caller-muval":arg:ar -> go (cfg {muvalScript = arg}) ar
        "--caller-chcmx":arg:ar -> go (cfg {chcMaxScript = arg}) ar
        s:_ -> Left $ "found invalid argument: " ++ s

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
  , " Logging:"
  , "   --quiet    : no logging at all"
  , "   --info     : enable standard log messages (default)"
  , "   --detailed : enable detailed log messages including sub-steps"
  , "   --verbose  : log almost everything, including SMT queries"
  , ""
  , "  --stats-to-stdout : write statistics to STDOUT (default: as log message)"
  , ""
  , ""
  , " Formula translation:"
  , "   --pruning LEVEL"
  , "         0 : monitor based pruning disabled (default)"
  , "         1 : monitor based pruning without deduction rules and low propagation"
  , "         2 : monitor based pruning with deduction rules and normal propagation"
  , "         3 : monitor based pruning with precise deduction and high propagation"
  , ""
  , " Game solving:"
  , "   --accel TYPE"
  , "       no   : acceleration disabled"
  , "       attr : enable only attractor acceleration (default)"
  , "       full : enable additionally Büchi and parity acceleration"
  , ""
  , "   --accel-attr TYPE"
  , "       geom       : geometric acceleration with invariant iteration (default)"
  , "       geom-chc   : geometric acceleration with chc invariant computation"
  , "       unint      : acceleration with uninterpreted lemmas"
  , "       unint-nest : acceleration with uninterpreted lemmas and nesting"
  , ""
  , "   --accel-difficulty TYPE"
  , "       easy   : stick to very local acceleration with simple arguments"
  , "       medium : go to elaborated accleration argument over time but stay reasonable (default)"
  , "       hard   : use everything that is possible, this will create signifcant overhead"
  , ""
  , " Synthesis:"
  , "   --synt         : generate program if spec is realizable (default: disabled)"
  , ""
  , " External tools:"
  , "   When some of these tools are needed depends on the other options. Note that"
  , "   they are NEVER needed for COMPILATION ONLY with --compile"
  , ""
  , "   --caller-z3 CMD    : path or command for z3"
  , "                          needed : always"
  , "                          default: 'z3'"
  , "   --caller-aut CMD   : path or command for Spot's ltl2tgba"
  , "                          needed : if temporal formula appear in the specification"
  , "                          default: 'ltl2tgba'"
  , "   --caller-muval CMD : path or command that calls coars MuVal with a timeout"
  , "                        as argument and the input on STDIN"
  , "                          needed : for --pruning 2 and --pruning 3"
  , "                          default: 'call-muval.sh'"
  , "   --caller-chcmx CMD : path or command that calls a moddified version of coars"
  , "                        CHCMax with a timeout as argument and the input on STDIN"
  , "                          needed : for --pruning 3 and --accel geom-chc"
  , "                          default: 'call-maxsat.sh'"
  ]
