{-# LANGUAGE LambdaCase #-}

module Main
  ( main
  ) where

import Control.Monad (when)
import Data.Bifunctor (second)
import System.Environment (getArgs)
import System.Exit (die, exitSuccess)

import Issy

data Mode
  = Compile
  | Print
  | ToGame
  | Solve
  | EncodeTSLMT
  | EncodeTSLMTLissy
  | EncodeMuCLP
  | EncodeRPG
  | EncodeLTLMT
  | EncodeSweap

data InputFormat
  = HighLevel
  | LowLevel
  | RPG
  | TSLMT

getSpec :: Config -> String -> InputFormat -> IO Specification
getSpec cfg input =
  \case
    LowLevel -> do
      spec <- liftErr $ parseLLIssyFormat input
      checkSpecification cfg spec >>= liftErr
      pure spec
    HighLevel -> do
      input <- liftErr $ compile input
      spec <- liftErr $ parseLLIssyFormat input
      checkSpecification cfg spec >>= liftErr
      pure spec
    _ -> error "assert: this function should only be called for Issy/Lissy stuff"

main :: IO ()
main = do
  (mode, inputFormat, cfg, input) <- argParser
  res <-
    case (mode, inputFormat) of
      (Compile, HighLevel) -> liftErr (compile input)
      (Compile, _) -> die "invalid arguments: can only compile issy format"
      (Print, LowLevel) -> printLLIssyFormat <$> getSpec cfg input LowLevel
      (Print, RPG) -> printRPG <$> liftErr (parseRPG input)
      (Print, _) -> die "invalid arguments: can only print low-level format and rpg-format"
      (ToGame, LowLevel) -> printSG <$> (specToSG cfg =<< getSpec cfg input LowLevel)
      (ToGame, HighLevel) -> printSG <$> (specToSG cfg =<< getSpec cfg input HighLevel)
      (ToGame, RPG) -> printRPG <$> liftErr (parseRPG input)
      (ToGame, TSLMT) -> printRPG <$> (tslToRPG cfg =<< parseTSL input)
      (Solve, LowLevel) ->
        printRes cfg
          =<< (solve cfg emptyStats . fromSG)
          =<< specToSG cfg
          =<< getSpec cfg input LowLevel
      (Solve, HighLevel) ->
        printRes cfg
          =<< (solve cfg emptyStats . fromSG)
          =<< specToSG cfg
          =<< getSpec cfg input HighLevel
      (Solve, RPG) -> printRes cfg =<< (solve cfg emptyStats . fromRPG) =<< liftErr (parseRPG input)
      (Solve, TSLMT) -> do
        printRes cfg =<< (solve cfg emptyStats . fromRPG) =<< tslToRPG cfg =<< parseTSL input
      (EncodeTSLMT, RPG) -> uncurry rpgToTSLT <$> liftErr (parseRPG input)
      (EncodeTSLMT, _) -> die "invalid arguments: can only encode RPGs to TSLMT at the moment"
      (EncodeTSLMTLissy, TSLMT) ->
        printLLIssyFormat . specFromRPLTL <$> (tslToRPLTL cfg =<< parseTSL input)
      (EncodeTSLMTLissy, _) -> die "invalid arguments: this encoding works only on TSLMT"
      (EncodeMuCLP, RPG) -> uncurry rpgToMuCLP <$> liftErr (parseRPG input)
      (EncodeMuCLP, _) -> die "invalid arguments: can only encode RPGs to MuCLP at the moment"
      (EncodeRPG, RPG) -> printSG . rpgToSG <$> liftErr (parseRPG input)
      (EncodeRPG, _) ->
        die "invalid arguments: can only encode RPGs/TSLMT to Symbolic Games at the moment"
      (EncodeLTLMT, LowLevel) -> specToLTLMT <$> getSpec cfg input LowLevel
      (EncodeLTLMT, HighLevel) -> specToLTLMT <$> getSpec cfg input HighLevel
      (EncodeLTLMT, RPG) -> do
        spec <- uncurry specFromSymbolicGame . rpgToSG <$> liftErr (parseRPG input)
        checkSpecification cfg spec >>= liftErr
        pure $ specToLTLMT spec
      (EncodeLTLMT, TSLMT) -> do
        spec <- specFromRPLTL <$> (tslToRPLTL cfg =<< parseTSL input)
        checkSpecification cfg spec >>= liftErr
        pure $ specToLTLMT spec
      (EncodeSweap, LowLevel) -> specToSweap <$> getSpec cfg input LowLevel
      (EncodeSweap, HighLevel) -> specToSweap <$> getSpec cfg input HighLevel
      (EncodeSweap, RPG) -> do
        game <- liftErr $ parseRPG input
        let spec = uncurry specFromSymbolicGame $ rpgToSG game
        checkSpecification cfg spec >>= liftErr
        pure $ specToSweap spec
      (EncodeSweap, TSLMT) -> do
        spec <- specFromRPLTL <$> (tslToRPLTL cfg =<< parseTSL input)
        checkSpecification cfg spec >>= liftErr
        pure $ specToSweap spec
  putStrLn res

printRes :: Config -> (Bool, Stats, Maybe (IO String)) -> IO String
printRes conf (res, stats, printProg) = do
  printStats conf stats
  let resStr
        | res = "Realizable"
        | otherwise = "Unrealizable"
  progStr <- maybe (pure "") (fmap ('\n' :)) printProg
  pure $ resStr ++ progStr

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
  when ("--version" `elem` args) $ do
    print issyVersion
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
    "--encode-rpg-llissy" -> Just EncodeRPG
    "--encode-tslmt-llissy" -> Just EncodeTSLMTLissy
    "--encode-ltlmt" -> Just EncodeLTLMT
    "--encode-sweap" -> Just EncodeSweap
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
            "polycomp" ->
              go (cfg {ufAcceleration = False, extendAcceleration = False, genGeomAccel = True}) ar
            "polycomp-ext" ->
              go (cfg {ufAcceleration = False, extendAcceleration = True, genGeomAccel = True}) ar
            "unint" -> go (cfg {ufAcceleration = True, extendAcceleration = False}) ar
            "unint-ext" -> go (cfg {ufAcceleration = True, extendAcceleration = True}) ar
            _ -> Left $ "found invalid attractor acceleration mode: " ++ arg
        "--accel-difficulty":arg:ar ->
          case arg of
            "easy" -> go (cfg {accelerationLevel = 0}) ar
            "medium" -> go (cfg {accelerationLevel = 1}) ar
            "hard" -> go (cfg {accelerationLevel = 2}) ar
            _ -> Left $ "found invalid attractor acceleration difficulty: " ++ arg
        "--enable-summaries":sr -> go (cfg {enforcementSummaries = True}) sr
        -- Synthesis
        "--synt":sr -> go (cfg {generateProgram = True}) sr
        -- External tools
        "--caller-z3":arg:ar -> go (cfg {z3cmd = arg}) ar
        "--caller-aut":arg:ar -> go (cfg {ltl2tgba = arg}) ar
        "--caller-muval":arg:ar -> go (cfg {muvalScript = arg}) ar
        "--caller-chcmx":arg:ar -> go (cfg {chcMaxScript = arg}) ar
        -- Debug
        "--debug":ar -> go (cfg {debug = True}) ar
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
  , ""
  , "   --encode-tslmt       : encode a RPG spec to TSLMT"
  , "   --encode-muclp       : encode a RPG spec to MuCLP used by 'muval'"
  , "   --encode-rpg-llissy  : encode a RPG spec to llissy"
  , "   --encode-tslmt-lissy : encode a TSLMT spec to llissy"
  , "   --encode-ltlmt       : encode issy/llissy spec as LTLMT formula used by 'Syntheos'"
  , "   --encode-sweap       : encode issy/llissy spec as specification used by 'Sweap'"
  , ""
  , "   --version : returns the version of Issy"
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
  , "       polycomp     : compositional-polyhedra-based acceleration (default)"
  , "       polycomp-ext : compositional-polyhedra-based acceleration and with nesting"
  , "       geom         : geometric acceleration with invariant iteration"
  , "       geom-ext     : geometric acceleration with extended invariant computation"
  , "       unint        : acceleration with uninterpreted lemmas"
  , "       unint-ext    : acceleration with uninterpreted lemmas and nesting"
  , ""
  , "   --accel-difficulty TYPE"
  , "       easy   : stick to very local acceleration with simple arguments"
  , "       medium : go to elaborated accleration argument over time but stay reasonable (default)"
  , "       hard   : use everything that is possible, this will create signifcant overhead"
  , ""
  , "   --enable-summaries : enable computation of enforcement summaries"
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
