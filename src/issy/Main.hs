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
    (EncodeTSLMT, RPG) -> do game <- liftErr $ parseRPG input
                             putStrLn $ uncurry rpgToTSLT game
    (EncodeTSLMT, _) -> die "invalid arguments: can only encode RPGs to TSLMT at the moment"
    (EncodeMuCLP, RPG) -> do game <- liftErr $ parseRPG input
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
    putStrLn argumentDescription
    exitSuccess
  (mode, args) <- pure $ retriveArg getMode Solve args
  (inputFormat, args) <- pure $ retriveArg getInputFormat HighLevel args
  (filename, args) <- getFileName args
  cfg <- liftErr $ argumentParser args
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
-- TODO port from config
---
-- Help descriptions
---
shortHelp :: [String]
shortHelp = ["no argument or filename found"]

-- TODO port from config
