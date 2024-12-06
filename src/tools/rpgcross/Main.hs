module Main
  ( main
  ) where

import System.Environment (getArgs)

import Issy (Objective, parseRPG, printRPG, rpgProduct)
import Issy.RPG (Game)

-- TODO: Make this cross-plattform!!
getDirPath :: String -> String
getDirPath = reverse . dropWhile (/= '/') . reverse

readGame :: String -> IO (Game, Objective)
readGame path = do
  content <- readFile path
  case parseRPG content of
    Left err -> fail err
    Right gwc -> return gwc

main :: IO ()
main = do
  crossFilePath <- head <$> getArgs
  subGameRelPaths <- filter (not . null) . lines <$> readFile crossFilePath
  let subGamePaths = map (getDirPath crossFilePath ++) subGameRelPaths
  games <- mapM readGame subGamePaths
  putStrLn (printRPG (rpgProduct games))
