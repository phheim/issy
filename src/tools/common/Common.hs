module Common where

import System.Environment (getArgs)
import System.Exit (die, exitSuccess)

liftErr :: Either String b -> IO b
liftErr res =
  case res of
    Left err -> die err
    Right res -> return res

checkArgs :: String -> IO [String]
checkArgs help = do
  args <- getArgs
  if any (`elem` args) ["--help", "-help", "-h", "-?"]
    then do
      putStrLn help
      exitSuccess
    else return args
