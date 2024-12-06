module Issy.Monitor.CHC
  ( checkCHC
  ) where

import qualified Data.Map as Map
import System.Process (readProcessWithExitCode)

import Issy.Config (Config, chcCmd, chcOpts)
import Issy.Logic.FOL
import Issy.Printers.SMTLib (s2Term, smtLib2)
import Issy.Utils.Extra (firstLine)
import Issy.Utils.Logging

checkCHC :: Config -> Symbol -> [Sort] -> [([Term], Term)] -> IO (Maybe Bool)
checkCHC cfg invPred sorts constraints = do
  let query = chcEncode invPred sorts constraints
  callCHCSolver cfg query

chcEncode :: Symbol -> [Sort] -> [([Term], Term)] -> String
chcEncode invPred sorts constr =
  unlines
    $ [ "(set-logic HORN)"
      , "(declare-fun " ++ invPred ++ "(" ++ concatMap ((' ' :) . s2Term) sorts ++ " ) Bool)"
      ]
        ++ map enc constr
        ++ ["(check-sat)"]
  where
    enc :: ([Term], Term) -> String
    enc (prem, conc) =
      let implication = func "=>" [andf prem, conc]
          vars = Map.toList $ bindings implication
          quantSig = concatMap (\(var, sort) -> "(" ++ var ++ " " ++ s2Term sort ++ ")") vars
       in "(assert (forall (" ++ quantSig ++ ") " ++ smtLib2 implication ++ "))"

callCHCSolver :: Config -> String -> IO (Maybe Bool)
callCHCSolver cfg query = do
  lg cfg ["CHC solver", "running"]
  (_, stdout, _) <- readProcessWithExitCode (chcCmd cfg) (chcOpts cfg) query
  lg cfg ["CHC solver", "terminated with", firstLine stdout]
  case stdout of
    's':'a':'t':_ -> pure $ Just True
    'u':'n':'s':'a':'t':_ -> pure $ Just False
    _ -> pure Nothing
