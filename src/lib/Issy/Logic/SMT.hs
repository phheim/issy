{-# LANGUAGE LambdaCase #-}

-- TODO: adapt name in SMT
module Issy.Logic.SMT
  ( satTO
  , satModelTO
  , satModel
  , sat
  , unsat
  , valid
  , -- Simplification
    simplifyTO
  , simplify
  , simplifyStrong
  , simplifyUF
  , trySimplifyUF
  , -- Max SMT
    optPareto
  , tryOptPareto
  ) where

import Data.Map ((!?))
import qualified Data.Set as Set

import Issy.Config (Config, smtQueryLogging)
import Issy.Logic.FOL
import Issy.Parsers.SMTLib
import Issy.Parsers.SMTLibLexer
import Issy.Printers.SMTLib
import Issy.Utils.Extra (noTimeout, runTO)
import Issy.Utils.Logging

import System.Exit (die)

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
-- TODO: Move to log
ifLog :: Config -> String -> String -> IO ()
ifLog cfg typ query
  | smtQueryLogging cfg = lg cfg [typ, query]
  | otherwise = return ()

callz3 :: Config -> Maybe Int -> String -> (String -> Maybe a) -> IO (Maybe a)
callz3 cfg to query parse = do
  ifLog cfg "z3 query:" query
  res <- runTO to "z3" ["-smt2", "-in"] query
  case res of
    Nothing -> pure Nothing
    Just res ->
      case parse res of
        Just res -> pure (Just res)
        _ -> die $ "z3 returned unexpected: \"" ++ res ++ "\" on \"" ++ query ++ "\""

satTO :: Config -> Maybe Int -> Term -> IO (Maybe Bool)
satTO cfg to f = do
  let query = toSMTLib2 f ++ "(check-sat)"
  callz3 cfg to query $ \case
    'u':'n':'s':'a':'t':_ -> Just False
    's':'a':'t':_ -> Just True
    _ -> Nothing

satModel :: Config -> Term -> IO (Maybe Model)
satModel conf = noTimeout . satModelTO conf Nothing

satModelTO :: Config -> Maybe Int -> Term -> IO (Maybe (Maybe Model))
satModelTO cfg to f = do
  let query = toSMTLib2 f ++ "(check-sat-using (and-then simplify default))(get-model)"
  callz3 cfg to query $ \case
    'u':'n':'s':'a':'t':_ -> Just Nothing
    's':'a':'t':xr -> Just $ Just $ extractModel (frees f) xr
    _ -> Nothing

sat :: Config -> Term -> IO Bool
sat cfg = noTimeout . satTO cfg Nothing

unsat :: Config -> Term -> IO Bool
unsat cfg f = not <$> sat cfg f

valid :: Config -> Term -> IO Bool
valid cfg f = not <$> sat cfg (neg f)

readTransformZ3 :: (Symbol -> Maybe Sort) -> [Token] -> Either String Term
readTransformZ3 ty =
  \case
    TLPar:TId "goals":TLPar:TId "goal":tr -> andf <$> readGoals tr
    ts -> Left $ "Invalid pattern for goals: " ++ show ts
  where
    readGoals =
      \case
        [] -> Left "assertion: found [] before ')' while reading goals"
        TId (':':_):_:tr -> readGoals tr
        [TRPar, TRPar] -> Right []
        ts ->
          case parseTerm ty ts of
            Left err -> Left err
            Right (f, tr) -> (f :) <$> readGoals tr

z3TacticList :: [String] -> String
z3TacticList =
  \case
    [] -> error "assertion: non-empty tactic list not allowed"
    [t] -> t
    t:tr -> "(and-then " ++ t ++ " " ++ z3TacticList tr ++ ")"

simplifyTO :: Config -> Maybe Int -> Term -> IO (Maybe Term)
simplifyTO conf to = simplifyTacs conf to z3Simplify

simplifyTacs :: Config -> Maybe Int -> [String] -> Term -> IO (Maybe Term)
simplifyTacs cfg to tactics f
  | ufFree f = do
    let query = toSMTLib2 f ++ "(apply " ++ z3TacticList tactics ++ ")"
    callz3 cfg to query $ \res ->
      case readTransformZ3 (bindings f !?) (tokenize res) of
        Right res -> Just res
        _ -> Nothing
  | otherwise = pure $ Just f

simplify :: Config -> Term -> IO Term
simplify cfg = noTimeout . simplifyTO cfg Nothing

simplifyStrong :: Config -> Term -> IO Term
simplifyStrong cfg term = do
  term <- simplify cfg term
  term <- simplify cfg $ neg term
  simplify cfg $ neg term

z3SimplifyUF :: [String]
z3SimplifyUF = ["simplify", "propagate-ineqs", "qe", "simplify"]

simplifyUF :: Config -> Term -> IO Term
simplifyUF cfg = noTimeout . trySimplifyUF cfg Nothing

trySimplifyUF :: Config -> Maybe Int -> Term -> IO (Maybe Term)
trySimplifyUF cfg to = simplifyTacs cfg to z3SimplifyUF

tryOptPareto :: Config -> Maybe Int -> Term -> [Term] -> IO (Maybe (Maybe Model))
tryOptPareto conf to f maxTerms = do
  f <- simplify conf f
  if not (quantifierFree f)
    then satModelTO conf to f
    else let maxQueries =
               concatMap (\t -> "(maximize " ++ smtLib2 t ++ ")")
                 $ filter ((`Set.isSubsetOf` frees f) . frees) maxTerms
             query =
               "(set-option :opt.priority pareto)"
                 ++ toSMTLib2 f
                 ++ maxQueries
                 ++ "(check-sat)(get-model)"
          in callz3 conf to query $ \case
               'u':'n':'s':'a':'t':_ -> Just Nothing
               's':'a':'t':xr -> Just $ Just $ extractModel (frees f) xr
               _ -> Nothing

optPareto :: Config -> Term -> [Term] -> IO (Maybe Model)
optPareto conf f = noTimeout . tryOptPareto conf Nothing f
