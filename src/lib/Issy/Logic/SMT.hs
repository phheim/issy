---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.SMT
  ( sat
  , satModel
  , trySat
  , trySatModel
  , unsat
  , valid
  , -- Simplification
    simplify
  , simplifyLight
  , simplifyHeavy
  , simplifyUF
  , trySimplify
  , trySimplifyUF
  , -- Max SMT
    optPareto
  , tryOptPareto
  ) where

---------------------------------------------------------------------------------------------------
import Data.Map ((!?))
import qualified Data.Set as Set
import System.Exit (die)

import Issy.Config (Config, z3cmd)
import Issy.Logic.FOL (Model, Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Parsers.SMTLib as SMTLib
import qualified Issy.Parsers.SMTLibLexer as SMTLib
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Utils.Extra (noTimeout, runTO)
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- SMT Solving
---------------------------------------------------------------------------------------------------
sat :: Config -> Term -> IO Bool
sat conf = noTimeout . trySat conf Nothing

unsat :: Config -> Term -> IO Bool
unsat conf f = not <$> sat conf f

valid :: Config -> Term -> IO Bool
valid conf f = not <$> sat conf (FOL.neg f)

satModel :: Config -> Term -> IO (Maybe Model)
satModel conf = noTimeout . trySatModel conf Nothing

trySat :: Config -> Maybe Int -> Term -> IO (Maybe Bool)
trySat conf to f = do
  let query = SMTLib.toQuery f ++ "(check-sat)"
  callz3 conf to query $ \case
    'u':'n':'s':'a':'t':_ -> Just False
    's':'a':'t':_ -> Just True
    _ -> Nothing

trySatModel :: Config -> Maybe Int -> Term -> IO (Maybe (Maybe Model))
trySatModel conf to f = do
  let query = SMTLib.toQuery f ++ "(check-sat-using (and-then simplify default))(get-model)"
  callz3 conf to query $ \case
    'u':'n':'s':'a':'t':_ -> Just Nothing
    's':'a':'t':xr -> Just $ Just $ SMTLib.extractModel (FOL.frees f) xr
    _ -> Nothing

---------------------------------------------------------------------------------------------------
-- Simplification
---------------------------------------------------------------------------------------------------
z3Simplify :: [String]
z3Simplify =
  [ "simplify"
  , "propagate-ineqs"
  , "qe2"
  , "simplify"
  , "propagate-ineqs"
  , "nnf"
  , "ctx-solver-simplify"
  , "propagate-ineqs"
  , "solver-subsumption"
  , "unit-subsume-simplify"
  , "simplify"
  ]

simplify :: Config -> Term -> IO Term
simplify conf = noTimeout . trySimplify conf Nothing

trySimplify :: Config -> Maybe Int -> Term -> IO (Maybe Term)
trySimplify conf to = simplifyTacs conf to z3Simplify

simplifyHeavy :: Config -> Term -> IO Term
simplifyHeavy conf term = do
  term <- simplify conf term
  term <- simplify conf $ FOL.neg term
  simplify conf $ FOL.neg term

z3SimplifyLight :: [String]
z3SimplifyLight =
  ["simplify", "propagate-ineqs", "qe2", "propagate-ineqs", "unit-subsume-simplify", "simplify"]

simplifyLight :: Config -> Term -> IO Term
simplifyLight conf = noTimeout . simplifyTacs conf Nothing z3SimplifyLight

z3SimplifyUF :: [String]
z3SimplifyUF = ["simplify", "propagate-ineqs", "qe", "simplify"]

simplifyUF :: Config -> Term -> IO Term
simplifyUF conf = noTimeout . trySimplifyUF conf Nothing

trySimplifyUF :: Config -> Maybe Int -> Term -> IO (Maybe Term)
trySimplifyUF conf to = simplifyTacs conf to z3SimplifyUF

simplifyTacs :: Config -> Maybe Int -> [String] -> Term -> IO (Maybe Term)
simplifyTacs conf to tactics f
  | FOL.ufFree f = do
    let query = SMTLib.toQuery f ++ "(apply " ++ z3TacticList tactics ++ ")"
    callz3 conf to query $ \res ->
      case readTransformZ3 (FOL.bindings f !?) (SMTLib.tokenize res) of
        Right res -> Just res
        _ -> Nothing
  | otherwise = pure $ Just f

z3TacticList :: [String] -> String
z3TacticList =
  \case
    [] -> error "assertion: non-empty tactic list not allowed"
    [t] -> t
    t:tr -> "(and-then " ++ t ++ " " ++ z3TacticList tr ++ ")"

readTransformZ3 :: (Symbol -> Maybe Sort) -> [SMTLib.Token] -> Either String Term
readTransformZ3 ty =
  \case
    SMTLib.TLPar:SMTLib.TId "goals":SMTLib.TLPar:SMTLib.TId "goal":tr -> FOL.andf <$> readGoals tr
    ts -> Left $ "Invalid pattern for goals: " ++ show ts
  where
    readGoals =
      \case
        [] -> Left "assertion: found [] before ')' while reading goals"
        SMTLib.TId (':':_):_:tr -> readGoals tr
        [SMTLib.TRPar, SMTLib.TRPar] -> Right []
        ts ->
          case SMTLib.parseTerm ty ts of
            Left err -> Left err
            Right (f, tr) -> (f :) <$> readGoals tr

---------------------------------------------------------------------------------------------------
-- Optimal Solving
---------------------------------------------------------------------------------------------------
optPareto :: Config -> Term -> [Term] -> IO (Maybe Model)
optPareto conf f = noTimeout . tryOptPareto conf Nothing f

tryOptPareto :: Config -> Maybe Int -> Term -> [Term] -> IO (Maybe (Maybe Model))
tryOptPareto conf to f maxTerms = do
  f <- simplify conf f
  if not (FOL.quantifierFree f)
    then trySatModel conf to f
    else let maxQueries =
               concatMap (\t -> "(maximize " ++ SMTLib.toString t ++ ")")
                 $ filter ((`Set.isSubsetOf` FOL.frees f) . FOL.frees) maxTerms
             query =
               "(set-option :opt.priority pareto)"
                 ++ SMTLib.toQuery f
                 ++ maxQueries
                 ++ "(check-sat)(get-model)"
          in callz3 conf to query $ \case
               'u':'n':'s':'a':'t':_ -> Just Nothing
               's':'a':'t':xr -> Just $ Just $ SMTLib.extractModel (FOL.frees f) xr
               _ -> Nothing

---------------------------------------------------------------------------------------------------
-- Helper and common routines
---------------------------------------------------------------------------------------------------
callz3 :: Config -> Maybe Int -> String -> (String -> Maybe a) -> IO (Maybe a)
callz3 conf to query parse = do
  lgv conf ["z3 query:", query]
  res <- runTO to (z3cmd conf) ["-smt2", "-in"] query
  case res of
    Nothing -> pure Nothing
    Just res ->
      case parse res of
        Just res -> pure (Just res)
        _ -> die $ "z3 returned unexpected: \"" ++ res ++ "\" on \"" ++ query ++ "\""
---------------------------------------------------------------------------------------------------
