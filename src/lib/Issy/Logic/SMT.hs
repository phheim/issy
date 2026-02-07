---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.SMT
-- Description : SMT operations
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements different SMT-solver base operations like satisfiability checking,
-- model generation, and simplifications. For this Z3 is used. We require at
-- least version "4.13.0" ov Z3.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

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
  , simplifyUF
  , trySimplify
  , trySimplifyUF
  , -- Max SMT
    optPareto
  , tryOptPareto
  ) where

---------------------------------------------------------------------------------------------------
import Data.Map ((!?))
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import System.Exit (die)

import Issy.Config (Config, debug, z3cmd)
import Issy.Logic.FOL (Model, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.Polyhedra as Poly (normalize)
import qualified Issy.Parsers.SMTLib as SMTLib
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Utils.Extra (noTimeout, runTO)
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- SMT Solving
---------------------------------------------------------------------------------------------------
-- | Check if a term is satisfiable, i.e. if there exists a model for the free variable
-- such that the formula evaluates to true. This method might diverge.
sat :: Config -> Term -> IO Bool
sat conf = noTimeout . trySat conf Nothing

-- | Check if a term in unsatisfiable, i.e. 'sat' is false. This method might diverge.
unsat :: Config -> Term -> IO Bool
unsat conf f = not <$> sat conf f

-- | Check if a term is valid, i.e. for all models for the free variables
-- the formula evaluates to true. This method might diverge.
valid :: Config -> Term -> IO Bool
valid conf f = not <$> sat conf (FOL.neg f)

-- | Like 'sat' but returns the model if it exists. This method might diverge.
satModel :: Config -> Term -> IO (Maybe Model)
satModel conf = noTimeout . trySatModel conf Nothing

-- | Like 'sat' but with an optional timeout. The timeout is given in seconds.
-- If a timeout is given, this methods will terminate.
trySat :: Config -> Maybe Int -> Term -> IO (Maybe Bool)
trySat conf to f
  | f == FOL.true = pure $ Just True
  | f == FOL.false = pure $ Just False
  | FOL.underapproxSAT f =
    assertM conf (Just True) (fromMaybe False <$> properSAT) "SMT.trySat: satisfiability differs"
  | otherwise = properSAT
  where
    properSAT = do
      let query = SMTLib.toQuery f ++ satCommand f
      callz3 conf to query $ \case
        'u':'n':'s':'a':'t':_ -> Just False
        's':'a':'t':_ -> Just True
        _ -> Nothing

-- | Like 'trySat' but returns the model if it exists. For the result
-- 'Nothing' means a timeout occurred and 'Just Nothing' means that no model
-- exists, i.e. the term is unsatisfiable.
trySatModel :: Config -> Maybe Int -> Term -> IO (Maybe (Maybe Model))
trySatModel conf to f = do
  let query = SMTLib.toQuery f ++ satCommand f ++ "(get-model)"
  callz3 conf to query $ \case
    'u':'n':'s':'a':'t':_ -> Just Nothing
    's':'a':'t':xr -> Just $ Just $ SMTLib.extractModel (FOL.decls f) xr
    _ -> Nothing

satCommand :: Term -> String
satCommand f
  | FOL.SInt `elem` FOL.sorts f && FOL.SReal `elem` FOL.sorts f && not (FOL.quantifierFree f) =
    "(check-sat-using (and-then qe default))"
  | otherwise = "(check-sat)"

---------------------------------------------------------------------------------------------------
-- Simplification
---------------------------------------------------------------------------------------------------
z3Simplify :: [String]
z3Simplify =
  ["simplify", "qe-light", "propagate-ineqs", "unit-subsume-simplify", "qe2"] ++ z3SimplifyQEFree

z3SimplifyQEFree :: [String]
z3SimplifyQEFree =
  [ "simplify"
  , "blast-term-ite"
  , "nnf"
  , "ctx-solver-simplify"
  , "propagate-ineqs"
  , "unit-subsume-simplify"
  , "solver-subsumption"
  , "simplify"
  ]

z3SimplifyUF :: [String]
z3SimplifyUF = ["simplify", "blast-term-ite", "nnf", "propagate-ineqs", "qe", "simplify"]

-- | Simplifies a term using SMT tactics. The given term must be free
-- of uninterpreted functions. The methods might diverge.
simplify :: Config -> Term -> IO Term
simplify conf = noTimeout . trySimplify conf Nothing

simplifyWith :: Term -> [String]
simplifyWith term
  | FOL.quantifierFree term = z3SimplifyQEFree
  | otherwise = z3Simplify

-- | Like 'simplify' but with an optional timeout in seconds.
-- If a timeout is given, this methods will terminate.
trySimplify :: Config -> Maybe Int -> Term -> IO (Maybe Term)
trySimplify conf to term = do
  simpTerm <- simplifyTacs conf to (simplifyWith term) term
  case simpTerm of
    Nothing -> pure Nothing
    Just simpTerm -> do
      simpTerm <- pure $ Poly.normalize simpTerm
      Just
        <$> assertM
              conf
              simpTerm
              (valid conf (simpTerm `FOL.iff` term))
              "SMT.trySimplify: terms differ"

assertM :: Config -> a -> IO Bool -> String -> IO a
assertM conf val check msg
  | debug conf = do
    res <- check
    if res
      then pure val
      else error $ "assert: " ++ msg
  | otherwise = pure val

simplifyTacs :: Config -> Maybe Int -> [String] -> Term -> IO (Maybe Term)
simplifyTacs conf to tactics f
  | null tactics = pure (Just f)
  | f == FOL.true || f == FOL.false = pure (Just f)
  | FOL.ufFree f = do
    let query = SMTLib.toQuery f ++ "(apply " ++ z3TacticList tactics ++ ")"
    callz3 conf to query $ \res ->
      case SMTLib.parseGoals (FOL.bindings f !?) res of
        Right res -> Just res
        _ -> Nothing
  | otherwise = pure $ Just f

-- | Simplifies a term with uninterpreted functions using SMT tactics.
-- Note that this is less powerful than 'simplify', which should be used
-- when possible. The methods might diverge.
simplifyUF :: Config -> Term -> IO Term
simplifyUF conf = noTimeout . trySimplifyUF conf Nothing

-- | Like 'simplifyUF' but with an optional timeout in seconds.
trySimplifyUF :: Config -> Maybe Int -> Term -> IO (Maybe Term)
trySimplifyUF conf to f
  | f == FOL.true || f == FOL.false = pure (Just f)
  | otherwise = do
    let query = SMTLib.toQuery f ++ "(apply " ++ z3TacticList z3SimplifyUF ++ ")"
    callz3 conf to query $ \res ->
      case SMTLib.parseGoals (FOL.bindings f !?) res of
        Right res -> Just $ Poly.normalize res
        _ -> Nothing

z3TacticList :: [String] -> String
z3TacticList =
  \case
    [] -> error "assertion: non-empty tactic list not allowed"
    [t] -> t
    t:tr -> "(and-then " ++ t ++ " " ++ z3TacticList tr ++ ")"

---------------------------------------------------------------------------------------------------
-- Optimal Solving
---------------------------------------------------------------------------------------------------
-- | Given a boolean constraint and a list of numeric terms, try to find a model for the
-- free variables, that satisfies the constraint and Pareto maximizes the numeric terms, i.e.
-- find an model such that there is no other model where the value of on of the optimization
-- term increases, while the vale of the other ones do not decrease.
optPareto :: Config -> Term -> [Term] -> IO (Maybe Model)
optPareto conf f = noTimeout . tryOptPareto conf Nothing f

-- | Like 'optPareto' but with an optional timeout in seconds.
-- If a timeout is given, this methods will terminate.
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
---------------------------------------------------------------------------------------------------
