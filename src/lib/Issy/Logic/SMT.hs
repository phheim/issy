{-# LANGUAGE LambdaCase #-}

module Issy.Logic.SMT
  ( SMTSolver(..)
  , satTO
  , satModelTO
  , sat
  , unsat
  , valid
  , implies
  , simplifyTO
  , simplify
  , simplifyStrong
  , trySimplifyUF
  , -- Max SMT
    satModelOpt
  , SMTOpt(..)
  ) where

import Data.Map ((!?))
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import System.Process (readProcessWithExitCode)
import qualified System.Timeout as Sys (timeout)

import Issy.Config
  ( Config(smtSimplifyZ3Tacs)
  , SMTSolver(..)
  , optSolver
  , smtModelGenCommand
  , smtQueryLogging
  , smtSolver
  )
import Issy.Logic.FOL
import Issy.Parsers.SMTLib
import Issy.Parsers.SMTLibLexer
import Issy.Printers.SMTLib
import Issy.Utils.Logging

modelQuery :: Config -> Maybe Int -> String
modelQuery cfg mto = preproc (smtModelGenCommand cfg)
  where
    to = fromMaybe maxBound mto
    preproc =
      \case
        [] -> []
        '%':'1':sr -> show to ++ preproc sr
        '%':'2':sr -> show (to `div` 2) ++ preproc sr
        '%':'4':sr -> show (to `div` 4) ++ preproc sr
        '%':'8':sr -> show (to `div` 8) ++ preproc sr
        s:sr -> s : preproc sr

ifLog :: Config -> String -> String -> IO ()
ifLog cfg typ query
  | smtQueryLogging cfg = lg cfg [typ, query]
  | otherwise = return ()

getSolver :: Config -> (String, [String])
getSolver cfg =
  case smtSolver cfg of
    SMTSolverZ3 -> ("z3", ["-smt2", "-in"])
    SMTSolverCVC5 -> ("cvc5", ["--produce-models", "-"])

satTO :: Config -> Maybe Int -> Term -> IO (Maybe Bool)
satTO cfg to f = do
  let query = toSMTLib2 f ++ "(check-sat)"
  let (solver, args) = getSolver cfg
  ifLog cfg "satTO:" query
  out <- runTO to solver args query
  return
    (do
       res <- out
       case res of
         'u':'n':'s':'a':'t':_ -> return False
         's':'a':'t':_ -> return True
         _ -> error ("smt-solver returned unexpected: \"" ++ res ++ "\""))

satModelTO :: Config -> Maybe Int -> Term -> IO (Maybe (Maybe Model))
satModelTO cfg to f = do
  let query = toSMTLib2 f ++ modelQuery cfg to ++ "(get-model)"
  let (solver, args) = getSolver cfg
  ifLog cfg "satModelTO:" query
  out <- runTO to solver args query
  return
    (do
       res <- out
       case res of
         'u':'n':'s':'a':'t':_ -> return Nothing
         's':'a':'t':xr -> return (Just (extractModel (frees f) xr))
         _ -> error ("smt-solver returned unexpected: \"" ++ res ++ "\""))

sat :: Config -> Term -> IO Bool
sat cfg = fmap (fromMaybe undefined) . satTO cfg Nothing

unsat :: Config -> Term -> IO Bool
unsat cfg f = not <$> sat cfg f

valid :: Config -> Term -> IO Bool
valid cfg f = not <$> sat cfg (neg f)

implies :: Config -> Term -> Term -> IO Bool
implies cfg f g = valid cfg (f `impl` g)

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
simplifyTO cfg to f
  | ufFree f = do
    let query = toSMTLib2 f ++ "(apply " ++ z3TacticList (smtSimplifyZ3Tacs cfg) ++ ")"
    let (solver, args) = ("z3", ["--smt2", "--in"])
    ifLog cfg "simplifyTO:" query
    out <- runTO to solver args query
    case out of
      Nothing -> pure Nothing
      Just res ->
        case readTransformZ3 (bindings f !?) (tokenize res) of
          Right res -> pure $ Just res
          Left err -> error $ "assert: " ++ err ++ " in \"" ++ query ++ "\""
  | otherwise = pure $ Just f

simplify :: Config -> Term -> IO Term
simplify cfg = fmap (fromMaybe undefined) . simplifyTO cfg Nothing

simplifyStrong :: Config -> Term -> IO Term
simplifyStrong cfg term = do
  term <- simplify cfg term
  term <- simplify cfg $ neg term
  simplify cfg $ neg term

runTO :: Maybe Int -> String -> [String] -> String -> IO (Maybe String)
runTO to cmd args input =
  case to of
    Nothing -> do
      (_, res, _) <- readProcessWithExitCode cmd args input
      return (Just res)
    Just n
      | n < 0 -> do
        (_, res, _) <- readProcessWithExitCode cmd args input
        return (Just res)
      | otherwise -> do
        res <- Sys.timeout (n * 10 ^ (6 :: Int)) $ readProcessWithExitCode cmd args input
        case res of
          Just (_, res, _) -> return (Just res)
          Nothing -> pure Nothing

z3SimplifyUF :: [String]
z3SimplifyUF = ["simplify", "propagate-ineqs", "qe", "simplify"]

trySimplifyUF :: Config -> Int -> Term -> IO (Maybe Term)
trySimplifyUF cfg to = simplifyTO (cfg {smtSimplifyZ3Tacs = z3SimplifyUF}) (Just to)

data SMTOpt =
  Paetro
  deriving (Eq, Ord, Show)

smtOptOption :: SMTOpt -> String
smtOptOption =
  \case
    Paetro -> "(set-option :opt.priority pareto)"

satModelOpt :: Config -> SMTOpt -> Term -> [Term] -> IO (Maybe Model)
satModelOpt conf opttype f maxTerms = do
  f <- simplify conf f
  case optSolver conf of
    Nothing -> fromMaybe (error "assert: unreachable code") <$> satModelTO conf Nothing f
    Just command
      | not (quantifierFree f) ->
        fromMaybe (error "assert: unreachable code") <$> satModelTO conf Nothing f
      | otherwise -> do
        let maxQueries =
              concatMap (\t -> "(maximize " ++ smtLib2 t ++ ")")
                $ filter ((`Set.isSubsetOf` frees f) . frees) maxTerms
        let query = smtOptOption opttype ++ toSMTLib2 f ++ maxQueries ++ "(check-sat)"
        res <- runTO Nothing command ["-model", "-optimization=true"] query
        case res of
          Nothing -> error "assert: unreachable code"
          Just ('u':'n':'s':'a':'t':_) -> return Nothing
          Just ('s':'a':'t':xr) -> return (Just (extractOptModel (frees f) xr))
          Just res ->
            error $ "smt-solver returned unexpected: \"" ++ res ++ "\" on \"" ++ query ++ "\""
