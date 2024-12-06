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
  , trySimplifyUF
  ) where

import Data.Map ((!?))
import Data.Maybe (fromMaybe)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

import Issy.Config
  ( Config(smtSimplifyZ3Tacs)
  , SMTSolver(..)
  , smtModelGenCommand
  , smtQueryLogging
  , smtSolver
  )
import Issy.Logic.FOL
import Issy.Parsers.SMTLib
import Issy.Parsers.SMTLibLexer
import Issy.Printers.SMTLib
import Issy.Utils.Logging

modelQuery :: Config -> Maybe Word -> String
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

satTO :: Config -> Maybe Word -> Term -> IO (Maybe Bool)
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

satModelTO :: Config -> Maybe Word -> Term -> IO (Maybe (Maybe Model))
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

readTransformZ3 :: (Symbol -> Maybe Sort) -> [Token] -> Term
readTransformZ3 ty =
  \case
    TLPar:TId "goals":TLPar:TId "goal":tr -> andf (readGoals tr)
    _ -> error "Assertion: Invalid pattern for goals"
  where
    readGoals =
      \case
        [] -> error "assertion: found [] before ')' while reading goals"
        TId (':':_):_:tr -> readGoals tr
        [TRPar, TRPar] -> []
        ts ->
          case parseTerm ty ts of
            Left err -> error ("Assertion: " ++ err)
            Right (f, tr) -> f : readGoals tr

z3TacticList :: [String] -> String
z3TacticList =
  \case
    [] -> error "assertion: non-empty tactic list not allowed"
    [t] -> t
    t:tr -> "(and-then " ++ t ++ " " ++ z3TacticList tr ++ ")"

simplifyTO :: Config -> Maybe Word -> Term -> IO (Maybe Term)
simplifyTO cfg to f = do
  let query = toSMTLib2 f ++ "(apply " ++ z3TacticList (smtSimplifyZ3Tacs cfg) ++ ")"
  let (solver, args) = ("z3", ["--smt2", "--in"])
  ifLog cfg "simplifyTO:" query
  out <- runTO to solver args query
  return
    (do
       res <- out
       case res of
         '(':'e':'r':'r':_ -> Nothing -- Is this still necessary?
         _ -> return (readTransformZ3 (bindings f !?) (tokenize res)))

simplify :: Config -> Term -> IO Term
simplify cfg = fmap (fromMaybe undefined) . simplifyTO cfg Nothing

runTO :: Maybe Word -> String -> [String] -> String -> IO (Maybe String)
runTO to cmd args input =
  case to of
    Nothing -> do
      (_, res, _) <- readProcessWithExitCode cmd args input
      return (Just res)
    Just n -> do
      (ext, res, _) <- readProcessWithExitCode "timeout" (show n : cmd : args) input
      case ext of
        ExitSuccess -> return (Just res)
        ExitFailure n
          | n == 124 -> return Nothing
          | otherwise -> return (Just res)

-- this will move to rpgsolve part
z3SimplifyUF :: [String]
z3SimplifyUF = ["simplify", "propagate-ineqs", "qe", "simplify"]

trySimplifyUF :: Config -> Word -> Term -> IO (Maybe Term)
trySimplifyUF cfg to = simplifyTO (cfg {smtSimplifyZ3Tacs = z3SimplifyUF}) (Just to)
