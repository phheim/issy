module Issy.Monitor
  ( State
  , stateName
  , Monitor
  , Verdict(..)
  , Issy.Monitor.Monitor.inputs
  , variables
  , initializeRPLTL
  , initializeTSL
  , verdict
  , initial
  , generateSuccessor
  , finish
  , toString
  , Trans(..)
  , leafs
  ) where

import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Variables (Variables)
import Issy.Config (Config, setName)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.RPLTL as RPLTL
import qualified Issy.Logic.TSLMT as TSL
import Issy.Monitor.Formula (Formula)
import qualified Issy.Monitor.Formula as MF
import Issy.Monitor.Monitor
import Issy.Monitor.Postprocess (finish)
import qualified Issy.Monitor.Propagation as MP
import qualified Issy.Monitor.Rules as MR
import Issy.Monitor.State (falseSt, initSt, stateToString, trueSt)
import Issy.Monitor.Successors (generateSuccessor)
import Issy.Printers.SMTLib (smtLib2)
import Issy.Utils.Logging

initializeTSL :: Config -> TSL.Spec -> IO Monitor
initializeTSL cfg spec = do
  cfg <- pure $ setName "Monitor TSL" cfg
  preds <- MP.generatePredicatesTSL cfg (TSL.variables spec) (TSL.preds spec) (TSL.updates spec)
  initialize
    cfg
    True
    (MR.contextTSL (TSL.variables spec) (TSL.updates spec))
    (TSL.variables spec)
    (MF.fromTSL <$> TSL.assumptions spec)
    (MF.fromTSL <$> TSL.guarantees spec)
    preds

initializeRPLTL :: Config -> RPLTL.Spec -> IO Monitor
initializeRPLTL cfg spec = do
  cfg <- pure $ setName "Monitor" cfg
  preds <- MP.generatePredicatesRPLTL cfg (RPLTL.variables spec) (RPLTL.preds spec)
  initialize
    cfg
    False
    (MR.context (RPLTL.variables spec))
    (RPLTL.variables spec)
    (MF.fromRPLTL <$> RPLTL.assumptions spec)
    (MF.fromRPLTL <$> RPLTL.guarantees spec)
    preds

initialize ::
     Config -> Bool -> MR.Context -> Variables -> [Formula] -> [Formula] -> Set Term -> IO Monitor
initialize cfg upd ctx vars assumptions guarantees preds = do
  lg cfg ["generate preds:", strS smtLib2 preds]
  let initialLabel = initSt assumptions guarantees
  lg cfg ["initalize:", "raw", stateToString initialLabel]
  (initialLabel, ctx) <- MR.applyRules cfg ctx initialLabel
  lg cfg ["initalize:", "simple", stateToString initialLabel]
  let initialLabels = [(State 0, initialLabel), (State 1, trueSt), (State 2, falseSt)]
  return
    $ Monitor
        { ctx = ctx
        , variables = vars
        , predicates = preds
        , initState = State 0
        , goodState = State 1
        , badState = State 2
        , stateLabel = Map.fromList initialLabels
        , revLabel = Map.fromList $ map (\(a, b) -> (b, a)) initialLabels
        , cnt = 3
        , safes = Set.empty
        , stateTrans = Map.empty
        , expansionCache = Map.empty
        , hasUpdates = upd
        }
