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
import qualified Data.Set as Set

import Issy.Config (Config, setName)
import qualified Issy.Logic.RPLTL as RPLTL
import Issy.Logic.TSLMT hiding (variables)
import qualified Issy.Logic.TSLMT as TSLMT (TSLSpec(variables))
import Issy.Monitor.Formula (fromTSL)
import Issy.Monitor.Monitor
import Issy.Monitor.Postprocess (finish)
import Issy.Monitor.Propagation (generatePredicates)
import Issy.Monitor.Rules (applyRules, context)
import Issy.Monitor.State (falseSt, initSt, stateToString, trueSt)
import Issy.Monitor.Successors (generateSuccessor)
import Issy.Printers.SMTLib (smtLib2)
import Issy.Utils.Logging

initializeTSL :: Config -> TSLSpec -> IO Monitor
initializeTSL cfg spec = do
  cfg <- pure $ setName "Monitor" cfg
  let ctx = context (TSLMT.variables spec) (tslSpecUpdates spec)
  let initialLabel = initSt (map fromTSL (assumptions spec)) (map fromTSL (guarantees spec))
  lg cfg ["initalize:", "raw", stateToString initialLabel]
  (initialLabel, ctx) <- applyRules cfg ctx initialLabel
  lg cfg ["initalize:", "simple", stateToString initialLabel]
  let initialLabels = [(State 0, initialLabel), (State 1, trueSt), (State 2, falseSt)]
  preds <- generatePredicates cfg (TSLMT.variables spec) (tslSpecPreds spec) (tslSpecUpdates spec)
  lg cfg ["generate preds:", strS smtLib2 preds]
  return
    $ Monitor
        { ctx = ctx
        , variables = TSLMT.variables spec
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
        }

initializeRPLTL :: Config -> RPLTL.Spec -> IO Monitor
initializeRPLTL = error "TODO FIX: init monitor with RP-LTL"
