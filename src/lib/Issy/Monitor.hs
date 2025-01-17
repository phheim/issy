---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Monitor.Issy
-- Description : Module exposing all functionalities of monitors for RPLTL
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
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
  , Trans(..)
  , leafs
  ) where

---------------------------------------------------------------------------------------------------
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
  ( Monitor(..)
  , State(..)
  , Trans(..)
  , Verdict(..)
  , initial
  , inputs
  , leafs
  , stateName
  , verdict
  )
import Issy.Monitor.Postprocess (finish)
import qualified Issy.Monitor.Propagation as MP
import qualified Issy.Monitor.Rules as MR
import Issy.Monitor.State (falseSt, initSt, stateToString, trueSt)
import Issy.Monitor.Successors (generateSuccessor)
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- | 'initializeRPLTL' creates as 'Monitor' for RPLTL formula specifications. In order to used the
-- monitor its transitions and verdict have to be computed.
initializeRPLTL :: Config -> RPLTL.Spec -> IO Monitor
initializeRPLTL cfg spec = do
  cfg <- pure $ setName "Monitor" cfg
  preds <- MP.generatePredicatesRPLTL cfg (RPLTL.variables spec) (RPLTL.preds spec)
  initialize
    cfg
    False
    (MR.globalState (RPLTL.variables spec))
    (RPLTL.variables spec)
    (MF.fromRPLTL <$> RPLTL.assumptions spec)
    (MF.fromRPLTL <$> RPLTL.guarantees spec)
    preds

---------------------------------------------------------------------------------------------------
-- | 'initializeTSL' creates as 'Monitor' for TSLMT formula specifications. In order to used the
-- monitor its transitions and verdict have to be computed.
initializeTSL :: Config -> TSL.Spec -> IO Monitor
initializeTSL cfg spec = do
  cfg <- pure $ setName "Monitor TSL" cfg
  preds <- MP.generatePredicatesTSL cfg (TSL.variables spec) (TSL.preds spec) (TSL.updates spec)
  initialize
    cfg
    True
    (MR.globalStateTSL (TSL.variables spec) (TSL.updates spec))
    (TSL.variables spec)
    (MF.fromTSL <$> TSL.assumptions spec)
    (MF.fromTSL <$> TSL.guarantees spec)
    preds

---------------------------------------------------------------------------------------------------
-- | 'initalize' is a generic initilaisation for both RPLTL and TSLMT. The main difference in the 
-- monitor is that RPLTL has now updates and therefore everything related to them should be 
-- disabled or have no effect.
initialize ::
     Config -> Bool -> MR.GlobalS -> Variables -> [Formula] -> [Formula] -> Set Term -> IO Monitor
initialize cfg upd gls vars assumptions guarantees preds = do
  lg cfg ["generate preds:", strS SMTLib.toString preds]
  let initialLabel = initSt assumptions guarantees
  lg cfg ["initalize:", "raw", stateToString initialLabel]
  (initialLabel, gls) <- MR.applyRules cfg gls initialLabel
  lg cfg ["initalize:", "simple", stateToString initialLabel]
  let initialLabels = [(State 0, initialLabel), (State 1, trueSt), (State 2, falseSt)]
  return
    $ Monitor
        { gls = gls
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
---------------------------------------------------------------------------------------------------
