---------------------------------------------------------------------------------------------------
-- |
-- Module      : Monitor.Issy
-- Description : Monitors for monitor-pruning
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module exposes all functionalities of monitors for pruning RPLTL and TSL formulas
-- upon their translation to games. They are described in the POPL'25 paper.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Monitor
  ( -- State
    State
  , stateName
  , -- Transition
    Trans(..)
  , leafs
  , -- Monitor
    Monitor
  , Verdict(..)
  , variables
  , Issy.Monitor.Monitor.inputs
  , verdict
  , initial
  , -- Computation
    initializeRPLTL
  , initializeTSL
  , generateSuccessor
  , finish
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Logic.RPLTL as RPLTL
import qualified Issy.Logic.TSLMT as TSL
import qualified Issy.Logic.Temporal as TL
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
import qualified Issy.Printers.SMTLib as SMTLib

---------------------------------------------------------------------------------------------------
-- | Create a monitor for an RPLTL formula specifications. In order to used the
-- monitor its transitions and verdict have to be computed.
initializeRPLTL :: Config -> TL.Spec RPLTL.Atom -> IO Monitor
initializeRPLTL cfg spec = do
  cfg <- pure $ setName "Monitor" cfg
  preds <- MP.generatePredicatesRPLTL cfg (TL.variables spec) (RPLTL.preds spec)
  initialize
    cfg
    False
    (MR.globalState (TL.variables spec))
    (TL.variables spec)
    (MF.fromRPLTL <$> TL.assumptions spec)
    (MF.fromRPLTL <$> TL.guarantees spec)
    preds

-- | Create a monitor for a TSLMT formula specifications. In order to used the
-- monitor its transitions and verdict have to be computed.
initializeTSL :: Config -> TL.Spec TSL.Atom -> IO Monitor
initializeTSL cfg spec = do
  cfg <- pure $ setName "Monitor TSL" cfg
  preds <- MP.generatePredicatesTSL cfg (TL.variables spec) (TSL.preds spec) (TSL.updates spec)
  initialize
    cfg
    True
    (MR.globalStateTSL (TL.variables spec) (TSL.updates spec))
    (TL.variables spec)
    (MF.fromTSL <$> TL.assumptions spec)
    (MF.fromTSL <$> TL.guarantees spec)
    preds

-- | A generic initialisation for both RPLTL and TSLMT. The main difference in the
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
