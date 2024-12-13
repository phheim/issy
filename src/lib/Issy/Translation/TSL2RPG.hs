{-# LANGUAGE LambdaCase #-}

module Issy.Translation.TSL2RPG
  ( tsl2rpg
  ) where

import Data.Bifunctor (second)
import Data.Foldable (find)
import Data.List (nub)
import Data.Map.Strict (Map, (!), (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tuple (swap)

import Issy.Base.Objectives (Objective(..))
import qualified Issy.Base.Objectives as Obj
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, setName)
import Issy.Logic.FOL
import qualified Issy.Logic.TSLMT as TSL
import qualified Issy.Logic.Temporal as TL
import Issy.RPG
import qualified Issy.RPG as RPG
import qualified Issy.Translation.DOA as DOA
import qualified Issy.Translation.LTL2DOA as LTL2DOA
import Issy.Utils.Extra
import Issy.Utils.Logging

updates :: Set TSL.Atom -> Map Symbol (Set Term)
updates =
  foldl
    (\mp ->
       \case
         TSL.Predicate _ -> mp
         TSL.Update x u -> Map.insertWith Set.union x (Set.singleton u) mp)
    Map.empty

selfUpdates :: Variables -> Set TSL.Atom
selfUpdates vars = Set.map (\v -> TSL.Update v (Var v (Vars.sortOf vars v))) $ Vars.stateVars vars

exactlyOneUpd :: Symbol -> Set Term -> [TSL.Formula]
exactlyOneUpd var updateTerms = map (TL.UExp TL.Globally) (atLeastOne : atMostOne)
  where
    updates = map (TL.Atom . TSL.Update var) (Set.toList updateTerms)
    atLeastOne = TL.Or updates
    atMostOne = go updates
    go =
      \case
        [] -> []
        [_] -> []
        x:y:xr -> TL.Not (TL.And [x, y]) : go (x : xr) ++ go (y : xr)

tsl2ltlMap :: Variables -> TSL.Formula -> (TSL.Formula, TSL.Atom -> String, String -> TSL.Atom)
tsl2ltlMap vars tslFormula = (TL.And (tslFormula : constr), (atoms2ap !), (ap2atoms !))
  where
    atoms = selfUpdates vars `Set.union` TL.atoms tslFormula
    upds = updates atoms
    constr = concatMap (uncurry exactlyOneUpd) (Map.toList upds)
    atomsAp = intmapSet (\n atom -> (atom, "ap" ++ show n)) atoms
    atoms2ap = Map.fromList atomsAp
    ap2atoms = Map.fromList (map swap atomsAp)

doa2game :: Variables -> (String -> TSL.Atom) -> DOA.DOA String -> (Game, Objective)
doa2game vars atomOf doa =
  let (game0, stateMap) = foldl addLocs (emptyGame, Map.empty) (DOA.states doa)
      mapState st = fromMaybe (error "unmapped DOA state") $ stateMap !? st
      game1 = foldl addVars game0 (Vars.inputs vars `Set.union` Vars.stateVars vars)
      game2 = foldl (addTrans mapState) game1 (DOA.states doa)
      init = mapState (DOA.initial doa)
      wc =
        case DOA.acceptance doa of
          DOA.Safety safe -> Obj.Safety $ Set.map mapState safe
          DOA.Buechi rep -> Obj.Buechi $ Set.map mapState rep
          DOA.Parity color -> Obj.Parity $ Map.mapKeys mapState color
   in (game2, Objective {initialLoc = init, winningCond = wc})
  where
    addLocs (game, stateMap) state =
      let (game', loc) = RPG.addLocation game (DOA.stateName state)
       in (game', Map.insert state loc stateMap)
    --
    addVars game var =
      case Vars.typeOf vars var of
        Vars.TInput sort -> fromMaybe game (RPG.addInput game var sort)
        Vars.TOutput sort -> fromMaybe game (RPG.addOutput game var sort False)
    --
    addTrans mapState game state =
      let doaTrans = DOA.trans doa state
          trans = doatran2tran (outputs game) mapState atomOf doaTrans
       in case addTransition game (mapState state) trans of
            Just game -> game
            Nothing -> error "assert: Transition should not already exist"

doatran2tran ::
     [Symbol]
  -> (DOA.State -> Loc)
  -> (String -> TSL.Atom)
  -> DOA.Transition String
  -> RPG.Transition
doatran2tran stateVars locOf atomOf = go
  where
    go doaTrans =
      case find (isPred . atomOf) $ DOA.transAPs doaTrans of
        Just ap ->
          let (doaTT, doaTF) = DOA.branch doaTrans ap
              tt = go doaTT
              tf = go doaTF
           in TIf (fromPred $ atomOf ap) tt tf
        Nothing ->
          let upds =
                mapMaybe (\(clause, q) -> (\u -> (u, locOf q)) <$> clause2update clause)
                  $ Set.toList doaTrans
           in TSys $ nub $ cleanUpdates upds
    --
    clause2update clause =
      let mapping =
            Map.fromListWith (++)
              $ map (second (: []) . fromUpdate . atomOf . fst) (filter snd (Set.toList clause))
       in if any ((/= 1) . length) mapping
            then Nothing
            else Just $ fmap head mapping
    -- 
    cleanUpdates upds =
      let filtered = filter (\(upd, _) -> all (`Map.member` upd) stateVars) upds
       in if null filtered
            then upds
            else filtered
    --
    isPred (TSL.Predicate _) = True
    isPred _ = False
    --
    fromPred (TSL.Predicate pred) = pred
    fromPred _ = error "fromPred applied to TSL.Update"
    --
    fromUpdate (TSL.Update var term) = (var, term)
    fromUpdate _ = error "fromUpdate applied to TSL.Predicate"

tsl2rpg :: Config -> TSL.Spec -> IO (Game, Objective)
tsl2rpg cfg spec = do
  let tsl = TSL.toFormula spec
  let vars = TSL.variables spec
  cfg <- pure $ setName "RPG2TSL" cfg
  lg cfg ["VARS:", show vars]
  lg cfg ["TSL:", show tsl]
  (tsl, ap2str, str2ap) <- pure $ tsl2ltlMap vars tsl
  doa <- LTL2DOA.translate cfg ap2str tsl
  lg cfg ["DOA:", show doa]
  simplifyRPG cfg $ doa2game vars str2ap doa
