{-# LANGUAGE LambdaCase #-}

module Issy.Monitor.Postprocess
  ( finish
  ) where

import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Config (Config)
import Issy.Monitor.Formula
  ( Formula(FAnd, FEventually, FGlobally, FOr)
  , feventually
  , fglobally
  , formulaToString
  , ftrue
  , substNotNested
  )
import Issy.Monitor.Monitor
import Issy.Monitor.Rules (derivedEventually)
import Issy.Monitor.State (Domain(..), fset, isSafeSt, mapFs, normSt, stateToString)
import qualified Issy.Monitor.State as M (State)
import Issy.Utils.Extra
import Issy.Utils.Logging

-------------------------------------------------------------------------------
-- for all GF pred, search reachables 
-- parts with (F pred derived) not derived remove 
-- them, for all other remove GF pred"
finish :: Config -> Monitor -> IO Monitor
finish cfg mon = do
  mon <- pure $ mon {revLabel = Map.empty}
  lg cfg ["Before discharge", strM (stateName mon) stateToString (stateLabel mon)]
  mon <- dischargeGFs cfg mon
  lg cfg ["After discharge", strM (stateName mon) stateToString (stateLabel mon)]
  pure $ markSafes mon

markSafes :: Monitor -> Monitor
markSafes mon =
  let predrel = statePred mon
      pred st = fromMaybe (error ("assert: found no pred for " ++ show st)) (predrel !? st)
      notSafes = Set.filter (not . isSafeSt . label mon) (states mon)
   in mon {safes = states mon `Set.difference` reachables pred notSafes}

statePred :: Monitor -> Map State (Set State)
statePred mon =
  let succRel = stateSucc mon
      succ st = Map.findWithDefault Set.empty st succRel
   in predecessorRelation succ $ states mon

stateSucc :: Monitor -> Map State (Set State)
stateSucc mon =
  Map.fromListWith Set.union
    $ map (\((st, _), tree) -> (st, Set.fromList (map snd (concat (leafs tree)))))
    $ Map.toList
    $ stateTrans mon

states :: Monitor -> Set State
states = Map.keysSet . stateLabel

dischargeGFs :: Config -> Monitor -> IO Monitor
dischargeGFs cfg mon = do
  eventMap <-
    mapM
      (\st -> do
         (events, _) <- derivedEventually cfg (ctx mon) Guarantees (label mon st)
         pure (st, events))
      $ Set.toList
      $ states mon
  eventMap <- pure $ Map.fromList eventMap
  lg cfg ["Discharge Map:", strM (stateName mon) (strL formulaToString) eventMap]
  let checkEvents st =
        case eventMap !? st of
          Just fs -> fs
          Nothing -> error $ "assert: found unmapped st " ++ show st
  pure $ foldl (dischargeGF checkEvents) mon (findGFs mon)

dischargeGF :: (State -> [Formula]) -> Monitor -> Formula -> Monitor
dischargeGF eventuallies mon inner =
  let gf = fglobally (feventually inner)
      fNotDischarged = Set.filter ((inner `notElem`) . eventuallies) (states mon)
      notDischarged = fNotDischarged `Set.difference` Set.fromList [goodState mon, badState mon]
      succRel = stateSucc mon
      succ st = Map.findWithDefault Set.empty st succRel
      dischargable = states mon `Set.difference` reachables succ notDischarged
   in foldl (mapLabel (\stl -> mapFs Guarantees stl (substNotNested gf ftrue))) mon dischargable

mapLabel :: (M.State -> M.State) -> Monitor -> State -> Monitor
mapLabel labelMap mon st =
  mon {stateLabel = Map.update (Just . normSt . labelMap) st (stateLabel mon)}

findGFs :: Monitor -> Set Formula
findGFs mon =
  Set.unions $ map go $ concatMap (fset Guarantees . label mon) $ Set.toList $ states mon
  where
    go =
      \case
        FAnd fs -> Set.unions $ map go fs
        FOr fs -> Set.unions $ map go fs
        FGlobally (FEventually inner) -> Set.singleton inner
        _ -> Set.empty
