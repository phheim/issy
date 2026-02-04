---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Products.RPGMonitor
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Products.RPGMonitor
  ( onTheFlyProduct
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude
import qualified Issy.Utils.OpenList as OL

import Issy.Games.Objectives (Objective(..), WinningCondition(..))
import Issy.Games.ReactiveProgramArena (RPArena, Transition(..))
import qualified Issy.Games.ReactiveProgramArena as RPG
import Issy.Monitor (Monitor, State, Trans(..), Verdict(..))
import qualified Issy.Monitor as Mon

onTheFlyProduct :: Config -> RPArena -> Objective -> Monitor -> IO (RPArena, Objective)
onTheFlyProduct cfg game obj monitor = do
  cfg <- pure $ setName "RPG x Monitor" cfg
  unless (Mon.variables monitor == RPG.variables game)
    $ error "assert: found variables in monitor not present in game"
  (monitor, product) <- explore cfg game (initialLoc obj) monitor
  lg cfg [show product]
  monitor <- Mon.finish cfg monitor
  let (prodGame, winEnv, winSys, toNew) = productToGame game monitor product
  let wc = winningCond obj
  let prodWC = newWC (winEnv, winSys) (explored product) (Mon.verdict monitor) toNew wc
  let prodInit = toNew $ initLocState (initialLoc obj) monitor
  let prodObj = Objective {initialLoc = prodInit, winningCond = prodWC}
  RPG.simplifyRPG cfg (prodGame, prodObj)

-- Intermediate product data-structure
data Product = Product
  { explored :: Set (Loc, State)
  , interTrans :: [(Loc, State, Trans [(Map Symbol Term, Loc, State)])]
  } deriving (Eq, Ord, Show)

emptyProd :: Product
emptyProd = Product {explored = Set.empty, interTrans = []}

initLocState :: Loc -> Monitor -> (Loc, State)
initLocState init monitor = (init, Mon.initial monitor)

explore :: Config -> RPArena -> Loc -> Monitor -> IO (Monitor, Product)
explore cfg game init mon = go (OL.fromList [initLocState init mon]) mon emptyProd
  where
    go openList mon prod =
      case OL.pop openList of
        Nothing -> return (mon, prod)
        Just ((l, q), openList)
          | (l, q) `elem` explored prod -> go openList mon prod
          | otherwise -> do
            (transition, mon) <- traversTransition cfg mon q $ RPG.trans game l
            let openList' =
                  OL.pushList
                    (filter ((`notElem` [VALID, UNSAFE]) . Mon.verdict mon . snd)
                       $ filter (`notElem` explored prod)
                       $ map (\(_, l', q') -> (l', q'))
                       $ concat
                       $ Mon.leafs transition)
                    openList
            go openList' mon
              $ prod
                  { explored = Set.insert (l, q) (explored prod)
                  , interTrans = (l, q, transition) : interTrans prod
                  }

traversTransition ::
     Config -> Monitor -> State -> Transition -> IO (Trans [(Map Symbol Term, Loc, State)], Monitor)
traversTransition cfg mon state = go Set.empty mon
  where
    go conditions mon =
      \case
        TIf p tt tf -> do
          (tt', mon) <- go (Set.insert (p, True) conditions) mon tt
          (tf', mon) <- go (Set.insert (p, False) conditions) mon tf
          return (TrIf p tt' tf', mon)
        TSys upds -> do
          (mon, trans) <- Mon.generateSuccessor cfg mon state conditions
          return (fmap (combs upds) trans, mon)
    --
    combs ::
         [(Map Symbol Term, Loc)]
      -> [([(Bool, Symbol, Term)], State)]
      -> [(Map Symbol Term, Loc, State)]
    combs upds mupds = [(upd, l, q) | (upd, l) <- upds, (mupd, q) <- mupds, validComb upd mupd]
    --
    validComb :: Map Symbol Term -> [(Bool, Symbol, Term)] -> Bool
    validComb upd =
      \case
        [] -> True
        -- Update in monitor active
        (True, v, tm):ur ->
          case upd !? v of
            Just t -> t == tm && validComb upd ur
            Nothing -> RPG.isSelfUpdate (v, tm) && validComb upd ur
        -- Update in monitor not active
        (False, v, tm):ur ->
          case upd !? v of
            Just t -> t /= tm && validComb upd ur
            Nothing -> not (RPG.isSelfUpdate (v, tm)) && validComb upd ur
    --

productToGame :: RPArena -> Monitor -> Product -> (RPArena, Loc, Loc, (Loc, State) -> Loc)
productToGame game mon prod =
  let (g0, winEnv) = RPG.addSink (RPG.empty (RPG.variables game)) "winEnv"
      (g1, winSys) = RPG.addSink g0 "winSys"
      (g2, oldToNew) =
        RPG.createLocsFor
          g1
          (\(l, q) -> RPG.locName game l ++ Mon.stateName mon q)
          (\(l, _) -> game `RPG.inv` l)
          (explored prod)
      mkTrans = transToTransition winEnv winSys oldToNew $ Mon.verdict mon
      g3 =
        foldl
          (\g (l, q, tr) -> fromJust $ RPG.addTransition g (oldToNew (l, q)) (mkTrans tr))
          g2
          (interTrans prod)
   in (g3, winEnv, winSys, oldToNew)

transToTransition ::
     Loc
  -> Loc
  -> ((Loc, State) -> Loc)
  -> (State -> Verdict)
  -> Trans [(Map Symbol Term, Loc, State)]
  -> Transition
transToTransition winEnv winSys oldToNew verdict = cleanupTransition winEnv . go
  where
    go =
      \case
        TrIf p tt tf -> TIf p (go tt) (go tf)
        TrSucc [] -> TSys [(Map.empty, winEnv)]
        TrSucc upds ->
          TSys
            $ nub
            $ map
                (\(upd, l, q) ->
                   case verdict q of
                     UNSAFE -> (upd, winEnv)
                     VALID -> (upd, winSys)
                     _ -> (upd, oldToNew (l, q)))
                upds

cleanupTransition :: Loc -> Transition -> Transition
cleanupTransition winEnv = go
  where
    go =
      \case
        TSys upd ->
          case filter ((/= winEnv) . snd) upd of
            [] -> TSys [(Map.empty, winEnv)]
            upd -> TSys upd
        TIf p tt tf ->
          let (tt', tf') = (go tt, go tf)
           in if tt' == tf'
                then tt'
                else TIf p tt' tf'

newWC ::
     (Loc, Loc)
  -> Set (Loc, State)
  -> (State -> Verdict)
  -> ((Loc, State) -> Loc)
  -> WinningCondition
  -> WinningCondition
newWC (winEnv, winSys) prods verdict toNew =
  \case
    Safety olds -> Safety $ winSet olds safety
    Reachability _ -> error "IMPLEMENT FIXME"
    Buechi olds -> Buechi $ winSet olds buechi
    CoBuechi olds -> CoBuechi $ winSet olds coBuechi
    Parity oldCol ->
      Parity
        $ Map.insert winSys 1
        $ Map.insert winEnv 0
        $ Map.mapKeys toNew
        $ Map.fromSet (parity oldCol) prods
  where
    winSet old pred =
      Set.insert
        winSys
        (Set.map toNew (Set.filter (\(l, q) -> pred (l `elem` old, verdict q)) prods))
    --
    safety (lin, ver) = lin && (ver /= UNSAFE) || ver == VALID
    buechi (lin, ver) = lin && (ver /= UNSAFE) || ver `elem` [VALID, SAFETY]
    coBuechi (lin, ver) = lin && (ver /= UNSAFE) || ver `elem` [VALID, SAFETY]
    --
    parity oldCol (l, q) =
      case verdict q of
        OPEN -> oldCol ! l
        SAFETY -> 1
        VALID -> 1
        UNSAFE -> 0
---------------------------------------------------------------------------------------------------
