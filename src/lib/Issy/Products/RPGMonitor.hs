{-# LANGUAGE LambdaCase #-}

module Issy.Products.RPGMonitor
  ( onTheFlyProduct
  ) where

import Data.List (nub)
import Data.Map.Strict (Map, (!), (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set (empty, filter, insert, map)
import qualified Issy.Utils.OpenList as OL (fromList, pop, pushList)

import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import Issy.Base.Variables hiding (inputs)
import qualified Issy.Base.Variables as Vars (inputs)
import Issy.Config (Config, setName)
import Issy.Logic.FOL
import Issy.Monitor
  ( Monitor
  , State
  , Trans(..)
  , Verdict(..)
  , finish
  , generateSuccessor
  , leafs
  , stateName
  , verdict
  )
import qualified Issy.Monitor as Monitor (initial, variables)
import Issy.RPG
import qualified Issy.RPG as RPG
import Issy.Utils.Logging

onTheFlyProduct :: Config -> Game -> Objective -> Monitor -> IO (Game, Objective)
onTheFlyProduct cfg game obj monitor = do
  cfg <- pure $ setName "RPG x Monitor" cfg
  case checkDomain game monitor of
    Just err -> fail ("assert: " ++ err)
    Nothing -> do
      (monitor, product) <- explore cfg game (initialLoc obj) monitor
      lg cfg [show product]
      monitor <- finish cfg monitor
      let (prodGame, winEnv, winSys, toNew) = productToGame game monitor product
      let wc = winningCond obj
      let prodWC = newWC (winEnv, winSys) (explored product) (verdict monitor) toNew wc
      let prodInit = toNew $ initLocState (initialLoc obj) monitor
      let prodObj = Objective {initialLoc = prodInit, winningCond = prodWC}
      simplifyRPG cfg (prodGame, prodObj)

-- checks if the game and monitor have the same symbols and updates and so
checkDomain :: Game -> Monitor -> Maybe String
checkDomain game mon =
  if all (`elem` RPG.inputs game) (Vars.inputs (Monitor.variables mon))
       && all (`elem` RPG.outputs game) (stateVars (Monitor.variables mon))
    then Nothing
    else Just "found variables in monitor not present in game"

-- Intermediate product data-structure
data Product = Product
  { explored :: Set (Loc, State)
  , interTrans :: [(Loc, State, Trans [(Map Symbol Term, Loc, State)])]
  } deriving (Eq, Ord, Show)

emptyProd :: Product
emptyProd = Product {explored = Set.empty, interTrans = []}

initLocState :: Loc -> Monitor -> (Loc, State)
initLocState init monitor = (init, Monitor.initial monitor)

explore :: Config -> Game -> Loc -> Monitor -> IO (Monitor, Product)
explore cfg game init mon = go (OL.fromList [initLocState init mon]) mon emptyProd
  where
    go openList mon prod =
      case OL.pop openList of
        Nothing -> return (mon, prod)
        Just ((l, q), openList)
          | (l, q) `elem` explored prod -> go openList mon prod
          | otherwise -> do
            (transition, mon) <- traversTransition cfg mon q (tran game l)
            let openList' =
                  OL.pushList
                    (filter ((`notElem` [VALID, UNSAFE]) . verdict mon . snd)
                       $ filter (`notElem` explored prod)
                       $ map (\(_, l', q') -> (l', q'))
                       $ concat
                       $ leafs transition)
                    openList
            go openList' mon
              $ prod
                  { explored = Set.insert (l, q) (explored prod)
                  , interTrans = (l, q, transition) : interTrans prod
                  }

traversTransition ::
     Config -> Monitor -> State -> Transition -> IO (Trans [(Map Symbol Term, Loc, State)], Monitor)
traversTransition cfg mon state = go [] mon
  where
    go conditions mon =
      \case
        TIf p tt tf -> do
          (tt', mon) <- go ((p, True) : conditions) mon tt
          (tf', mon) <- go ((p, False) : conditions) mon tf
          return (TrIf p tt' tf', mon)
        TSys upds -> do
          (mon, trans) <- generateSuccessor cfg mon state conditions
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
            Nothing -> isSelfUpdate (v, tm) && validComb upd ur
        -- Update in monitor not active
        (False, v, tm):ur ->
          case upd !? v of
            Just t -> t /= tm && validComb upd ur
            Nothing -> not (isSelfUpdate (v, tm)) && validComb upd ur

-- TODO: Maybe move this
isSelfUpdate :: (Symbol, Term) -> Bool
isSelfUpdate (v, Var s _) = s == v
isSelfUpdate _ = False

-- TODO: Maybe move this to RPG construction
createLocations :: Ord a => Game -> Set a -> (a -> String) -> (a -> Term) -> (Game, Map a Loc)
createLocations game elems elemName elemInv = foldl add (game, Map.empty) elems
  where
    add (g, m) a =
      let (g0, l) = addLocation g (elemName a)
          g1 = setInv g0 l (elemInv a)
       in (g1, Map.insert a l m)

-- TODO: Maybe move this to RPG construction
addTrivialWins :: Game -> (Game, Loc, Loc)
addTrivialWins game =
  let (g0, winEnv) = addLocation game "winEnv"
      (g1, winSys) = addLocation g0 "winSys"
      g2 = fromJust $ addTransition g1 winSys (TSys [(Map.empty, winSys)])
      g3 = fromJust $ addTransition g2 winEnv (TSys [(Map.empty, winEnv)])
   in (g3, winEnv, winSys)

productToGame :: Game -> Monitor -> Product -> (Game, Loc, Loc, (Loc, State) -> Loc)
productToGame game mon prod =
  let g0 = sameSymbolGame game
      (g1, winEnv, winSys) = addTrivialWins g0
      (g2, mp) =
        createLocations
          g1
          (explored prod)
          (\(l, q) -> locName game l ++ stateName mon q)
          (\(l, _) -> game `inv` l)
      oldToNew old = fromMaybe (error ("assert: unmapped " ++ show old)) (mp !? old)
      mkTrans = transToTransition winEnv winSys oldToNew (verdict mon)
      g3 =
        foldl
          (\g (l, q, tr) -> fromJust $ addTransition g (oldToNew (l, q)) (mkTrans tr))
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
