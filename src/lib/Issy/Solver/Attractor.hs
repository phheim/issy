---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Solver.Attractor
-- Description : Implementation of top-level attractor computation
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Solver.Attractor
  ( SolSt(stats)
  , StopCheck
  , emptySolSt
  , attractor
  , attractorEx
  , noCheck
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Config (accelerate, enforcementSummaries, generateProgram)
import qualified Issy.Games.SymbolicState as SymSt
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib (toString)
import Issy.Solver.Acceleration (accelReach, canAccel)
import Issy.Solver.EnforcementSummaries (EnfSt, trySummary)
import qualified Issy.Solver.EnforcementSummaries as EnfSum
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Statistics (Stats)
import qualified Issy.Statistics as Stats
import Issy.Utils.Extra (ifM, justOn, orM)
import Issy.Utils.OpenList (OpenList)
import qualified Issy.Utils.OpenList as OL

---------------------------------------------------------------------------------------------------
-- The top level interface
---------------------------------------------------------------------------------------------------
-- | Solver state
data SolSt = SolSt
  { stats :: Stats
  , enfst :: EnfSt
  }

emptySolSt :: Stats -> SolSt
emptySolSt stats = SolSt {stats = stats, enfst = EnfSum.empty}

type StopCheck = Maybe (Loc -> SymSt -> IO Bool)

noCheck :: StopCheck
noCheck = Nothing

-- | 'attractor' compute the attractor for a given player, game, and symbolic state
attractor :: Config -> SolSt -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, SolSt)
attractor cfg solst player arena stopCheck target = do
  cfg <- pure $ setName "Attr" $ cfg {generateProgram = False}
  (res, solst, _) <- attractorFull cfg solst player arena stopCheck target
  pure (res, solst)

-- | 'attractorEx' compute the attractor for a given player, game, and symbolic state and does
-- program extraction if indicated in the 'Config'.
attractorEx :: Config -> SolSt -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, SolSt, SyBo)
attractorEx cfg solst player arena stopCheck target = do
  cfg <-
    pure
      $ if generateProgram cfg
          then setName "AttrE" cfg
          else setName "Attr" cfg
  attractorFull cfg solst player arena stopCheck target

---------------------------------------------------------------------------------------------------
-- | 'attractorFull' does the complete attractor computation and is later used for the different
-- type of attractor computations (with/without extraction)
attractorFull :: Config -> SolSt -> Player -> Arena -> StopCheck -> SymSt -> IO (SymSt, SolSt, SyBo)
attractorFull cfg solst player arena stopCheck =
  attrState cfg solst stopCheck Nothing player arena >=> fullAttr cfg >=> attrResult cfg

---------------------------------------------------------------------------------------------------
-- Attractors are computed as chaotic fixpoints
---------------------------------------------------------------------------------------------------
class FixPointSt a where
  open :: a -> Maybe (Loc, a)
  addOpen :: Set Loc -> a -> a
  markVisit :: Loc -> a -> a
  doStop :: Loc -> a -> IO Bool
  visitCnt :: Loc -> a -> Int

attrFP :: FixPointSt a => (a -> Loc -> IO a) -> a -> IO a
attrFP step ast =
  case open ast of
    Nothing -> pure ast
    Just (loc, ast) -> do
      ast <- pure $ markVisit loc ast
      ifM (doStop loc ast) (pure ast) $ attrFP step =<< step ast loc

---------------------------------------------------------------------------------------------------
-- Attractors need at least the enforcable predecessors
---------------------------------------------------------------------------------------------------
class FixPointSt a =>
      AttrSt a
  where
  arena :: a -> Arena
  player :: a -> Player
  reach :: a -> SymSt
  prog :: a -> SyBo
  setIn :: Loc -> Term -> a -> a
  setProg :: SyBo -> a -> a

enforce :: AttrSt a => Config -> a -> Loc -> IO (Maybe a)
enforce conf ast l = do
  let old = reach ast `get` l
  lgd conf ["Step in", locName (arena ast) l, "with", SMTLib.toString old]
  new <- SMT.simplify conf $ FOL.orf [cpre (player ast) (arena ast) (reach ast) l, old]
  lgd conf ["Compute new", SMTLib.toString new]
  changed <- fmap not $ SMT.valid conf $ new `FOL.impl` old
  lgd conf ["which has changed?", show changed]
  pure
    $ justOn changed
    $ addOpen (preds (arena ast) l)
    $ setIn l new
    $ setProg (Synt.enforceTo l new (reach ast) (prog ast)) ast

---------------------------------------------------------------------------------------------------
-- Attractors can be accelerated
---------------------------------------------------------------------------------------------------
class AttrSt a =>
      AccAttrSt a
  where
  markAccelTry :: Loc -> a -> a
  markAccelSuc :: Loc -> a -> a
  doAccel :: Loc -> a -> Bool
  markEnforcementChange :: Loc -> a -> a
  reachAccel :: Loc -> a -> SymSt
  reachAccelNum :: Loc -> a -> Int

accel :: AccAttrSt a => Config -> a -> Loc -> IO (Maybe a)
accel conf ast l = do
  let tries = reachAccelNum l ast
  lg conf ["Try acceleration in", locName (arena ast) l, "(", show tries, "times)"]
  (acc, progSub) <- accelReach conf tries (player ast) (arena ast) l (reachAccel l ast)
  lg conf ["Accleration formula", SMTLib.toString acc]
  res <- SMT.simplify conf $ FOL.orf [get (reach ast) l, acc]
  succ <- not <$> SMT.valid conf (res `FOL.impl` get (reach ast) l)
  lg conf ["Accelerated:", show succ]
  pure
    $ justOn succ
    $ addOpen (preds (arena ast) l)
    $ setIn l res
    $ setProg (Synt.callOn l acc progSub (prog ast))
    $ markAccelSuc l ast

tryAccel :: AccAttrSt a => Config -> a -> Loc -> IO a
tryAccel conf ast l = markAccelTry l . fromMaybe ast <$> accel conf ast l

accelAttr :: AccAttrSt a => Config -> a -> IO a
accelAttr = attrFP . accelStep

accelStep :: AccAttrSt a => Config -> a -> Loc -> IO a
accelStep conf ast loc = do
  mast <- fmap (markEnforcementChange loc) <$> enforce conf ast loc
  case mast of
    Nothing -> pure ast
    Just ast
      | accelerate conf && canAccel (arena ast) loc && doAccel loc ast -> tryAccel conf ast loc
      | otherwise -> pure ast

accelAttractor :: Maybe Int -> Config -> Player -> Arena -> SymSt -> IO (SymSt, SyBo)
accelAttractor limit conf player arena reach =
  attrState conf (emptySolSt (Stats.emptyStats conf)) Nothing limit player arena reach
    >>= accelAttr conf
    >>= attrResult conf <&> (\(reach, _, prog) -> (reach, prog))

---------------------------------------------------------------------------------------------------
-- Attractors can addtionally have enforcement summaries
---------------------------------------------------------------------------------------------------
class AccAttrSt a =>
      AccSumAttrSt a
  where
  getEnfst :: a -> EnfSt
  setEnfst :: EnfSt -> a -> a
  markSumApp :: Loc -> a -> a

accelSum :: AccSumAttrSt a => Config -> a -> Loc -> IO (a, Bool)
accelSum conf ast l = do
  (enfstRes, msum) <-
    trySummary
      conf
      (accelAttractor sumSteps)
      (player ast)
      (arena ast)
      l
      (getEnfst ast)
      (reachAccel l ast)
  ast <- pure $ setEnfst enfstRes ast
  case msum of
    Nothing -> pure (ast, False) -- Summary was not found and could not be computed either
    Just (sum, subProg) -> do
      extended <- SMT.sat conf $ FOL.andf [sum, FOL.neg (get (reach ast) l)]
      if extended
        then do
          new <- SMT.simplify conf $ FOL.orf [get (reach ast) l, sum]
          ast <-
            pure $ markSumApp l $ setProg (Synt.callOn l sum subProg (prog ast)) $ setIn l new ast
          pure (ast, True)
        else pure (ast, False)

fullAttr :: AccSumAttrSt a => Config -> a -> IO a
fullAttr = attrFP . fullStep

fullStep :: AccSumAttrSt a => Config -> a -> Loc -> IO a
fullStep conf ast loc = do
  mast <- fmap (markEnforcementChange loc) <$> enforce conf ast loc
  case mast of
    Nothing -> pure ast
    Just ast
      | accelerate conf && canAccel (arena ast) loc && doAccel loc ast ->
        if enforcementSummaries conf
          then do
            (ast, succ) <- accelSum conf ast loc
            if succ
              then pure ast
              else tryAccel conf ast loc
          else tryAccel conf ast loc
      | otherwise -> pure ast

---------------------------------------------------------------------------------------------------
-- The concrete attractor state(s)
---------------------------------------------------------------------------------------------------
data AttrState = AttrState
  { stArena :: Arena
  , stPlayer :: Player
  , stReach :: SymSt
  , stProg :: SyBo
  , stOpen :: OpenList Loc
  , vsCnt :: VisitCounter
  , stStats :: Stats
  , stEnfst :: EnfSt
  , stopCheck :: StopCheck
  , visitLimit :: Maybe Int
  , history :: Map Loc [SymSt]
  , accelsIn :: Map Loc Int
  }

instance FixPointSt AttrState where
  open ast = second (\ol -> ast {stOpen = ol}) <$> OL.pop (stOpen ast)
  addOpen locs ast = ast {stOpen = OL.push locs (stOpen ast)}
  doStop loc ast =
    let reachedTarget =
          case stopCheck ast of
            Nothing -> pure False
            Just check -> check loc $ reach ast
        reachedVistitLimit = pure $ maybe False (totalVisits (vsCnt ast) >=) (visitLimit ast)
     in reachedVistitLimit `orM` reachedTarget
  markVisit loc ast = ast {vsCnt = visit loc (vsCnt ast)}
  visitCnt loc = visits loc . vsCnt -- REMAKR previous herusitc had old /= FOL.false addionally

instance AttrSt AttrState where
  arena = stArena
  player = stPlayer
  reach = stReach
  prog = stProg
  setIn loc term ast = ast {stReach = set (stReach ast) loc term}
  setProg prog ast = ast {stProg = prog}

instance AccAttrSt AttrState where
  markAccelTry loc ast =
    ast
      { stStats = Stats.statCnt "Acceleration Attempts" (stStats ast)
      , accelsIn = Map.insertWith (+) loc 1 (accelsIn ast)
      }
  markAccelSuc _ ast = ast {stStats = Stats.statCnt "Acceleration Success" (stStats ast)}
  doAccel loc = visits2accel . visitCnt loc
  markEnforcementChange loc ast =
    case history ast !? loc of
      Nothing -> ast {history = Map.insert loc [reach ast] (history ast)}
            -- This could turn sour for longer running times!!
            -- Both in terms of time and memory efficency!
      Just hist -> ast {history = Map.insert loc (hist ++ [reach ast]) (history ast)}
  reachAccel _ = reach
  reachAccelNum loc ast = Map.findWithDefault 0 loc (accelsIn ast)

--    case history ast !? loc of
--      Nothing -> error "assert: only accelerate after marking an enforcement change"
--      Just history ->
--        let k = reachAccelNum loc ast
--         in if k >= length history
--              then error "assert: acceleration should not happend that oftern"
--              else history !! k
instance AccSumAttrSt AttrState where
  getEnfst = stEnfst
  setEnfst enfst ast = ast {stEnfst = enfst}
  markSumApp _ ast = ast {stStats = Stats.statCnt "Summary Applications" (stStats ast)}

attrState :: Config -> SolSt -> StopCheck -> Maybe Int -> Player -> Arena -> SymSt -> IO AttrState
attrState conf solst stopCheck visitLimit player arena reach = do
  satLocs <- Set.fromList . map fst <$> filterM (SMT.sat conf . snd) (SymSt.toList reach)
  lg conf ["Attractor for", show player, "from", strLocs satLocs, "to reach", strStA reach]
  let prog = Synt.returnOn reach $ Synt.normSyBo conf arena
  pure
    $ AttrState
        { stArena = arena
        , stPlayer = player
        , stReach = reach
        , stProg = prog
        , stOpen = OL.fromSet (predSet arena satLocs)
        , vsCnt = noVisits arena
        , stStats = stats solst
        , stEnfst = enfst solst
        , stopCheck = stopCheck
        , visitLimit = visitLimit
        , history = Map.empty
        , accelsIn = Map.empty
        }
  where
    strLocs = strS (locName arena)
    strStA = strSt arena

attrResult :: Config -> AttrState -> IO (SymSt, SolSt, SyBo)
attrResult conf ast = do
  lg conf ["Result", strSt (arena ast) (reach ast)]
  pure (stReach ast, SolSt {enfst = stEnfst ast, stats = stStats ast}, stProg ast)

---------------------------------------------------------------------------------------------------
-- Heuristics
---------------------------------------------------------------------------------------------------
--accelNow :: Loc -> Term -> VisitCounter -> Bool
--accelNow l f vcnt = (f /= FOL.false) && visits2accel (visits l vcnt)
accelerationDist :: Int
accelerationDist = 4

sumSteps :: Maybe Int
sumSteps = Just $ accelerationDist * 3

visits2accel :: Int -> Bool
visits2accel k = (k < accelerationDist) || (k `mod` accelerationDist == 0)
---------------------------------------------------------------------------------------------------
