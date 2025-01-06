{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Solver.Attractor
  ( attractor
  , attractorCache
  , attractorEx
  , CacheEntry(..)
  , Cache
  ) where

-------------------------------------------------------------------------------
import Control.Monad (filterM, foldM)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, generateProgram, setName)
import Issy.Logic.FOL (Symbol)
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.SMT (sat, simplify, valid)
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.Acceleration (accelReach)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import Issy.Solver.Heuristics (visits2accel)
import Issy.Utils.Logging
import Issy.Utils.OpenList (OpenList, pop, push)
import qualified Issy.Utils.OpenList as OL (fromSet)

-------------------------------------------------------------------------------
-- Accleration
-------------------------------------------------------------------------------
-- Caching / Hinting
-------------------------------------------------------------------------------
-- | 'CacheEntry' represents a piece of attractor computation that is assumed
-- to be true. Note that the game it refers to is  implicit and the correctness 
-- gas to be ensured by whoever provides the cache
data CacheEntry = CacheEntry
  { forPlayer :: Ply
  , independendCells :: Set Symbol
  , targetSt :: SymSt
  , cachedSt :: SymSt
  , involvedLocs :: Set Loc
  } deriving (Eq, Ord, Show)

type Cache = [CacheEntry]

-------------------------------------------------------------------------------
-- | 'applyEntry' checks if a cache entry is applicable to an intermediate
-- attractor computation step, and if it is applies it.
applyEntry :: Config -> Game -> Ply -> CacheEntry -> SymSt -> IO SymSt
applyEntry ctx game ply cache attrSt
  | ply /= forPlayer cache = return attrSt
  | otherwise = do
    ipred <- independedPred
    check <-
      allM (\l -> valid ctx (FOL.andf [targ l, ipred] `FOL.impl` (attrSt `get` l))) (locations game)
    if check
      then let newAttrSt =
                 SymSt.disjS attrSt $ SymSt.map (\f -> FOL.andf [ipred, f]) (cachedSt cache)
            in SymSt.simplify ctx newAttrSt
      else return attrSt
  where
    dependends = filter (`notElem` independendCells cache) $ Vars.stateVarL (vars game)
    targ l = targetSt cache `get` l
    -- This is only one choice for the independent program variables. However
    -- this seems awfully like we are computing an interpolant. Furthermore,
    -- it might be possible to use some cheaper syntactic stuff (like setting
    -- everything non-independent to "true")
    independLocPred l
      | targ l == FOL.false = return FOL.true
      | otherwise = simplify ctx $ FOL.forAll dependends (targ l `FOL.impl` (attrSt `get` l))
    -- 
    independedPred = do
      preds <- mapM independLocPred (Set.toList (locations game))
      simplify ctx (FOL.andf preds)
   -- 
    allM p =
      foldM
        (\val elem ->
           if val
             then p elem
             else return False)
        True

-------------------------------------------------------------------------------
-- | 'applyCache' transforms an attractor state after an update on a given 
-- location based on the 'Cache'.
applyCache :: Config -> Game -> Ply -> Cache -> SymSt -> Loc -> IO SymSt
applyCache ctx game player cache attrSt currentLoc = go attrSt cache
  where
    go symst =
      \case
        [] -> return symst
        ce:cer
          | currentLoc `notElem` involvedLocs ce -> go symst cer
          | otherwise -> do
            symst <- applyEntry ctx game player ce symst
            go symst cer

-------------------------------------------------------------------------------
-- Attractor Computation
-------------------------------------------------------------------------------
-- | 'attractorFull' does the complete attractor computation and is later used
-- for the different type of attractor computations (with/without extraction,
--  cache, ...). Note the for correctness it has to hold
--      null cache || not (generateProgram ctx)
--  Otherwise the generated program does not make any sense.
attractorFull :: Config -> Ply -> Game -> Cache -> SymSt -> IO (SymSt, CFG)
attractorFull ctx p g cache symst = do
  nf <- Set.fromList . map fst <$> filterM (sat ctx . snd) (SymSt.toList symst)
  lg ctx ["Attractor for", show p, "from", strS (locName g) nf, "starting in", strSt g symst]
  (res, cfg) <- attr (noVisits g) (OL.fromSet (predSet g nf)) symst (CFG.goalCFG symst)
  lg ctx ["Attractor result", strSt g res]
  return (res, cfg)
  where
    attr :: VisitCounter -> OpenList Loc -> SymSt -> CFG -> IO (SymSt, CFG)
    attr vc o st cfg =
      case pop o of
        Nothing -> return (st, cfg)
        Just (l, no) -> do
          let fo = st `get` l
          lg ctx ["Step in", locName g l, "with", smtLib2 fo]
          -- Enforcable predecessor step
          fn <- simplify ctx (FOL.orf [cpre p g st l, fo])
          lg ctx ["Compute new", smtLib2 fn]
          let st' = set st l fn
          let vc' = visit l vc
          -- Check if this changed something in this location
          unchanged <- valid ctx (fn `FOL.impl` fo)
          lg ctx ["which has not changed (", show unchanged, ")"]
          if unchanged
            then rec vc' no st cfg
            else do
              cfg <- extr (CFG.addUpd st g l cfg)
              cfg <- simpCFG cfg
              -- Caching 
              (st', cached) <-
                if any ((== p) . forPlayer) cache
                  then do
                    st'' <- applyCache ctx g p cache st' l
                    cached <-
                      filterM
                        (\l -> sat ctx (FOL.andf [st'' `get` l, FOL.neg (st' `get` l)]))
                        (SymSt.locations st)
                    return (st'', cached)
                  else return (st', [])
              lg ctx ["Cached", strL (locName g) cached]
              -- Compute potential new locations 
              let on' = Set.unions (preds g <$> cached) `push` (preds g l `push` no)
              -- Check if we accelerate
              if accelNow l fo vc' && canAccel g && null cached --DEBUG!
                  -- Acceleration
                then do
                  lg ctx ["Attempt reachability acceleration"]
                  (acc, cfgSub) <- accelReach ctx (visits l vc') p g l st'
                  lg ctx ["Accleration formula", smtLib2 acc]
                  res <- simplify ctx (FOL.orf [fn, acc])
                  succ <- not <$> valid ctx (res `FOL.impl` fn)
                  lg ctx ["Accelerated:", show succ]
                  if succ
                      -- Acceleration succeed
                    then do
                      cfg <- extr (CFG.integrate cfgSub cfg)
                      cfg <- simpCFG cfg
                      rec vc' on' (set st' l res) cfg
                    else rec vc' on' st' cfg
                else rec vc' on' st' cfg
      where
        rec h o st cfg = do
          attr h o st cfg
        accelNow l fo vc = (g `cyclicIn` l) && (fo /= FOL.false) && visits2accel (visits l vc)
        extr cfg
          | generateProgram ctx = pure cfg
          | otherwise = pure CFG.empty
        simpCFG cfg
          | generateProgram ctx = CFG.simplify ctx cfg
          | otherwise = pure cfg

canAccel :: Game -> Bool
canAccel g = any (\v -> FOL.isNumber (sortOf g v) && not (boundedVar g v)) (stateVars g)

-------------------------------------------------------------------------------
-- | 'attractor' compute the attractor for a given player, game, and symbolic
-- state
attractor :: Config -> Ply -> Game -> SymSt -> IO SymSt
attractor ctx p g symst = do
  ctx <- pure $ setName "Attr" ctx
  fst <$> attractorFull (ctx {generateProgram = False}) p g [] symst

-------------------------------------------------------------------------------
-- | 'attractorCache' compute the attractor for a given player, game, 
-- and symbolic state provided with a cache that it assumes to be true for
-- this game 
attractorCache :: Config -> Ply -> Game -> Cache -> SymSt -> IO SymSt
attractorCache ctx p g cache symst = do
  ctx <- pure $ setName "AttrCached" ctx
  fst <$> attractorFull (ctx {generateProgram = False}) p g cache symst

-------------------------------------------------------------------------------
-- | 'attractorEx' compute the attractor for a given player, game, and symbolic
-- state and does program extraction if indicated in the 'Config'. If it does 
-- program extraction the cache is not used.
attractorEx :: Config -> Cache -> Ply -> Game -> SymSt -> IO (SymSt, CFG)
attractorEx ctx cache p g
  | generateProgram ctx = do
    ctx <- pure $ setName "AttrExtract" ctx
    attractorFull ctx p g []
  | otherwise = do
    ctx <- pure $ setName "AttrCached" ctx
    attractorFull ctx p g cache
-------------------------------------------------------------------------------
