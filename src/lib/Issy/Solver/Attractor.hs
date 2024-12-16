{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Solver.Attractor
  ( Ply(..)
  , opponent
  , attractor
  , attractorCache
  , attractorEx
  , cpreS
  , CacheEntry(..)
  , Cache
  ) where

import Control.Monad (filterM, foldM, unless)

-------------------------------------------------------------------------------
import Data.Map.Strict (Map, findWithDefault, fromSet)
import qualified Data.Map.Strict as Map (insertWith)
import Data.Set (Set, union, unions)
import qualified Data.Set as Set (fromList, toList)

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, generateProgram, setName)
import Issy.Logic.FOL
import Issy.Logic.SMT (sat, simplify, valid)
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
  ( Game
  , Loc
  , boundedVar
  , cpreEnv
  , cpreSys
  , cyclicIn
  , inv
  , locName
  , locations
  , loopGame
  , predSet
  , preds
  , sortOf
  , stateVarL
  , stateVars
  , strSt
  , usedSymbols
  , vars
  )
import Issy.Solver.Heuristics
import Issy.Solver.LemmaFinding (Constraint, LemSyms(..), replaceLemma, resolve)
import Issy.Utils.Logging
import Issy.Utils.OpenList (OpenList, pop, push)
import qualified Issy.Utils.OpenList as OL (fromSet)

-------------------------------------------------------------------------------
-- Enforcement Relations
-------------------------------------------------------------------------------
data Ply
  = Sys
  | Env
  deriving (Eq, Ord, Show)

opponent :: Ply -> Ply
opponent =
  \case
    Sys -> Env
    Env -> Sys

cpre :: Ply -> Game -> SymSt -> Loc -> Term
cpre p =
  case p of
    Sys -> cpreSys
    Env -> cpreEnv

cpreS :: Config -> Ply -> Game -> SymSt -> IO SymSt
cpreS ctx p g st = SymSt.simplify ctx (SymSt.symSt (locations g) (cpre p g st))

-------------------------------------------------------------------------------
-- Visit Counting
-------------------------------------------------------------------------------
type VisitCounter = Map Loc Int

noVisits :: Game -> VisitCounter
noVisits g = fromSet (const 0) (locations g)

visit :: Loc -> VisitCounter -> VisitCounter
visit l = Map.insertWith (+) l 1

visits :: Loc -> VisitCounter -> Int
visits = findWithDefault 0

-------------------------------------------------------------------------------
-- Accleration
-------------------------------------------------------------------------------
data UsedSyms =
  UsedSyms (Set Symbol) [LemSyms]

lemmaSymbols :: Game -> UsedSyms -> (Term, Term, Term, LemSyms, Function, UsedSyms)
lemmaSymbols g (UsedSyms allS lems) =
  let b = uniqueName "b" allS
      s = uniqueName "s" allS
      c = uniqueName "c" allS
      lSyms = LemSyms b s c
   in ( Vars.unintPredTerm (vars g) b
      , Vars.unintPredTerm (vars g) s
      , Vars.unintPredTerm (vars g) c
      , lSyms
      , Vars.unintPred (vars g) s
      , UsedSyms (allS `union` Set.fromList [b, s, c]) (lSyms : lems))

--
-- Step relation [EX ++ CELLS]
-- Other relations [CELLS]
-- 
expandStep :: Game -> Function -> Term -> Term
expandStep g name =
  \case
    Quant q t f -> Quant q t (expandStep g name f)
    Lambda t f -> Lambda t (expandStep g name f)
    Func n args
      | n == name -> Func n ([Var c (sortOf g c) | c <- stateVarL g] ++ args)
      | otherwise -> Func n (expandStep g name <$> args)
    atom -> atom

accReach :: Int -> Ply -> Game -> Loc -> SymSt -> UsedSyms -> (Constraint, Term, UsedSyms, CFG)
accReach depth p g l st uSym =
  let (gl, l') = loopGame g l
      (b, s, c, lSyms, sSym, uSym') = lemmaSymbols g uSym
      st' = set st l' (orf [st `get` l, s])
      cfgInit = CFG.loopCFG (l, l') st lSyms s
      (consR, stAccR, uSym'', cfg) = iterAttr depth p gl st' l' uSym' cfgInit
      -- quantSub f = forallX g (andf [g `inv` l, c, neg (st `get` l)] `impl` f) <- This is not strictly necessary
      quantSub f = Vars.forallX (vars g) $ andf [g `inv` l, c] `impl` f
      cons = expandStep g sSym <$> consR
      stAcc = SymSt.map (expandStep g sSym) stAccR
      cons' =
        [ Vars.forallX (vars g) $ andf [g `inv` l, b] `impl` (st `get` l)
        , quantSub (stAcc `get` l)
        , quantSub (andf cons)
        ]
   in (cons', c, uSym'', cfg)

visitingThreshold :: Int
visitingThreshold = 1

iterAttr ::
     Int -> Ply -> Game -> SymSt -> Loc -> UsedSyms -> CFG -> (Constraint, SymSt, UsedSyms, CFG)
iterAttr depth p g st shadow = attr (OL.fromSet (preds g shadow)) (noVisits g) [] st
  where
    attr ::
         OpenList Loc
      -> VisitCounter
      -> Constraint
      -> SymSt
      -> UsedSyms
      -> CFG
      -> (Constraint, SymSt, UsedSyms, CFG)
    attr ol vc cons st uSym cfg =
      case pop ol of
        Nothing -> (cons, st, uSym, cfg)
        Just (l, ol')
          | visits l vc < visitingThreshold ->
            reC l ol' cons (SymSt.disj st l (cpre p g st l)) uSym (CFG.addUpd st g l cfg)
          | visits l vc == visitingThreshold && depth > 0 ->
            let (consA, fA, uSymA, cfgSub) = accReach (depth - 1) p g l st uSym
                cfg' = CFG.integrate cfgSub cfg
             in reC l ol' (cons ++ consA) (set st l (orf [fA, st `get` l])) uSymA cfg'
          | otherwise -> attr ol' vc cons st uSym cfg
      where
        reC l ol' = attr (preds g l `push` ol') (visit l vc)

accelReach :: Config -> Int -> Ply -> Game -> Loc -> SymSt -> IO (Term, CFG)
accelReach ctx limit p g l st = do
  ctx <- pure $ setName "AccReach" ctx
  lg ctx ["Accelerate in", locName g l, "on", strSt g st]
  let (cons, f, UsedSyms _ syms, cfg) =
        accReach (limit2depth limit) p g l st (UsedSyms (usedSymbols g) [])
  cons <- pure $ cons ++ [Vars.existsX (vars g) (andf [f, neg (st `get` l)])]
  unless (all (null . frees) cons)
    $ error
    $ "assert: constraint with free variables " ++ strL (strS show . frees) cons
  (res, col) <- resolve ctx limit (vars g) cons f syms
  cfg <- pure $ foldl (flip (\(l, li) -> CFG.mapCFG (replaceLemma (vars g) li l))) cfg col
  cfg <- pure $ CFG.setLemmas (stateVarL g) col cfg
  lg ctx ["Acceleration resulted in", smtLib2 res]
  return (res, cfg)

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
    check <- allM (\l -> valid ctx (andf [targ l, ipred] `impl` (attrSt `get` l))) (locations game)
    if check
      then let newAttrSt = SymSt.disjS attrSt $ SymSt.map (\f -> andf [ipred, f]) (cachedSt cache)
            in SymSt.simplify ctx newAttrSt
      else return attrSt
  where
    dependends = filter (`notElem` independendCells cache) (stateVarL game)
    targ l = targetSt cache `get` l
    -- This is only one choice for the independent program variables. However
    -- this seems awfully like we are computing an interpolant. Furthermore,
    -- it might be possible to use some cheaper syntactic stuff (like setting
    -- everything non-independent to "true")
    independLocPred l
      | targ l == false = return true
      | otherwise = simplify ctx $ forAll dependends (targ l `impl` (attrSt `get` l))
    -- 
    independedPred = do
      preds <- mapM independLocPred (Set.toList (locations game))
      simplify ctx (andf preds)
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
          fn <- simplify ctx (orf [cpre p g st l, fo])
          lg ctx ["Compute new", smtLib2 fn]
          let st' = set st l fn
          let vc' = visit l vc
          -- Check if this changed something in this location
          unchanged <- valid ctx (fn `impl` fo)
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
                        (\l -> sat ctx (andf [st'' `get` l, neg (st' `get` l)]))
                        (SymSt.locations st)
                    return (st'', cached)
                  else return (st', [])
              lg ctx ["Cached", strL (locName g) cached]
              -- Compute potential new locations 
              let on' = unions (preds g <$> cached) `push` (preds g l `push` no)
              -- Check if we accelerate
              if accelNow l fo vc' && canAccel g && null cached --DEBUG!
                  -- Acceleration
                then do
                  lg ctx ["Attempt reachability acceleration"]
                  (acc, cfgSub) <- accelReach ctx (visits l vc') p g l st'
                  lg ctx ["Accleration formula", smtLib2 acc]
                  res <- simplify ctx (orf [fn, acc])
                  succ <- not <$> valid ctx (res `impl` fn)
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
        accelNow l fo vc = (g `cyclicIn` l) && (fo /= false) && visits2accel (visits l vc)
        extr cfg
          | generateProgram ctx = pure cfg
          | otherwise = pure CFG.empty
        simpCFG cfg
          | generateProgram ctx = CFG.simplify ctx cfg
          | otherwise = pure cfg

canAccel :: Game -> Bool
canAccel g = any (\v -> isNumber (sortOf g v) && not (boundedVar g v)) (stateVars g)

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
