{-# LANGUAGE LambdaCase #-}

module Issy.Solver.Acceleration
  ( accelReach
  ) where

import Control.Monad (unless)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, setName)
import Issy.Logic.FOL
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import Issy.Solver.Heuristics
import Issy.Solver.LemmaFinding (Constraint, LemSyms(..), replaceLemma, resolve)
import Issy.Utils.Extra (allM)
import Issy.Utils.Logging
import Issy.Utils.OpenList (OpenList, pop, push)
import qualified Issy.Utils.OpenList as OL (fromSet)

-------------------------------------------------------------------------------
-- Global Acceleration
-------------------------------------------------------------------------------
-- TODO: Replace limit by more abstract limiting state, that is tracking over time!
accelReach :: Config -> Int -> Ply -> Game -> Loc -> SymSt -> IO (Term, CFG)
accelReach ctx limit p g l st = do
  -- TODO: Add eglibility check!!
  ctx <- pure $ setName "AccReach" ctx
  lg ctx ["Accelerate in", locName g l, "on", strSt g st]
  lg ctx ["Depth bound", show (limit2depth limit)]
  lg ctx ["Size bound", show (limit2size limit)]
  (cons, f, UsedSyms _ syms, cfg) <-
    accReach ctx limit (limit2depth limit) p g l st (UsedSyms (usedSymbols g) [])
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
-- IterA and accReach
-------------------------------------------------------------------------------
accReach ::
     Config
  -> Int
  -> Int
  -> Ply
  -> Game
  -> Loc
  -> SymSt
  -> UsedSyms
  -> IO (Constraint, Term, UsedSyms, CFG)
accReach ctx limit depth p g loc st uSym = do
  let targetInv = g `inv` loc
  -- Compute new lemma symbols
  (b, s, c, lSyms, stepSymb, uSym) <- pure $ lemmaSymbols g uSym
  -- Compute loop game
  (gl, loc') <- pure $ loopGame g loc
  let subLocs = subArena (Just (limit2size limit)) gl (loc, loc')
  (gl, oldToNew) <- pure $ inducedSubGame gl subLocs
  loc <- pure $ oldToNew loc
  loc' <- pure $ oldToNew loc'
  lg ctx ["Loop game", show gl]
  -- Copy target for loop game
  let oldSt = st
  st <- pure $ SymSt.symSt (locations gl) (const false)
  st <-
    pure
      $ foldl
          (\st oldloc ->
             if oldToNew oldloc == loc'
               then st
               else set st (oldToNew oldloc) (oldSt `get` oldloc))
          st
          subLocs
  -- Initialize loop-program
  cfg <- pure $ CFG.loopCFG (loc, loc') st lSyms s
  -- Build accleration restircted target and fixed invariant
  indeps <- independentProgVars ctx gl
  lg ctx ["Full state", SymSt.toString (locName gl) st]
  (st, fixedInv) <- accTarget ctx (vars gl) loc indeps st
  lg ctx ["Reduced state", SymSt.toString (locName gl) st]
  lg ctx ["Fixed invariant", smtLib2 fixedInv]
  -- Finialize loop game target with step relation and compute loop attractor
  let st' = set st loc' $ orf [st `get` loc, s]
  (cons, stAcc, uSym, cfg) <- iterA ctx limit depth p gl st' loc' uSym cfg
  -- Derive constraints
  let quantSub f = Vars.forallX (vars g) $ andf [targetInv, c] `impl` f
  cons <- pure $ map (expandStep g stepSymb) cons
  stAcc <- pure $ SymSt.map (expandStep g stepSymb) stAcc
  cons <-
    pure
      [ Vars.forallX (vars g) $ andf [targetInv, b] `impl` (st `get` loc)
      , quantSub (stAcc `get` loc)
      , quantSub (andf cons)
      ]
  pure (cons, andf [c, fixedInv], uSym, cfg)

-- TODO: adapat SMT simplify to be able to catch uninterpreted functions or something like that !!!
accTarget :: Config -> Variables -> Loc -> Set Symbol -> SymSt -> IO (SymSt, Term)
accTarget ctx vars loc indeps st = do
  let deps = Vars.stateVars vars `Set.difference` indeps
  fixedInv <- SMT.simplify ctx $ FOL.exists (Set.toList deps) $ get st loc
  let st' = SymSt.map (\phi -> FOL.forAll (Set.toList indeps) (fixedInv `impl` phi)) st
  st' <- SymSt.simplify ctx st'
  check <-
    allM (\l -> SMT.implies ctx (andf [st' `get` l, fixedInv]) (st `get` l)) (SymSt.locations st)
  if check
    then pure (st', fixedInv)
    else pure (st, FOL.true)

-- TODO: this should be part of the heursitics!
visitingThreshold :: Int
visitingThreshold = 1

-- The choosen sub-arena should contain the sucessors of 
-- the accelerated location and all locations that are 
-- on a (simple) path of lenght smaller equal the bound 
-- form loc to loc'
subArena :: Maybe Int -> Game -> (Loc, Loc) -> Set Loc
subArena bound loopArena (loc, loc') =
  let forwDist = distances bound (succs loopArena) loc
      backDist = distances bound (preds loopArena) loc'
      minPath = Map.intersectionWith (+) forwDist backDist
      pathInc =
        case bound of
          Nothing -> Map.keysSet minPath
          Just bound -> Map.keysSet $ Map.filter (<= bound) minPath
   in pathInc `Set.union` succs loopArena loc `Set.union` Set.fromList [loc, loc']

distances :: Ord a => Maybe Int -> (a -> Set a) -> a -> Map a Int
distances bound next init = go 0 (Set.singleton init) (Map.singleton init 0)
  where
    go depth last acc
      | null last = acc
      | bound == Just depth = acc
      | otherwise =
        let new = Set.unions (Set.map next last) `Set.difference` Map.keysSet acc
         in go (depth + 1) new $ foldl (\acc l -> Map.insert l (depth + 1) acc) acc new

-- TODO add propagation bound restriction!
iterA ::
     Config
  -> Int
  -> Int
  -> Ply
  -> Game
  -> SymSt
  -> Loc
  -> UsedSyms
  -> CFG
  -> IO (Constraint, SymSt, UsedSyms, CFG)
iterA ctx limit depth p g st shadow = attr (OL.fromSet (preds g shadow)) (noVisits g) [] st
  where
    attr ::
         OpenList Loc
      -> VisitCounter
      -> Constraint
      -> SymSt
      -> UsedSyms
      -> CFG
      -> IO (Constraint, SymSt, UsedSyms, CFG)
    attr ol vc cons st uSym cfg =
      case pop ol of
        Nothing -> pure (cons, st, uSym, cfg)
        Just (l, ol')
          | visits l vc < visitingThreshold -> do
            lg ctx ["Update", locName g l, "with", smtLib2 (cpre p g st l)]
            reC l ol' cons (SymSt.disj st l (cpre p g st l)) uSym (CFG.addUpd st g l cfg)
          | visits l vc == visitingThreshold && depth > 0 -> do
            (consA, fA, uSymA, cfgSub) <- accReach ctx limit (depth - 1) p g l st uSym
            cfg <- pure $ CFG.integrate cfgSub cfg
            reC l ol' (cons ++ consA) (set st l (orf [fA, st `get` l])) uSymA cfg
          | otherwise -> attr ol' vc cons st uSym cfg
      where
        reC l ol' = attr (preds g l `push` ol') (visit l vc)

-------------------------------------------------------------------------------
-- Symbol Management
-------------------------------------------------------------------------------
--TODO: add more "global acceleration state"
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
      , UsedSyms (allS `Set.union` Set.fromList [b, s, c]) (lSyms : lems))

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
-------------------------------------------------------------------------------
