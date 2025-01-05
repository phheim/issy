{-# LANGUAGE LambdaCase #-}

module Issy.Solver.Acceleration
  ( accelReach
  ) where

import Control.Monad (unless)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config, setName)
import Issy.Logic.FOL
import Issy.Printers.SMTLib (smtLib2)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import Issy.Solver.Heuristics
import Issy.Solver.LemmaFinding (Constraint, LemSyms(..), replaceLemma, resolve)
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
  let target = st `get` loc
  let targetInv = g `inv` loc
  -- Compute new lemma symbols
  (b, s, c, lSyms, sSym, uSym) <- pure $ lemmaSymbols g uSym
  -- Compute loop game
  (gl, loc') <- pure $ loopGame g loc
  let subLocs = subArena (Just (limit2size limit)) gl (loc, loc')
  (gl, oldToNew) <- pure $ inducedSubGame gl subLocs
  loc <- pure $ oldToNew loc
  loc' <- pure $ oldToNew loc'
  -- Compute loop target and fixed invariant
  let oldSt = st
  st <- pure $ SymSt.symSt (locations gl) (const false)
  -- TODO: FIXME this access the old loc' from oldSt which does not exists
  st <- pure $ foldl (\st oldloc -> set st (oldToNew oldloc) (oldSt `get` oldloc)) st subLocs
  -- indeps <- independentProgVars ctx gl 
  let st' = set st loc' $ orf [target, s]
  -- Initialize loop-program
  cfg <- pure $ CFG.loopCFG (loc, loc') st lSyms s
  -- Compute sub-attractor for loop game
  (cons, stAcc, uSym, cfg) <- iterA ctx limit depth p gl st' loc' uSym cfg
  -- Derive constraints
  let quantSub f = Vars.forallX (vars g) $ andf [targetInv, c] `impl` f
  cons <- pure $ map (expandStep g sSym) cons
  stAcc <- pure $ SymSt.map (expandStep g sSym) stAcc
  cons <-
    pure
      [ Vars.forallX (vars g) $ andf [targetInv, b] `impl` target
      , quantSub (stAcc `get` loc)
      , quantSub (andf cons)
      ]
  pure (cons, c, uSym, cfg)

accTarget :: Config -> Set Symbol -> Loc -> SymSt -> IO (SymSt, Term)
accTarget ctx loopGame targ =
  error
    "TODO: implement: forall ind. (exists depend targ) -> targ; qelim if possible!; check if new + invariant implies old, otherwise return nothing"

-- TODO: this should be part of the heursitics!
visitingThreshold :: Int
visitingThreshold = 1

-- The choosen sub-arena should contain the sucessors of 
-- the accelerated locations and all locations that are 
-- on a (simple) path of lenght smaller equal the bound 
-- form loc to loc'
subArena :: Maybe Int -> Game -> (Loc, Loc) -> Set Loc
subArena bound loopArena (loc, loc') = error "TODO IMPLEMENT"

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
