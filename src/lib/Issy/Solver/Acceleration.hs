{-# LANGUAGE LambdaCase #-}

module Issy.Solver.Acceleration
  ( accelReach
  ) where

import Control.Monad (unless)
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
  let (cons, f, UsedSyms _ syms, cfg) =
        accReach limit (limit2depth limit) p g l st (UsedSyms (usedSymbols g) [])
  cons <- pure $ cons ++ [Vars.existsX (vars g) (andf [f, neg (st `get` l)])]
  unless (all (null . frees) cons)
    $ error
    $ "assert: constraint with free variables " ++ strL (strS show . frees) cons
  (res, col) <- resolve ctx limit (vars g) cons f syms
  cfg <- pure $ foldl (flip (\(l, li) -> CFG.mapCFG (replaceLemma (vars g) li l))) cfg col
  cfg <- pure $ CFG.setLemmas (stateVarL g) col cfg
  lg ctx ["Acceleration resulted in", smtLib2 res]
  return (res, cfg)

accReach ::
     Int -> Int -> Ply -> Game -> Loc -> SymSt -> UsedSyms -> (Constraint, Term, UsedSyms, CFG)
accReach limit depth p g l st uSym =
  let (gl, l') = loopGame (Just (limit2size limit)) g l
      (b, s, c, lSyms, sSym, uSym') = lemmaSymbols g uSym
      st' =
        SymSt.symSt (locations gl) $ \loc ->
          if loc `elem` SymSt.locations st
            then get st loc
            else if loc == l'
                   then orf [st `get` l, s]
                   else false
      cfgInit = CFG.loopCFG (l, l') st lSyms s
      (consR, stAccR, uSym'', cfg) = iterA limit depth p gl st' l' uSym' cfgInit
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

-------------------------------------------------------------------------------
-- IterA and accReach
-------------------------------------------------------------------------------
-- TODO add propagation bound restriction!
iterA ::
     Int
  -> Int
  -> Ply
  -> Game
  -> SymSt
  -> Loc
  -> UsedSyms
  -> CFG
  -> (Constraint, SymSt, UsedSyms, CFG)
iterA limit depth p g st shadow = attr (OL.fromSet (preds g shadow)) (noVisits g) [] st
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
            let (consA, fA, uSymA, cfgSub) = accReach limit (depth - 1) p g l st uSym
                cfg' = CFG.integrate cfgSub cfg
             in reC l ol' (cons ++ consA) (set st l (orf [fA, st `get` l])) uSymA cfg'
          | otherwise -> attr ol' vc cons st uSym cfg
      where
        reC l ol' = attr (preds g l `push` ol') (visit l vc)

-------------------------------------------------------------------------------
-- Symbol Management
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
