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
import Issy.Config (Config, nestAcceleration, setName)
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
import qualified Issy.Utils.OpenList as OL (fromSet, pop, push)

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
  let acst = accState ctx limit p g
  (cons, f, cfg, acst) <- accReach acst g l st
  cons <- pure $ cons ++ [Vars.existsX (vars g) (andf [f, neg (st `get` l)])]
  unless (all (null . frees) cons)
    $ error
    $ "assert: constraint with free variables " ++ strL (strS show . frees) cons
  (res, col) <- resolve ctx limit (vars g) cons f (lemmaSyms acst)
  cfg <- pure $ foldl (flip (\(l, li) -> CFG.mapCFG (replaceLemma (vars g) li l))) cfg col
  cfg <- pure $ CFG.setLemmas (Vars.stateVarL (vars g)) col cfg
  lg ctx ["Acceleration resulted in", smtLib2 res]
  return (res, cfg)

-------------------------------------------------------------------------------
-- IterA and accReach
-------------------------------------------------------------------------------
data AccState = AccState
  { player :: Ply
  , limit :: Int
  , depth :: Int
  , config :: Config
  , usedSyms :: Set Symbol
  , lemmaSyms :: [LemSyms]
  , visitCounters :: [VisitCounter]
  }

accState :: Config -> Int -> Ply -> Game -> AccState
accState cfg limit ply arena =
  AccState
    { config = cfg
    , player = ply
    , limit = limit
    , depth = 0
    , usedSyms = usedSymbols arena
    , lemmaSyms = []
    , visitCounters = []
    }

sizeLimit :: AccState -> Maybe Int
sizeLimit = Just . limit2size . limit

unnest :: AccState -> Loc -> AccState
unnest acst = doVisit $ acst {visitCounters = tail (visitCounters acst), depth = depth acst - 1}

nest :: Loc -> AccState -> Bool
nest l acst =
  nestAcceleration (config acst)
    && (depth acst - 1 > limit2depth (limit acst))
    && (visitingThreshold == visits l (head (visitCounters acst)))

visiting :: Loc -> AccState -> Bool
visiting l = (< visitingThreshold) . visits l . head . visitCounters

doVisit :: AccState -> Loc -> AccState
doVisit acst l =
  acst {visitCounters = visit l (head (visitCounters acst)) : tail (visitCounters acst)}

doIterA :: AccState -> Game -> AccState
doIterA acst arena =
  acst {visitCounters = noVisits arena : visitCounters acst, depth = depth acst + 1}

-- TODO: Move to separate module
loopScenario :: Config -> Maybe Int -> Game -> Loc -> SymSt -> IO (Game, Loc, Loc, SymSt, Term)
loopScenario ctx pathBound arena loc target = do
  (loopAr, loc') <- pure $ loopGame arena loc
  let subs = subArena pathBound loopAr (loc, loc')
  (loopAr, oldToNew) <- pure $ inducedSubGame loopAr subs
  loc <- pure $ oldToNew loc
  loc' <- pure $ oldToNew loc'
  let loopTarget = SymSt.symSt (locations loopAr) (const false)
  loopTarget <-
    pure
      $ foldl
          (\st oldloc ->
             if oldToNew oldloc == loc'
               then st
               else set st (oldToNew oldloc) (target `get` oldloc))
          loopTarget
          subs
  indeps <- independentProgVars ctx loopAr
  (loopTarget, fixedInv) <- accTarget ctx (vars loopAr) loc indeps loopTarget
  pure (loopAr, loc, loc', loopTarget, fixedInv)

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

-- TODO: Move to seprate utils module!
distances :: Ord a => Maybe Int -> (a -> Set a) -> a -> Map a Int
distances bound next init = go 0 (Set.singleton init) (Map.singleton init 0)
  where
    go depth last acc
      | null last = acc
      | bound == Just depth = acc
      | otherwise =
        let new = Set.unions (Set.map next last) `Set.difference` Map.keysSet acc
         in go (depth + 1) new $ foldl (\acc l -> Map.insert l (depth + 1) acc) acc new

accReach :: AccState -> Game -> Loc -> SymSt -> IO (Constraint, Term, CFG, AccState)
accReach acst g loc st = do
  let targetInv = g `inv` loc
  -- Compute loop scenario
  (gl, loc, loc', st, fixedInv) <- loopScenario (config acst) (sizeLimit acst) g loc st
  -- Compute new lemma symbols
  (base, step, conc, lsym, stepSym, acst) <- pure $ lemmaSymbols (vars g) acst
  -- Initialize loop-program
  cfg <- pure $ CFG.loopCFG (loc, loc') st lsym step
  -- Finialize loop game target with step relation and compute loop attractor
  let st' = set st loc' $ orf [st `get` loc, step]
  (cons, stAcc, cfg, acst) <- iterA acst gl st' loc' cfg
  -- Derive constraints
  let quantSub f = Vars.forallX (vars g) $ andf [targetInv, conc] `impl` f
  cons <- pure $ map (expandStep (vars g) stepSym) cons
  stAcc <- pure $ SymSt.map (expandStep (vars g) stepSym) stAcc
  cons <-
    pure
      [ Vars.forallX (vars g) $ andf [targetInv, base] `impl` (st `get` loc)
      , quantSub (stAcc `get` loc)
      , quantSub (andf cons)
      ]
  pure (cons, andf [conc, fixedInv], cfg, acst)

accReachS :: AccState -> Game -> Loc -> SymSt -> IO (Term -> (Constraint, Term, CFG))
accReachS acst g loc st = do
  let targetInv = g `inv` loc
  (gl, loc, loc', st, fixedInv) <- loopScenario (config acst) (sizeLimit acst) g loc st
  let (base, step, conc, lsym) = error "TODO IMPLEMENT: Probably without lsym!!!"
  pure $ \invar ->
    let st' = set st loc' $ orf [st `get` loc, FOL.andf [step, Vars.primeT (vars gl) invar]]
        (stAcc, cfg) = iterAS acst gl st' loc' $ CFG.loopCFG (loc, loc') st lsym step
        cons =
          [ Vars.forallX (vars g) $ andf [targetInv, base, invar] `impl` (st `get` loc)
          , Vars.forallX (vars g) $ andf [targetInv, conc, invar] `impl` (stAcc `get` loc)
          ]
     in (cons, andf [conc, fixedInv, invar], cfg)

iterAS :: AccState -> Game -> SymSt -> Loc -> CFG -> (SymSt, CFG)
iterAS acst g attr shadow = go (doIterA acst g) (OL.fromSet (preds g shadow)) attr
  where
    go acst open attr cfgl =
      case OL.pop open of
        Nothing -> (attr, cfgl)
        Just (l, open)
          | visiting l acst ->
            go
              (doVisit acst l)
              (preds g l `OL.push` open)
              (SymSt.disj attr l $ cpre (player acst) g attr l)
              (CFG.addUpd attr g l cfgl)
          | otherwise -> go acst open attr cfgl

iterA :: AccState -> Game -> SymSt -> Loc -> CFG -> IO (Constraint, SymSt, CFG, AccState)
iterA acst g attr shadow = go (doIterA acst g) (OL.fromSet (preds g shadow)) [] attr
  where
    go acst open cons attr cfgl =
      case OL.pop open of
        Nothing -> pure (cons, attr, cfgl, acst)
        Just (l, open)
          -- Normal IterA update
          | visiting l acst -> do
            open <- pure $ preds g l `OL.push` open
            cfgl <- pure $ CFG.addUpd attr g l cfgl
            attr <- pure $ SymSt.disj attr l $ cpre (player acst) g attr l
            go (doVisit acst l) open cons attr cfgl
          -- Nested IterA update
          | nest l acst -> do
            (consA, fA, cfgSub, acst) <- accReach acst g l attr
            open <- pure $ preds g l `OL.push` open
            cons <- pure $ cons ++ consA
            attr <- pure $ set attr l $ orf [fA, attr `get` l]
            cfgl <- pure $ CFG.integrate cfgSub cfgl
            go (unnest acst l) open cons attr cfgl
          -- Do nothing
          | otherwise -> go acst open cons attr cfgl

-------------------------------------------------------------------------------
-- Symbol Management
-------------------------------------------------------------------------------
lemmaSymbols :: Variables -> AccState -> (Term, Term, Term, LemSyms, Function, AccState)
lemmaSymbols vars acst =
  let base = uniqueName "b" $ usedSyms acst
      step = uniqueName "s" $ usedSyms acst
      conc = uniqueName "c" $ usedSyms acst
      lsym = LemSyms base step conc
   in ( Vars.unintPredTerm vars base
      , Vars.unintPredTerm vars step
      , Vars.unintPredTerm vars conc
      , lsym
      , Vars.unintPred vars step
      , acst
          { usedSyms = usedSyms acst `Set.union` Set.fromList [base, step, conc]
          , lemmaSyms = lsym : lemmaSyms acst
          })

--
-- Step relation [EX ++ CELLS]
-- Other relations [CELLS]
-- 
expandStep :: Variables -> Function -> Term -> Term
expandStep vars func = go
  where
    go =
      \case
        Quant q s t -> Quant q s $ go t
        Lambda s t -> Lambda s $ go t
        Func f args
          | f == func -> Func f $ [Var v (Vars.sortOf vars v) | v <- Vars.stateVarL vars] ++ args
          | otherwise -> Func f $ map go args
        atom -> atom
-------------------------------------------------------------------------------
{-
estimateTarget :: Config -> Term -> IO Term
estimateTarget = error "TODO IMPLEMENT"

generateTerms :: Config -> Variables -> Term -> [Term]
generateTerms = error "TODO IMPLEMENT"

boundIn :: Config -> Term -> Term -> IO Bool
boundIn = error "TODO IMPLEMENT"

type Box = [(Term, Just Integer, Just Integer)]

mkBox :: Config -> Term -> [Term] -> IO Box
mkBox = error "TODO IMPLEMENT"

mkManhatten :: Config -> Term -> Box -> IO Term
mkManhatten = error "TODO IMPLEMENT"

lemmaGuess :: Config -> Term -> IO (Term, Term, Term)
lemmaGuess = error "TODO IMPLEMENT"

-}
