module Issy.Solver.Acceleration.LoopScenario
  ( loopScenario
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import Issy.Solver.GameInterface
import Issy.Solver.Synthesis (SyBo)
import qualified Issy.Solver.Synthesis as Synt
import Issy.Utils.Extra (allM)

-------------------------------------------------------------------------------
loopScenario ::
     Config
  -> Maybe Int
  -> Arena
  -> Loc
  -> SymSt
  -> Symbol
  -> IO (Arena, Loc, Loc, SymSt, Term, SyBo)
loopScenario conf pathBound arena loc target prime = do
  (loopAr, loc') <- pure $ loopArena arena loc
  let subs = subArena pathBound loopAr (loc, loc')
  (loopAr, oldToNew) <- pure $ inducedSubArena loopAr subs
  loc <- pure $ oldToNew loc
  loc' <- pure $ oldToNew loc'
  let loopTarget = SymSt.symSt (locations loopAr) (const FOL.false)
  loopTarget <-
    pure
      $ foldl
          (\st oldloc ->
             if oldToNew oldloc == loc'
               then st
               else set st (oldToNew oldloc) (target `get` oldloc))
          loopTarget
          subs
  indeps <- independentProgVars conf loopAr
  (loopTarget, fixedInv) <- accTarget conf (vars loopAr) loc indeps loopTarget
  let newToOld =
        Map.fromList
          $ mapMaybe
              (\old ->
                 if old `elem` subs
                   then Just (oldToNew old, old)
                   else Nothing)
          $ Set.toList
          $ locations arena
  let prog = Synt.returnOn loopTarget $ Synt.loopSyBo conf loopAr loc loc' prime newToOld
  pure (loopAr, loc, loc', loopTarget, fixedInv, prog)

accTarget :: Config -> Variables -> Loc -> Set Symbol -> SymSt -> IO (SymSt, Term)
accTarget conf vars loc indeps st = do
  let deps = Vars.stateVars vars `Set.difference` indeps
  fixedInv <- SMT.simplify conf $ FOL.exists (Set.toList deps) $ get st loc
  let st' = SymSt.map (\phi -> FOL.forAll (Set.toList indeps) (fixedInv `FOL.impl` phi)) st
  st' <- SymSt.simplify conf st'
  checkImpl <-
    allM
      (\l -> SMT.valid conf (FOL.andf [st' `get` l, fixedInv] `FOL.impl` get st l))
      (SymSt.locations st)
  checkSat <- SMT.sat conf $ st' `get` loc
  if checkImpl && checkSat
    then pure (st', fixedInv)
    else pure (st, FOL.true)

-- The choosen sub-arena should contain the sucessors of 
-- the accelerated location and all locations that are 
-- on a (simple) path of lenght smaller equal the bound 
-- form loc to loc'
subArena :: Maybe Int -> Arena -> (Loc, Loc) -> Set Loc
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
-------------------------------------------------------------------------------
