-------------------------------------------------------------------------------
module Issy.Solver.Acceleration.LoopScenario
  ( loopScenario
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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
import Issy.Utils.Extra (allM)

-------------------------------------------------------------------------------
loopScenario :: Config -> Maybe Int -> Game -> Loc -> SymSt -> IO (Game, Loc, Loc, SymSt, Term)
loopScenario ctx pathBound arena loc target = do
  (loopAr, loc') <- pure $ loopGame arena loc
  let subs = subArena pathBound loopAr (loc, loc')
  (loopAr, oldToNew) <- pure $ inducedSubGame loopAr subs
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
  indeps <- independentProgVars ctx loopAr
  (loopTarget, fixedInv) <- accTarget ctx (vars loopAr) loc indeps loopTarget
  pure (loopAr, loc, loc', loopTarget, fixedInv)

accTarget :: Config -> Variables -> Loc -> Set Symbol -> SymSt -> IO (SymSt, Term)
accTarget ctx vars loc indeps st = do
  let deps = Vars.stateVars vars `Set.difference` indeps
  fixedInv <- SMT.simplify ctx $ FOL.exists (Set.toList deps) $ get st loc
  let st' = SymSt.map (\phi -> FOL.forAll (Set.toList indeps) (fixedInv `FOL.impl` phi)) st
  st' <- SymSt.simplify ctx st'
  check <-
    allM
      (\l -> SMT.valid ctx (FOL.andf [st' `get` l, fixedInv] `FOL.impl` get st l))
      (SymSt.locations st)
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
