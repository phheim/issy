module Issy.Products.SymbolicGames
  ( intersection
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Base.Locations as Locs
import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import qualified Issy.Base.Objectives as Obj
import qualified Issy.Logic.FOL as FOL
import Issy.SymbolicArena (Arena)
import qualified Issy.SymbolicArena as SG

intersection :: [(Arena, Objective)] -> (Arena, Objective)
intersection games
  | null games = error "assert: cannot construct empty game intersection"
  | otherwise = foldl1 intersect2 games

intersect2 :: (Arena, Objective) -> (Arena, Objective) -> (Arena, Objective)
intersect2 (a1, o1) (a2, o2) =
  let (arenaI, mp) = intersectArena a1 a2
      prods ls1 ls2 = Set.map mp $ Set.cartesianProduct ls1 ls2
      init = mp (initialLoc o1, initialLoc o2)
      (arenaS, sink) = SG.addSink arenaI
   in case (winningCond o1, winningCond o2) of
        (Safety s1, Safety s2) ->
          (arenaI, Objective {initialLoc = init, winningCond = Safety (prods s1 s2)})
        (_, Safety _) -> intersect2 (a2, o2) (a1, o1)
        (Safety s1, wc2) ->
          let bads = SG.locSet arenaS `Set.difference` prods s1 (SG.locSet a2)
              arenaR = foldl (\a l -> SG.redirectTransTo a l sink) arenaS bads
              wc =
                Obj.mapWC
                  (prods s1)
                  (\rank ->
                     Map.insert sink 0
                       $ Map.mapKeys mp
                       $ Map.fromSet ((rank !) . snd)
                       $ Set.cartesianProduct (SG.locSet a1) (SG.locSet a2))
                  wc2
           in (arenaR, Objective {initialLoc = init, winningCond = wc})
        (_, _) -> error "assert: at least on objective has to be safety"

intersectArena :: Arena -> Arena -> (Arena, (Loc, Loc) -> Loc)
intersectArena a1 a2
  | SG.variables a1 /= SG.variables a2 = error "assert: variables should be the same"
  | otherwise =
    let locProduct = Set.cartesianProduct (SG.locSet a1) (SG.locSet a2)
        (arena0, mp) =
          SG.createLocsFor
            (SG.empty (SG.variables a1))
            (\(l1, l2) -> Locs.name (SG.locations a1) l1 ++ "_" ++ Locs.name (SG.locations a2) l2)
            (\(l1, l2) -> FOL.andf [SG.domain a1 l1, SG.domain a2 l2])
            locProduct
        arena1 =
          foldl
            (\a (l, l') ->
               SG.setTrans
                 a
                 (mp l)
                 (mp l')
                 (FOL.andf [SG.trans a1 (fst l) (fst l'), SG.trans a2 (snd l) (snd l')]))
            arena0
            $ Set.cartesianProduct locProduct locProduct
     in (arena1, mp)
