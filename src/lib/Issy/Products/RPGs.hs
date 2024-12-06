{-# LANGUAGE LambdaCase #-}

module Issy.Products.RPGs
  ( rpgProduct
  ) where

import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import Issy.Base.Objectives (Objective(..), WinningCondition(Safety))
import Issy.Logic.FOL
import Issy.RPG

gameProduct2 :: (Game, Objective) -> (Game, Objective) -> (Game, Objective)
gameProduct2 (g1, obj1) (g2, obj2) =
  let gA = foldl (\g v -> fromMaybe g $ addInput g v (sortOf g2 v)) emptyGame (inputs g2)
      gB = foldl (\g v -> fromMaybe g $ addInput g v (sortOf g1 v)) gA (inputs g1)
      gC =
        foldl
          (\g v -> fromMaybe g $ addOutput g v (sortOf g2 v) (v `elem` boundedCells g2))
          gB
          (outputs g2)
      gD =
        foldl
          (\g v -> fromMaybe g $ addOutput g v (sortOf g1 v) (v `elem` boundedCells g1))
          gC
          (outputs g1)
        -- add locations
      locProd = Set.cartesianProduct (locations g1) (locations g2)
      (gE, mp) = foldl multLocs (gD, Map.empty) locProd
        -- add invariants
      gF =
        foldl (\g (l1, l2) -> setInv g (mp ! (l1, l2)) (andf [g1 `inv` l1, g2 `inv` l2])) gE locProd
        -- add transitions 
      gG =
        foldl
          (\g (l1, l2) ->
             fromMaybe g $ addTransition g (mp ! (l1, l2)) (mergeTrans mp (tran g1 l1) (tran g2 l2)))
          gF
          locProd
        -- compute new objective
      init = mp ! (initialLoc obj1, initialLoc obj2)
      wc =
        case (winningCond obj1, winningCond obj2) of
          (Safety s1, Safety s2) -> Safety $ Set.map (mp !) (Set.cartesianProduct s1 s2)
          _ -> error "Only safety is allowed for now"
   in (gG, Objective {initialLoc = init, winningCond = wc})
  where
    multLocs (g, mp) (l1, l2) =
      let (g', l) = addLocation g $ locName g1 l1 ++ "__" ++ locName g2 l2
       in (g', Map.insert (l1, l2) l mp)
    --
    mergeTrans mp t1 =
      \case
        TIf p tt tf -> TIf p (mergeTrans mp t1 tt) (mergeTrans mp t1 tf)
        TSys upds -> mergeTransH mp upds t1
    mergeTransH mp upd2 =
      \case
        TIf p tt tf -> TIf p (mergeTransH mp upd2 tt) (mergeTransH mp upd2 tf)
        TSys upd1 -> TSys [(mergeUpds u1 u2, mp ! (l1, l2)) | (u1, l1) <- upd1, (u2, l2) <- upd2]
    mergeUpds u1 u2 =
      Map.fromListWithKey
        (\var old new ->
           case old of
             Var var' _ ->
               if var == var'
                 then new
                 else old
             _ -> old)
        (Map.toList u1 ++ Map.toList u2)

rpgProduct :: [(Game, Objective)] -> (Game, Objective)
rpgProduct =
  \case
    [] -> error "Cannot construct empty product"
    [gwc] -> gwc
    gwc:lr -> gameProduct2 gwc (rpgProduct lr)
