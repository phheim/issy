{-# LANGUAGE Safe, LambdaCase #-}

module Issy.Translation.RPG2SG
  ( rpgToSG
  ) where

import qualified Data.Map.Strict as Map
import Issy.Prelude

import qualified Issy.Games.Objectives as Obj
import qualified Issy.Games.ReactiveProgramArena as RPG
import qualified Issy.Games.SymbolicArena as SG
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL

rpgToSG :: (RPG.Game, Objective) -> (SG.Arena, Objective)
rpgToSG (rpg, objRPG) =
  let arena0 = SG.empty $ RPG.variables rpg
      (arena1, oldToNew) =
        SG.createLocsFor arena0 (RPG.locName rpg) (const FOL.true) (RPG.locations rpg)
      arena2 =
        foldr
          (\oldSrcLoc ->
             flip
               (foldr
                  (\(oldTrgLoc, cond) arena ->
                     SG.setTrans arena (oldToNew oldSrcLoc) (oldToNew oldTrgLoc) cond))
               (transToCond (RPG.variables rpg) (RPG.trans rpg oldSrcLoc)))
          arena1
          (RPG.locations rpg)
      objSG =
        Obj.Objective
          { Obj.initialLoc = oldToNew (Obj.initialLoc objRPG)
          , Obj.winningCond = Obj.mapLoc oldToNew (Obj.winningCond objRPG)
          }
   in (arena2, objSG)

transToCond :: Variables -> RPG.Transition -> [(Loc, Term)]
transToCond vars = Map.toList . fmap (FOL.orf . map FOL.andf) . go
  where
    go =
      \case
        RPG.TIf cond tt tf ->
          let recTT = map (cond :) <$> go tt
              recTF = map (FOL.neg cond :) <$> go tf
           in Map.unionWith (++) recTT recTF
        RPG.TSys upds -> Map.fromListWith (++) $ map (\(upd, l) -> (l, [[updToCond vars upd]])) upds

updToCond :: Variables -> Map Symbol Term -> Term
updToCond vars upd =
  FOL.andfL (Map.toList upd) $ \(v, u) -> FOL.equal (Vars.primeT vars (Vars.mk vars v)) u
