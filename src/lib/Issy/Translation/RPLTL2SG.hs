---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Translation.RPLTL2SG
-- Description : Translation of RPLTL to symbolic games
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements the translation from RPLTL to symbolic games.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Translation.RPLTL2SG
  ( translate
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import Issy.Games.Objectives (Objective(..))
import qualified Issy.Games.Objectives as Obj
import Issy.Games.SymbolicArena (Arena)
import qualified Issy.Games.SymbolicArena as SG
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.RPLTL as RPLTL
import qualified Issy.Logic.Temporal as TL
import qualified Issy.Translation.DOA as DOA
import qualified Issy.Translation.LTL2DOA as LTL2DOA
import Issy.Utils.Extra (intmapSet)

---------------------------------------------------------------------------------------------------
-- | Translates a RPLTL specification into an symbolic game (i.e. a symbolic arena and a
-- respective objective). During this process the external tool ltl2tgba is called.
translate :: Config -> TL.Spec Term -> IO (Arena, Objective)
translate cfg spec = do
  let formula = RPLTL.pullBoolF $ TL.toFormula spec
  let (atoms2ap, ap2atoms) = rpltlToltlMap formula
  doa <- LTL2DOA.translate cfg atoms2ap formula
  lg cfg ["DOA:", show doa]
  SG.simplifySG cfg $ doa2game (TL.variables spec) ap2atoms doa

-- | extract the atoms out for the formula
rpltlToltlMap :: TL.Formula Term -> (Term -> String, String -> Term)
rpltlToltlMap formula =
  let atomsAP = intmapSet (\n atom -> (atom, 'a' : show n)) $ TL.atoms formula
      atoms2ap = Map.fromList atomsAP
      ap2atoms = Map.fromList (map swap atomsAP)
   in ((atoms2ap !), (ap2atoms !))

-- | translates the 'DOA' into the game
doa2game :: Variables -> (String -> Term) -> DOA.DOA String -> (Arena, Objective)
doa2game vars atomOf doa =
  let arena0 = SG.empty vars
      (arena1, mapState) =
        SG.createLocsFor arena0 DOA.stateName (const FOL.true) (DOA.stateList doa)
      arena2 = foldl (addTrans mapState) arena1 (DOA.states doa)
      init = mapState (DOA.initial doa)
      wc =
        case DOA.acceptance doa of
          DOA.Safety safe -> Obj.Safety $ Set.map mapState safe
          DOA.Buechi rep -> Obj.Buechi $ Set.map mapState rep
          DOA.ParityMaxOdd color -> Obj.Parity $ Map.mapKeys mapState color
   in (arena2, Objective {initialLoc = init, winningCond = wc})
  where
    addTrans mapState arena s =
      let locPerState =
            map (bimap mapState dnfToTerm)
              $ Map.toList
              $ Map.fromListWith (++)
              $ map (\(cl, st) -> (st, [Set.toList cl]))
              $ Set.toList
              $ DOA.trans doa s
       in foldl (\ar (l', f) -> SG.setTrans ar (mapState s) l' f) arena locPerState
    dnfToTerm dnf =
      FOL.orf
        $ map
            (FOL.andf
               . map
                   (\(ap, pol) ->
                      if pol
                        then atomOf ap
                        else FOL.neg (atomOf ap)))
            dnf
---------------------------------------------------------------------------------------------------
