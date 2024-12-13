module Issy.Translation.RPLTL2SG
  ( translate
  ) where

import Data.Bifunctor (bimap)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Tuple (swap)

import Issy.Base.Objectives (Objective(..))
import qualified Issy.Base.Objectives as Obj
import Issy.Base.Variables (Variables)
import Issy.Config (Config)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.RPLTL as RPLTL
import qualified Issy.Logic.Temporal as TL
import qualified Issy.Translation.DOA as DOA
import qualified Issy.Translation.LTL2DOA as LTL2DOA
import Issy.SymbolicArena (Arena)
import qualified Issy.SymbolicArena as SG
import Issy.Utils.Extra
import Issy.Utils.Logging

translate :: Config -> RPLTL.Spec -> IO (Arena, Objective)
translate cfg spec = do
  let formula = RPLTL.toFormula spec
  let (atoms2ap, ap2atoms) = rpltlToltlMap formula
  doa <- LTL2DOA.translate cfg atoms2ap formula
  lg cfg ["DOA:", show doa]
  SG.simplifySG cfg $ doa2game (RPLTL.variables spec) ap2atoms doa

rpltlToltlMap :: RPLTL.Formula -> (Term -> String, String -> Term)
rpltlToltlMap formula =
  let atomsAP = intmapSet (\n atom -> (atom, 'a' : show n)) $ TL.atoms formula
      atoms2ap = Map.fromList atomsAP
      ap2atoms = Map.fromList (map swap atomsAP)
   in ((atoms2ap !), (ap2atoms !))

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
          DOA.Parity color -> Obj.Parity $ Map.mapKeys mapState color
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
