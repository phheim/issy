{-# LANGUAGE Safe #-}

module Issy.Encoders.ToFormula
  ( toFormula
  , shiftInTime
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Games.Objectives as Obj
import qualified Issy.Games.SymbolicArena as SG
import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.Temporal as TL
import qualified Issy.Specification as Spec
import Issy.Specification (Specification)

-- | 'shiftInTime' adapts the formula such that unpriming it matches the different 
-- semantic in shifting in time.
shiftInTime :: (Variables, TL.Formula Term) -> (Variables, TL.Formula Term)
shiftInTime (vars, formula) =
  let inputPref = FOL.uniquePrefix "intial_value_" $ Vars.allSymbols vars
      mapping = map (\v -> (Vars.prime v, inputPref ++ v, Vars.sortOf vars v)) $ Vars.stateVarL vars
      inputEnc = map (\(var, init, sort) -> FOL.var var sort `FOL.equal` FOL.var init sort) mapping
      newVars = foldl (\vars (_, init, sort) -> Vars.addInput vars init sort) vars mapping
   in (newVars, TL.And (map TL.Atom inputEnc ++ [TL.next formula]))

toFormula :: Specification -> (Variables, TL.Formula Term)
toFormula spec =
  let prefix = FOL.uniquePrefix "loc_var_" $ Vars.allSymbols $ Spec.variables spec
      gamesAndLocVar =
        zipWith (curry (first ((prefix ++) . show))) [(1 :: Int) ..] $ Spec.games spec
      locVars = map fst gamesAndLocVar
      formula =
        TL.And $ map (uncurry gameToFormula) gamesAndLocVar ++ map TL.toFormula (Spec.formulas spec)
      newVars =
        foldl (\vars loc -> Vars.addStateVar vars loc FOL.SInt) (Spec.variables spec) locVars
   in (newVars, formula)

gameToFormula :: Symbol -> (SG.Arena, Objective) -> TL.Formula Term
gameToFormula locVar (arena, obj) =
  let holdLoc =
        TL.globally
          $ TL.Or
          $ map (\l -> TL.And [TL.Atom (encLoc l), TL.Atom (SG.domain arena l)])
          $ Set.toList
          $ SG.locSet arena
      transEff =
        TL.globally
          $ TL.Or
          $ map (\(l, l', p) -> TL.And [TL.Atom (encLoc l), TL.Atom (encLoc' l'), TL.Atom p])
          $ SG.transList arena
   in TL.And [Obj.toTemporalLogic encLoc obj, holdLoc, transEff]
  where
    locNums = Map.fromList $ zip (Set.toList $ SG.locSet arena) [1 ..]
    encLoc loc = FOL.ivarT locVar `FOL.equal` FOL.intConst (locNums ! loc)
    encLoc' = Vars.primeT (SG.variables arena) . encLoc
