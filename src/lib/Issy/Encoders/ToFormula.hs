{-# LANGUAGE Safe #-}

module Issy.Encoders.ToFormula
  ( toFormula
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

toFormula :: Specification -> (Variables, TL.Formula Term)
toFormula spec =
  let vars = Spec.variables spec
      inputPref = FOL.uniquePrefix "intial_value_" $ Vars.allSymbols vars
      inputEnc = map (\(var, init, sort) -> FOL.var var sort `FOL.equal` FOL.var init sort) mapping
      locPrefix = FOL.uniquePrefix "loc_var_" $ Vars.allSymbols vars
      gamesAndLocVar =
        zipWith (curry (first ((locPrefix ++) . show))) [(1 :: Int) ..] $ Spec.games spec
      mapping = map (\v -> (Vars.prime v, inputPref ++ v, Vars.sortOf vars v)) $ Vars.stateVarL vars
      formula =
        TL.And $ map (uncurry gameToFormula) gamesAndLocVar ++ map TL.toFormula (Spec.formulas spec)
      newVarsI = foldl (\vars (_, init, sort) -> Vars.addInput vars init sort) vars mapping
      newVarsL =
        foldl (\vars (loc, _) -> Vars.addStateVar vars loc FOL.SInt) newVarsI gamesAndLocVar
   in (newVarsL, TL.And (map TL.Atom inputEnc ++ [TL.next formula]))

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
