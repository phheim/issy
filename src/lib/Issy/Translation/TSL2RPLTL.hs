---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Translation.TSL2RPLTL
-- Description : Translation of TSL into RPLTL
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module implements a translation from TSL specifications to RPLTL specifications.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Translation.TSL2RPLTL
  ( tslToRPLTL
  ) where

---------------------------------------------------------------------------------------------------
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

import qualified Issy.Games.Variables as Vars
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Logic.TSLMT as TSL
import qualified Issy.Logic.Temporal as TL

---------------------------------------------------------------------------------------------------
-- | Encodes a TSL formula as an RPLTL formula. Note that this encoding might need
-- to add new variables to properly realize TSL's exactly-one-update-per-cell semantic.
-- In addition, it uses as simple SMT-based simplification to avoid unnecessary encoding parts.
tslToRPLTL :: Config -> TL.Spec TSL.Atom -> IO (TL.Spec Term)
tslToRPLTL conf spec = do
  let vars = TL.variables spec
  needEncode <-
    filterM (fmap not . isPairwiseDisjoint conf . Set.toList . snd)
      $ Map.toList
      $ updateSets vars spec
  let selVars = encode vars needEncode
  vars <-
    pure
      $ foldl (\vars v -> Vars.addStateVar vars v FOL.SBool) vars
      $ concatMap Map.elems
      $ Map.elems selVars
  let excl = exclusive selVars
  pure
    $ TL.Spec
        { TL.variables = vars
        , TL.assumptions =
            map
              (\f -> TL.Or [mapFormula vars selVars f, TL.eventually (TL.Not excl)])
              (TL.assumptions spec)
        , TL.guarantees = TL.globally excl : map (mapFormula vars selVars) (TL.guarantees spec)
        }

type Selectors = Map Symbol (Map Term Symbol)

exclusive :: Selectors -> TL.Formula Term
exclusive sel = TL.And $ concatMap (exactlyOne . Map.elems) $ Map.elems sel
  where
    exactlyOne selVars =
      let selVarsT = map (TL.Atom . FOL.bvarT) selVars
       in TL.Or selVarsT : map (\(a, b) -> TL.Not (TL.And [a, b])) (pairwise selVarsT)

mapFormula :: Variables -> Selectors -> TL.Formula TSL.Atom -> TL.Formula Term
mapFormula vars sel = fmap (mapAtoms vars sel)

mapAtoms :: Variables -> Selectors -> TSL.Atom -> Term
mapAtoms vars sel =
  \case
    TSL.Predicate pred -> pred
    TSL.Update var upd ->
      let effect = Vars.primeT vars (Vars.mk vars var) `FOL.equal` upd
       in case sel !? var of
            Nothing -> effect
            Just selVar -> FOL.andf [effect, FOL.bvarT (selVar ! upd)]

encode :: Variables -> [(Symbol, Set Term)] -> Selectors
encode vars upds =
  let prefix = FOL.uniquePrefix "upd_sel_" $ Vars.allSymbols vars
   in Map.fromList $ map (\(var, upds) -> (var, encodeFor (prefix ++ var) upds)) upds

encodeFor :: String -> Set Term -> Map Term Symbol
encodeFor prefix updTerms =
  Map.fromList
    $ zip (Set.toList updTerms)
    $ map (((prefix ++ "_upd_") ++) . show) [(1 :: Integer) ..]

updateSets :: Variables -> TL.Spec TSL.Atom -> Map Symbol (Set Term)
updateSets vars =
  let selfMap = Map.fromSet (Set.singleton . Vars.mk vars) $ Vars.stateVars vars
   in foldr (\(var, upd) -> Map.adjust (Set.insert upd) var) selfMap . TSL.updates

isPairwiseDisjoint :: Config -> [Term] -> IO Bool
isPairwiseDisjoint conf updTerms =
  SMT.unsat conf $ FOL.orf $ map (uncurry FOL.equal) $ pairwise updTerms

--TODO: Move to utils.extra
pairwise :: [a] -> [(a, a)]
pairwise =
  \case
    [] -> []
    [_] -> []
    x:xr -> map (\y -> (x, y)) xr ++ pairwise xr
---------------------------------------------------------------------------------------------------
