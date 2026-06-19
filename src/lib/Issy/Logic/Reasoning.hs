---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Logic.Reasoning
-- Description : More complex algorithms for logic reasoning
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module contains more complex algorithms to reason on logic which go
-- beyond simple normalisation operations but are not part of any other modules
-- like reasoning on polyhedra or intervals.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe, LambdaCase #-}

---------------------------------------------------------------------------------------------------
module Issy.Logic.Reasoning
  ( skolemize
  , equalitiesFor
  ) where

---------------------------------------------------------------------------------------------------
import Data.Bifunctor (second)
import qualified Data.List as List (isPrefixOf, nub)
import qualified Data.Map as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Config (Config, setName)
import Issy.Logic.FOL (Function(..), Sort(..), Symbol, Term(..))
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import qualified Issy.Printers.SMTLib as SMTLib
import Issy.Utils.Extra (justOn)
import Issy.Utils.Logging

---------------------------------------------------------------------------------------------------
-- | 'skolemize' computes for a set of variables V and 'Term's t and pre
-- skolem functions for F_v for all v in V, such that the folllowing holds:
--
--  forall (FreeVars(t) \ V). pre(FreeVars(t) \ V) -> t[v -> F_v]
--
-- The usual scenario is that pre := exists V. t.
-- Both 'Term's should be free of uninterpreted functions.
-- It is possible to provide hints for possible skolem functions for the variables.
skolemize :: Config -> [(Symbol, Sort)] -> Map Symbol [Term] -> Term -> Term -> IO (Map Symbol Term)
skolemize conf vars eqHints pre term = do
  if any isSkolem (FOL.frees pre) then error "assert: precondition should not have skolem variables" else 
    if not (any isSkolem (FOL.frees term)) then pure $ Map.fromList $ map (second defaultTerm) vars else
      do
      conf <- pure $ setName "Skolemize" conf
      lgd conf ["Skolem vars", strL fst vars]
      lgv conf ["Precondition", SMTLib.toString pre]
      lgv conf ["Term", SMTLib.toString term]
      -- pre <- SMT.simplify conf pre
      -- term <- SMT.simplify conf term
      (term, skolemEqs) <- eqElim conf vars eqHints pre term
      skolemDirs <- skolemDirect conf vars pre term
      pure $ complete $ Map.fromList $ skolemEqs ++ skolemDirs
  where
    isSkolem v = any ((v ==) . fst) vars
    complete mp =
      foldl
        (\mp (var, sort) ->
           if var `Map.member` mp
             then mp
             else Map.insert var (defaultTerm sort) mp)
        mp
        vars

skolemDirect :: Config -> [(Symbol, Sort)] -> Term -> Term -> IO [(Symbol, Term)]
skolemDirect conf vars pre term
  | null freeSkolems = pure []
  | otherwise = do
    lgd conf ["Skolemize with SMT on", strL fst freeSkolems]
    let termSkolem = FOL.mapTerm (\v s -> justOn (isSkolem v) (skolem v s)) term
    let f = FOL.impl pre termSkolem
    let query = FOL.pushdownQE $ FOL.forAll (Set.toList (FOL.frees f)) f
    model <- SMT.satModel conf query
    case model of
      Nothing -> error $ "assert: precondition was not proper"
      Just model -> do
        model <- pure $ map unskolem $ Map.toList $ FOL.modelToMap model
        lgd conf ["Skolem model", strL (strP id SMTLib.toString) model]
        pure model
  where
    prefix =
      FOL.uniquePrefix "skolem_func_"
        $ FOL.symbols pre `Set.union` FOL.symbols term `Set.union` Set.fromList (map fst vars)
    isSkolem v = any ((v ==) . fst) vars
        --
    freeSkolems = filter ((`elem` FOL.frees term) . fst) vars
        --
    otherVars = filter (not . isSkolem . fst) $ Map.toList $ FOL.bindings $ FOL.impl pre term
    skolem v s = FOL.unintFunc (prefix ++ v) s otherVars
        --
    unskolem (f, t)
      | not (prefix `List.isPrefixOf` f) = error $ "assert: found unkown function " ++ f
      | otherwise =
        let v = drop (length prefix) f
         in (v, FOL.instantiate t (map (uncurry FOL.var) otherVars))

eqElim ::
     Config -> [(Symbol, Sort)] -> Map Symbol [Term] -> Term -> Term -> IO (Term, [(Symbol, Term)])
eqElim conf vars eqHints pre term = do
  --TODO Try adding 'assign to self' to eqHints if no hints are there.
  let varsWithHints = map (\(v,s) -> (v, FOL.var v s, Map.findWithDefault [] v eqHints)) vars
  let eqsPerVariable = filter (\(_,_,eqs)->not.null $ eqs) varsWithHints
  let eqHintsEncoded = FOL.andfL eqsPerVariable encodeVarHint
  let eqHintsTerm = FOL.andf [term, eqHintsEncoded]
  let canUseEqHints = FOL.andf [ FOL.neg $ FOL.exists (map fst vars) eqHintsTerm, pre]
  res <- SMT.sat conf canUseEqHints
  let missingHints = (any (null.snd) $ Map.toAscList eqHints)
  if res || missingHints then 
    go term [] vars
  else
    parAssignEqElim conf eqHints pre term
  where
    go term skolems [] = pure (term, skolems)
    go term skolems ((var, _):vr)
      | var `notElem` FOL.frees term = go term skolems vr
      | otherwise = do
        sk <- tryEqElim conf eqHints vars pre term var
        case sk of
          Nothing -> go term skolems vr
          Just sk -> do
            term <- SMT.simplify conf $ FOL.setSymbolTo var sk term
            go term ((var, sk) : skolems) vr

    encodeVarHint (_,v,eqs) = 
      FOL.orfL eqs (FOL.equal v)

parAssignEqElim ::
    Config -> Map Symbol [Term] -> Term -> Term -> IO (Term, [(Symbol, Term)])
parAssignEqElim conf eqHints pre term = do
  lgd conf ["Use parAssignEqElim"]
  case pre of
    FOL.Const (FOL.CBool False) -> do
      -- This can happen when a safety game has unreachable locations.
      -- These can appear with a winning region of true, but a domain of false.
      -- Idealy there would be no Enforce step at all, but this should prevent crashing in that case.
      lgd conf ["Skolemization was called with a precondition of false, use default assignment."]
      pure (substHints term (head blastedHints) ,head blastedHints) 
    _ -> do
      assigns <- go pre blastedHints
      let substTerm = substHints term assigns
      pure (substTerm, assigns)
  where
    blastedHints = map Map.toAscList $ sequence eqHints
    go :: Term -> [[(Symbol, Term)]] -> IO [(Symbol, Term)]
    go pre [] = do
      lg conf ["eqHints:", show eqHints]
      lg conf ["remaining pre:", SMTLib.toString pre]
      error "assert: using only hints is impossible!"
    go pre (hints:hs) = do
      -- TODO sometimes there is a cheap overapproximation we could check the hints against
      -- before processing the whole term.
      -- For example we could check if a combination of assignments is possible in a symbolic arena.
      let condSet = substHints term hints
      satT <- SMT.sat conf $ FOL.andf [condSet, pre]
      if satT
        then do
          condSet <- SMT.simplify conf condSet
          pre <- SMT.simplify conf $ FOL.andf [pre, FOL.neg condSet]
          satE <- SMT.sat conf pre
          if satE
            then do
              inner <- go pre hs
              --assume the order of symbols matches and never changes
              pure $ zipWith (\(sym, innerTerm) (_, eq) -> (sym, FOL.ite condSet eq innerTerm)) inner hints 
              
            else pure hints
      else go pre hs
    substHints = 
      foldl (\t (sym, ass) -> FOL.setSymbolTo sym ass t)

-- | try to eliminate skolem  functions based on equalities found in the
-- condition
tryEqElim ::
     Config -> Map Symbol [Term] -> [(Symbol, Sort)] -> Term -> Term -> Symbol -> IO (Maybe Term)
tryEqElim conf eqHints vars pre term var = do
  let eqDerived = filter (not . any isSkolem . FOL.frees) $ Set.toList $ equalitiesFor var term
  --let equals = List.nub $ eqDerived ++ Map.findWithDefault [] var eqHints
  let equals = List.nub $ (Map.findWithDefault [] var eqHints) ++ eqDerived 
  lgd conf ["For", var, "use equalties", strL SMTLib.toString equals]
  res <- go pre equals
  case res of
    Nothing -> lgd conf ["Failed to derive skolem function"]
    Just res -> lgd conf ["Derive skolem function", var, ":=", SMTLib.toString res]
  pure res
  where
    isSkolem v = any ((v ==) . fst) vars
    --
    go pre =
      \case
        [] -> pure Nothing
        eq:eqr -> do
          let substEq = FOL.setSymbolTo var eq term
          substEq <- SMT.simplify conf substEq
          let condSet = FOL.exists (map fst vars) $ substEq 
          condSet <- SMT.simplify conf condSet
          satT <- SMT.sat conf condSet
          if satT
            then do
              pre <- SMT.simplify conf $ FOL.andf [pre, FOL.neg condSet]
              satE <- SMT.sat conf pre
              if satE
                then fmap (FOL.ite condSet eq) <$> go pre eqr
                else pure $ Just eq
            else go pre eqr

defaultTerm :: Sort -> Term
defaultTerm =
  \case
    SBool -> FOL.boolConst False
    SInt -> FOL.intConst 0
    SReal -> FOL.realConst 0
    SFunc _ _ -> error "assert: higher-order skolem variables should not happen"

-- | Heuristically extract all terms that are set to equal in a given terms to
-- a given variable. For, example in the term "(x = (y + 1)) && (x > z) (3 = x)",
-- for "x" this are the terms "3" and "y + 1". This method works syntactically, and
-- hence things likes "2x = x + 1" can be missed.
equalitiesFor :: Symbol -> Term -> Set Term
equalitiesFor var = go
  where
    go =
      \case
        Func FEq [st1, st2]
          | var `elem` FOL.frees st1 && var `elem` FOL.frees st2 -> go st1 `Set.union` go st2
          | var `elem` FOL.frees st2 -> go $ Func FEq [st2, st1]
          | var `elem` FOL.frees st1 ->
            case st1 of
              Var v _
                | v == var -> Set.singleton st2
                | otherwise -> error "assert: this should not be reachable"
              Func FMul [Const c, Var v _]
                | v == var -> Set.singleton $ FOL.multT [Const (FOL.invertC c), st2]
                | otherwise -> error "assert: this should not be reachable"
              Func FAdd [] -> error "assert: this should not be reachable"
              Func FAdd (t:ts)
                | var `elem` FOL.frees t -> go $ Func FEq [t, FOL.minusT [st2, Func FAdd ts]]
                | otherwise -> go $ Func FEq [Func FAdd ts, FOL.minusT [st2, t]]
              _ -> Set.empty
          | otherwise -> Set.empty
        Func _ args -> Set.unions $ map go args
        Quant _ _ f -> go f
        Lambda _ f -> go f
        _ -> Set.empty
---------------------------------------------------------------------------------------------------
