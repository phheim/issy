{-# LANGUAGE LambdaCase #-}

module Issy.Monitor.Successors
  ( generateSuccessor
  ) where

import Data.Bifunctor (first, second)
import Data.Map.Strict ((!?))
import qualified Data.Map.Strict as Map
import Data.Set (Set)

import Issy.Config (Config, setName)
import Issy.Logic.FOL
import Issy.Logic.SMT (simplify, unsat)
import Issy.Monitor.Monitor
import Issy.Monitor.Propagation
import Issy.Monitor.Rules
import Issy.Monitor.State
  ( ExpansionState
  , addFacts
  , expandSt
  , fromExpansionState
  , normESt
  , normSt
  , pickFreeSt
  , pickUpdSt
  , replaceSt
  , replacesSt
  , setUpdSt
  , shiftSt
  , toExpansionState
  )
import qualified Issy.Monitor.State as M (State)
import Issy.Printers.SMTLib (smtLib2)
import Issy.Utils.Extra
import Issy.Utils.Logging

generateSuccessor ::
     Config
  -> Monitor
  -> State
  -> [(Term, Bool)]
  -> IO (Monitor, Trans [([(Bool, Symbol, Term)], State)])
generateSuccessor cfg mon st assign = do
  cfg <- pure $ setName "Monitor" cfg
  case stateTrans mon !? (st, assign) of
    Just trans -> return (mon, trans)
    Nothing -> do
      let oldState = label mon st
      let expState = toExpansionState oldState
      (expansionTree, mon) <-
        case expansionCache mon !? (expState, assign) of
          Just tree -> pure (tree, mon)
          Nothing -> do
            lg cfg ["Compute Expansion", stateName mon st, strL (strP smtLib2 show) assign]
            tree <- computeExpansion cfg (predicates mon) expState assign
            pure
              (tree, mon {expansionCache = Map.insert (expState, assign) tree (expansionCache mon)})
      (trans, newCtx) <- applySucessorRules cfg oldState (ctx mon) expansionTree
      mon <- pure $ mon {ctx = newCtx}
      mon <- pure $ foldl addLabel mon (map snd (concat (leafs trans)))
      trans <- pure $ fmap (map (second (revlabel mon))) trans
      mon <- pure $ mon {stateTrans = Map.insert (st, assign) trans (stateTrans mon)}
      return (mon, trans)

applySucessorRules ::
     Config
  -> M.State
  -> Context
  -> Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)]
  -> IO (Trans [([(Bool, Symbol, Term)], M.State)], Context)
applySucessorRules cfg oldState =
  recLeafs
    $ recList
    $ \ctx (prop, choices, est) -> do
        let st = fromExpansionState oldState est
        st <- pure $ normSt $ addFacts [prop] st
        (st, ctx) <- applyRules cfg ctx st
        pure ((choices, st), ctx)

computeExpansion ::
     Config
  -> Set Term
  -> ExpansionState
  -> [(Term, Bool)]
  -> IO (Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)])
computeExpansion cfg preds st assign =
  let constr = map polTerm assign
   in computeBranching cfg preds constr $ replacesSt assign $ expandSt st

computeBranching ::
     Config
  -> Set Term
  -> [Term]
  -> ExpansionState
  -> IO (Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)])
computeBranching cfg preds = go
  where
    go constr st =
      case pickFreeSt st of
        Just p -> do
          let query pol = polTerm (p, pol) : constr
          let stTrue = replaceSt (p, True) st
          let stFalse = replaceSt (p, False) st
          lg cfg ["branch", "queryTrue", strL smtLib2 (query True)]
          lg cfg ["branch", "queryFalse", strL smtLib2 (query False)]
          ifM (unsatC cfg (query True)) (go constr stFalse)
            $ ifM (unsatC cfg (query False)) (go constr stTrue)
            $ do
                recP <- go (query True) stTrue
                recN <- go (query False) stFalse
                pure $ trIf p recP recN
        Nothing -> TrSucc <$> computeUpdates cfg preds (andf constr) st

computeUpdates ::
     Config
  -> Set Term
  -> Term
  -> ExpansionState
  -> IO [(Term, [(Bool, Symbol, Term)], ExpansionState)]
computeUpdates cfg preds constr = go []
  where
    go choices st =
      case pickUpdSt st of
        Just (v, upd) -> do
          lg cfg ["genUpdates:", "pick (", v, ":=", smtLib2 upd, ")"]
          let rec pol = go ((pol, v, upd) : choices) $ setUpdSt (v, upd) pol st
          this <- rec True
          none <- rec False
          pure (this ++ none)
        Nothing -> do
          let upds = (\(_, v, u) -> (v, u)) <$> filter (\(pol, _, _) -> pol) choices
          prop <- andf <$> propagatedPredicates cfg constr upds preds
          prop <- simplify cfg prop
          pure [(prop, choices, normESt (shiftSt st))]

unsatC :: Config -> [Term] -> IO Bool
unsatC cfg = unsat cfg . andf

polTerm :: (Term, Bool) -> Term
polTerm (p, True) = p
polTerm (p, False) = neg p

recLeafs :: Monad m => (c -> a -> m (b, c)) -> c -> Trans a -> m (Trans b, c)
recLeafs func c =
  \case
    TrSucc a -> do
      (b, c) <- func c a
      pure (TrSucc b, c)
    TrIf p tt tf -> do
      (tt, c) <- recLeafs func c tt
      (tf, c) <- recLeafs func c tf
      pure (TrIf p tt tf, c)

recList :: Monad m => (c -> a -> m (b, c)) -> c -> [a] -> m ([b], c)
recList func c =
  \case
    [] -> pure ([], c)
    x:xr -> do
      (x, c) <- func c x
      first (x :) <$> recList func c xr
