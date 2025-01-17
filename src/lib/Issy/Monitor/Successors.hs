{-# LANGUAGE LambdaCase #-}

module Issy.Monitor.Successors
  ( generateSuccessor
  ) where

import Data.Bifunctor (first, second)
import Data.Map.Strict ((!?))
import qualified Data.Map.Strict as Map
import Data.Set (Set)

import Issy.Config (Config, setName)
import Issy.Logic.FOL (Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
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
import qualified Issy.Printers.SMTLib as SMTLib (toString)
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
            lg cfg ["Compute Expansion", stateName mon st, strL (strP SMTLib.toString show) assign]
            tree <- computeExpansion cfg (hasUpdates mon) (predicates mon) expState assign
            pure
              (tree, mon {expansionCache = Map.insert (expState, assign) tree (expansionCache mon)})
      (trans, newCtx) <- applySucessorRules cfg oldState (gls mon) expansionTree
      mon <- pure $ mon {gls = newCtx}
      mon <- pure $ foldl addLabel mon (map snd (concat (leafs trans)))
      trans <- pure $ fmap (map (second (revlabel mon))) trans
      mon <- pure $ mon {stateTrans = Map.insert (st, assign) trans (stateTrans mon)}
      return (mon, trans)

applySucessorRules ::
     Config
  -> M.State
  -> GlobalS
  -> Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)]
  -> IO (Trans [([(Bool, Symbol, Term)], M.State)], GlobalS)
applySucessorRules cfg oldState =
  recLeafs
    $ recList
    $ \gls (prop, choices, est) -> do
        let st = fromExpansionState oldState est
        st <- pure $ normSt $ addFacts [prop] st
        (st, gls) <- applyRules cfg gls st
        pure ((choices, st), gls)

computeExpansion ::
     Config
  -> Bool
  -> Set Term
  -> ExpansionState
  -> [(Term, Bool)]
  -> IO (Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)])
computeExpansion cfg hasUpd preds st assign =
  let constr = map polTerm assign
   in computeBranching cfg hasUpd preds constr $ replacesSt assign $ expandSt st

computeBranching ::
     Config
  -> Bool
  -> Set Term
  -> [Term]
  -> ExpansionState
  -> IO (Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)])
computeBranching cfg hasUpd preds = go
  where
    go constr st =
      case pickFreeSt st of
        Just p -> do
          let query pol = polTerm (p, pol) : constr
          let stTrue = replaceSt (p, True) st
          let stFalse = replaceSt (p, False) st
          lg cfg ["branch", "queryTrue", strL SMTLib.toString (query True)]
          lg cfg ["branch", "queryFalse", strL SMTLib.toString (query False)]
          ifM (unsatC cfg (query True)) (go constr stFalse)
            $ ifM (unsatC cfg (query False)) (go constr stTrue)
            $ do
                recP <- go (query True) stTrue
                recN <- go (query False) stFalse
                pure $ trIf p recP recN
        Nothing
          | hasUpd -> TrSucc <$> computeUpdates cfg preds (FOL.andf constr) st
          | otherwise -> do
            prop <- FOL.andf <$> propagatedPredicatesRPLTL cfg (FOL.andf constr) preds
            prop <- SMT.simplify cfg prop
            pure $ TrSucc [(prop, [], normESt (shiftSt st))]

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
          lg cfg ["genUpdates:", "pick (", v, ":=", SMTLib.toString upd, ")"]
          let rec pol = go ((pol, v, upd) : choices) $ setUpdSt (v, upd) pol st
          this <- rec True
          none <- rec False
          pure (this ++ none)
        Nothing -> do
          let upds = (\(_, v, u) -> (v, u)) <$> filter (\(pol, _, _) -> pol) choices
          prop <- FOL.andf <$> propagatedPredicatesTSL cfg constr upds preds
          prop <- SMT.simplify cfg prop
          pure [(prop, choices, normESt (shiftSt st))]

unsatC :: Config -> [Term] -> IO Bool
unsatC cfg = SMT.unsat cfg . FOL.andf

polTerm :: (Term, Bool) -> Term
polTerm (p, True) = p
polTerm (p, False) = FOL.neg p

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
