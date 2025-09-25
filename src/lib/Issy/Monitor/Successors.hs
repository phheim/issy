{-# LANGUAGE LambdaCase #-}

module Issy.Monitor.Successors
  ( generateSuccessor
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude

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

generateSuccessor ::
     Config
  -> Monitor
  -> State
  -> Set (Term, Bool)
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
            lg cfg ["Compute Expansion", stateName mon st, strS (strP SMTLib.toString show) assign]
            tree <-
              computeExpansion cfg (variables mon) (hasUpdates mon) (predicates mon) expState assign
            pure
              (tree, mon {expansionCache = Map.insert (expState, assign) tree (expansionCache mon)})
      (trans, newCtx) <- applySucessorRules cfg oldState (gls mon) expansionTree
      mon <- pure $ mon {gls = newCtx}
      mon <- pure $ foldl addLabel mon (map snd (concat (leafs trans)))
      trans <- pure $ fmap (map (second (revlabel mon))) trans
      mon <- pure $ mon {stateTrans = Map.insert (st, assign) trans (stateTrans mon)}
      pure (mon, trans)

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
  -> Variables
  -> Bool
  -> Set Term
  -> ExpansionState
  -> Set (Term, Bool)
  -> IO (Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)])
computeExpansion cfg vars hasUpd preds st assign = do
  let constr = FOL.andf $ map polTerm $ Set.toList assign
  constr <- SMT.simplify cfg constr
  computeBranching cfg vars hasUpd preds constr $ replacesSt assign $ expandSt st

computeBranching ::
     Config
  -> Variables
  -> Bool
  -> Set Term
  -> Term
  -> ExpansionState
  -> IO (Trans [(Term, [(Bool, Symbol, Term)], ExpansionState)])
computeBranching cfg vars hasUpd preds = go
  where
    -- TODO: can constr be false?
    go constr st =
      case pickFreeSt st of
        Just p -> do
          let query pol = FOL.andf [polTerm (p, pol), constr]
          queryTrue <- SMT.simplify cfg (query True)
          queryFalse <- SMT.simplify cfg (query False)
          let stTrue = replaceSt (p, True) st
          let stFalse = replaceSt (p, False) st
          lg cfg ["branch", "queryTrue", SMTLib.toString queryTrue]
          lg cfg ["branch", "queryFalse", SMTLib.toString queryFalse]
          ifM (SMT.unsat cfg queryTrue) (go constr stFalse)
            $ ifM (SMT.unsat cfg queryFalse) (go constr stTrue)
            $ do
                recP <- go queryTrue stTrue
                recN <- go queryFalse stFalse
                pure $ trIf p recP recN
        Nothing
          | hasUpd -> TrSucc <$> computeUpdates cfg preds constr st
          | otherwise -> do
            prop <- FOL.andf <$> propagatedPredicatesRPLTL cfg vars constr preds
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
