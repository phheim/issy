{-# LANGUAGE LambdaCase #-}

module Issy.Products.SGMonitor
  ( onTheFlyProduct
  ) where

import Control.Monad (foldM, when)
import Data.Bifunctor (first)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Issy.Base.Locations (Loc)
import Issy.Base.Objectives (Objective(..), WinningCondition(..))
import qualified Issy.Base.Objectives as Obj
import Issy.Config (Config, setName)
import Issy.Logic.FOL (Term)
import qualified Issy.Logic.FOL as FOL
import Issy.Logic.SMT as SMT
import Issy.Monitor (Monitor, State, Trans(..), Verdict(..))
import qualified Issy.Monitor as Mon
import Issy.Printers.SMTLib as SMTLib
import Issy.SymbolicArena (Arena)
import qualified Issy.SymbolicArena as SG
import Issy.Utils.Logging
import Issy.Utils.OpenList as OL

onTheFlyProduct :: Config -> Arena -> Objective -> Monitor -> IO (Arena, Objective)
onTheFlyProduct cfg arena obj mon = do
  cfg <- pure $ setName "SG x Monitor" cfg
  when (SG.variables arena /= Mon.variables mon)
    $ error "assert: variables of monitor and symbolic game do not match"
  (mon, product) <- explore cfg arena (Obj.initialLoc obj) mon
  lg cfg ["Product", strM (strP show show) (strM (strP show show) SMTLib.smtLib2) product]
  mon <- Mon.finish cfg mon
  let (prodArena, winEnv, winSys, toProd) = productArena arena mon product
  let prodObj =
        Objective
          { initialLoc = toProd (initialLoc obj, Mon.initial mon)
          , winningCond =
              newWC (winEnv, winSys) (Map.keysSet product) (Mon.verdict mon) toProd
                $ winningCond obj
          }
  SG.simplifySG cfg (prodArena, prodObj)

type Product = Map (Loc, State) (Map (Loc, State) Term)

productArena :: Arena -> Monitor -> Product -> (Arena, Loc, Loc, (Loc, State) -> Loc)
productArena arena mon prod =
  let (arena0, toProd) =
        SG.createLocsFor
          (SG.empty (SG.variables arena))
          (\(l, q) -> SG.locName arena l ++ Mon.stateName mon q)
          (SG.domain arena . fst)
          (Map.keys prod)
      (arena1, winSys) = SG.addSink arena0
      (arena2, winEnv) = SG.addSink arena1
      arena3 =
        Map.foldlWithKey
          (\ar lq trans ->
             if null trans
               then error "assert: I do not think this should be possible"
               else Map.foldlWithKey
                      (\ar lq' term ->
                         let next =
                               case Mon.verdict mon (snd lq') of
                                 UNSAFE -> winEnv
                                 VALID -> winSys
                                 _ -> toProd lq'
                             oldTrans = SG.trans ar (toProd lq) next
                          in SG.setTrans ar (toProd lq) next (FOL.orf [term, oldTrans]))
                      ar
                      trans)
          arena2
          prod
   in (arena3, winEnv, winSys, toProd)

explore :: Config -> Arena -> Loc -> Monitor -> IO (Monitor, Product)
explore cfg arena init mon = go (OL.fromList [(init, Mon.initial mon)]) mon Map.empty
  where
    go openList mon prod =
      case OL.pop openList of
        Nothing -> pure (mon, prod)
        Just ((l, q), openList)
          | (l, q) `Map.member` prod -> go openList mon prod
          | otherwise -> do
            (trans, mon) <-
              foldM
                (\(transL, mon) l' ->
                   first (: transL) <$> genTransition cfg mon l' q (SG.trans arena l l'))
                ([], mon)
                (SG.succs arena l)
            -- Remark: The transition maps generated here are disjoint by design!
            trans <- pure $ Map.fromList $ concatMap Map.toList trans
            let openList' =
                  OL.pushList
                    (filter ((`notElem` [VALID, UNSAFE]) . Mon.verdict mon . snd)
                       $ filter (`Map.notMember` prod)
                       $ Map.keys trans)
                    openList
            go openList' mon $ Map.insert (l, q) trans prod

genTransition :: Config -> Monitor -> Loc -> State -> Term -> IO (Map (Loc, State) Term, Monitor)
genTransition cfg mon l' q term = do
  (trans, mon) <- go [] mon term $ Set.toList $ FOL.nonBoolTerms term
  trans <- pure $ Map.fromListWith (\t1 t2 -> FOL.orf [t1, t2]) trans
  trans <- Map.filter (/= FOL.false) <$> mapM (SMT.simplify cfg) trans
  pure (trans, mon)
  where
    go conditions mon term
      | term == FOL.false = const $ pure ([], mon)
      | otherwise =
        \case
          [] -> do
            (mon, trans) <- Mon.generateSuccessor cfg mon q conditions
            trans <-
              pure
                $ fmap
                    (\case
                       [([], q')] -> ((l', q'), term)
                       _ -> error "assert: this monitor should not have any updates!")
                    trans
            trans <- pure $ flattenTrans trans
            pure (trans, mon)
          p:pr -> do
            let rec mon pol = go ((p, pol) : conditions) mon (FOL.setTerm p pol term) pr
            let mpAnd q = map (\(st, t) -> (st, FOL.andf [q, t]))
            (tt, mon) <- rec mon True
            (tf, mon) <- rec mon False
            pure (mpAnd p tt ++ mpAnd (FOL.neg p) tf, mon)
    --
    flattenTrans :: Trans (a, Term) -> [(a, Term)]
    flattenTrans =
      \case
        TrIf p tt tf ->
          let mpAnd q = map (\(a, t) -> (a, FOL.andf [q, t])) . flattenTrans
           in mpAnd p tt ++ mpAnd (FOL.neg p) tf
        TrSucc suc -> [suc]

newWC ::
     (Loc, Loc)
  -> Set (Loc, State)
  -> (State -> Verdict)
  -> ((Loc, State) -> Loc)
  -> WinningCondition
  -> WinningCondition
newWC (winEnv, winSys) prods verdict toNew =
  \case
    Safety olds -> Safety $ winSet olds safety
    Reachability _ -> error "IMPLEMENT FIXME"
    Buechi olds -> Buechi $ winSet olds buechi
    CoBuechi olds -> CoBuechi $ winSet olds coBuechi
    Parity oldCol ->
      Parity
        $ Map.insert winSys 1
        $ Map.insert winEnv 0
        $ Map.mapKeys toNew
        $ Map.fromSet (parity oldCol) prods
  where
    winSet old pred =
      Set.insert
        winSys
        (Set.map toNew (Set.filter (\(l, q) -> pred (l `elem` old, verdict q)) prods))
    --
    safety (lin, ver) = lin && (ver /= UNSAFE) || ver == VALID
    buechi (lin, ver) = lin && (ver /= UNSAFE) || ver `elem` [VALID, SAFETY]
    coBuechi (lin, ver) = lin && (ver /= UNSAFE) || ver `elem` [VALID, SAFETY]
    --
    parity oldCol (l, q) =
      case verdict q of
        OPEN -> oldCol ! l
        SAFETY -> 1
        VALID -> 1
        UNSAFE -> 0
