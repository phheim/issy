---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Translation.LTL2DOA
-- Description : TODO DOCUMENT
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

module Issy.Translation.LTL2DOA
  ( translate
  ) where

import qualified Data.List as List (sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Issy.Prelude
import System.Process (readProcessWithExitCode)

import Hanoi
  ( AcceptanceSet
  , AcceptanceType(..)
  , Formula(..)
  , HOA(..)
  , HOAAcceptanceName(Buchi, ParityMaxOdd, Streett)
  , HOAProperty(COLORED, COMPLETE, DETERMINISTIC)
  )
import qualified Hanoi as HOA (State, parse, printHOA, states, atomicProps)

import Issy.Config (ltl2tgba)
import qualified Issy.Logic.Temporal as TL
import qualified Issy.Translation.DOA as DOA

spotHOA :: Config -> [String] -> String -> IO HOA
spotHOA cfg options ltlstr = do
  let opts = options ++ ["--deterministic", "--state-based-acceptance", "--complete", "-"]
  lgv cfg $ ["Spot run:", ltl2tgba cfg] ++ opts ++ [ltlstr]
  (_, stdout, _) <- readProcessWithExitCode (ltl2tgba cfg) opts ltlstr
  lgv cfg ["Spot return:", stdout]
  case HOA.parse stdout of
    Left err -> error err
    Right hoa -> return hoa

toLTLStr :: (a -> String) -> TL.Formula a -> String
toLTLStr ap2str = go
  where
    go =
      \case
        TL.Atom atom -> ap2str atom
        TL.And fs -> nop "&" "true" $ map go fs
        TL.Or fs -> nop "|" "false" $ map go fs
        TL.Not f -> "(! " ++ go f ++ ")"
        TL.UExp op f -> "(" ++ uop2str op ++ " " ++ go f ++ ")"
        TL.BExp op f g -> "(" ++ go f ++ " " ++ bop2str op ++ " " ++ go g ++ ")"
     --
    nop _ neut [] = neut
    nop op _ (f:fr) = "(" ++ f ++ concatMap (\g -> " " ++ op ++ " " ++ g) fr ++ ")"
     --
    bop2str =
      \case
        TL.Until -> "U"
        TL.WeakUntil -> "W"
        TL.Release -> "R"
     --
    uop2str =
      \case
        TL.Next -> "X"
        TL.Globally -> "G"
        TL.Eventually -> "F"

translate :: Config -> (a -> String) -> TL.Formula a -> IO (DOA.DOA String)
translate cfg ap2str formula = do
  let ltlstr = toLTLStr ap2str formula
  lg cfg ["LTL:", ltlstr]
  hoa <- spotHOA cfg ["--buchi"] ltlstr
  checkProp hoa COMPLETE
  if DETERMINISTIC `elem` properties hoa
    then do
      lg cfg ("HOA Buechi:" : lines (HOA.printHOA hoa))
      return $ hoa2doa hoa
    else do
      hoa <- spotHOA cfg ["--colored-parity=max odd"] ltlstr
      lg cfg ("HOA Parity:" : lines (HOA.printHOA hoa))
      checkProp hoa COMPLETE
      checkProp hoa DETERMINISTIC
      checkProp hoa COLORED
      return $ hoa2doa hoa
  where
    checkProp hoa prop =
      unless (prop `elem` properties hoa) $ fail $ "automaton expected to contain " ++ show prop

hoa2doa :: HOA -> DOA.DOA String
hoa2doa hoa =
  let (doa, stateMap) = hoastruct2doa hoa
      accept = hoa2doaAccept (stateMap !) hoa
   in DOA.setAcceptance accept doa

hoastruct2doa :: HOA -> (DOA.DOA String, Map HOA.State DOA.State)
hoastruct2doa hoa =
  let doa0 = DOA.initDOA (Set.fromList (hoaAtoms hoa)) (size hoa)
      statesMap = Map.fromList $ zip (hoaStates hoa) (DOA.stateList doa0)
      fromState st = fromMaybe (error ("Unmapped HOA state " ++ show statesMap)) $ statesMap !? st
      doa1 = DOA.setInitial (getInitial fromState hoa) doa0
      doa2 =
        foldl
          (\doa st -> DOA.setTrans (fromState st) (genTrans fromState st) doa)
          doa1
          (hoaStates hoa)
   in (doa2, statesMap)
  where
    genTrans fromState = Set.unions . Set.map (genEdges fromState) . edges hoa
    --
    genEdges fromState =
      \case
        (_, Nothing, _) -> error "expected transition label"
        (_, _, Just _) -> error "expected not transition acceptance"
        ([st], Just label, _) -> Set.map (genEdge fromState st) (toDNF label)
        _ -> error "expected non-branching automaton"
    --
    genEdge fromState st clause = (Set.map (first (atomicPropositionName hoa)) clause, fromState st)

hoa2doaAccept :: (HOA.State -> DOA.State) -> HOA -> DOA.Acceptance
hoa2doaAccept fromState hoa =
  case acceptanceName hoa of
    Nothing -> error "expected acceptance name"
    Just accName ->
      case accName of
        Buchi ->
          let rep = matchBuechi (Hanoi.acceptance hoa)
              acc =
                filter
                  (\st ->
                     case stateAcceptance hoa st of
                       Nothing -> False
                       Just accSets -> rep `elem` accSets)
                  $ hoaStates hoa
           in DOA.Buechi $ Set.fromList $ map fromState acc
        ParityMaxOdd numCols ->
          let parity =
                Map.fromList $ matchParity (numCols - 1) (Hanoi.acceptance hoa) -- does not work if numCols is 0
              acc =
                map
                  (\st ->
                     case Set.toList <$> stateAcceptance hoa st of
                       Just [accSet] -> (st, parity ! accSet)
                       _ -> error "expected colored automaton")
                  $ hoaStates hoa
           in DOA.Parity $ Map.mapKeys fromState $ Map.fromList acc
        Streett 1 ->
          let parity = Map.fromList $ matchStreet1 $ Hanoi.acceptance hoa
              acc =
                map
                  (\st ->
                     case Set.toList <$> stateAcceptance hoa st of
                       Just [accSet] -> (st, parity ! accSet)
                       _ -> error "expected colored automaton")
                  $ hoaStates hoa
           in DOA.Parity $ Map.mapKeys fromState $ Map.fromList acc
        _ ->
          error $ "illegal acceptance name " ++ show accName ++ " " ++ show (Hanoi.acceptance hoa)
  where
    matchBuechi :: Formula AcceptanceType -> AcceptanceSet
    matchBuechi =
      \case
        FVar (Inf True rep) -> rep
        _ -> error "Found non-canonical acceptance condition for Büchi acceptance"
    --
    matchParity :: Int -> Formula AcceptanceType -> [(AcceptanceSet, Word)]
    matchParity col form =
      case (col, odd col, form) of
        (0, _, FVar (Fin True accs)) -> [(accs, 0)]
        (_, True, FOr [FVar (Inf True accs), rest]) ->
          (accs, toEnum col) : matchParity (col - 1) rest
        (_, False, FAnd [FVar (Fin True accs), rest]) ->
          (accs, toEnum col) : matchParity (col - 1) rest
        _ ->
          error
            ("Found non-canonical acceptance condition for parity acceptance "
               ++ show col
               ++ " "
               ++ show form)
    --
    matchStreet1 :: Formula AcceptanceType -> [(AcceptanceSet, Word)]
    matchStreet1 =
      \case
        FOr [FVar (Fin True afin), FVar (Inf True ainf)] -> [(ainf, 1), (afin, 0)]
        FOr [FVar (Inf True afin), FVar (Fin True ainf)] -> [(ainf, 1), (afin, 0)]
        form -> error $ "Found non-canonical Street 1 acceptance " ++ show form

-- TODO inline
hoaStates :: HOA -> [HOA.State]
hoaStates = HOA.states

-- TODO inline
hoaAtoms :: HOA -> [String]
hoaAtoms hoa = atomicPropositionName hoa <$> HOA.atomicProps hoa

getInitial :: (HOA.State -> DOA.State) -> HOA -> DOA.State
getInitial fromState hoa =
  case Set.toList (initialStates hoa) of
    [[st]] -> fromState st
    _ -> error "assert: HOA not deterministic"

toDNF :: Ord a => Formula a -> Set (Set (a, Bool))
toDNF =
  \case
    FTrue -> Set.singleton Set.empty
    FFalse -> Set.empty
    FVar a -> Set.singleton $ Set.singleton (a, True)
    FOr fs -> Set.unions (map toDNF fs)
    FAnd [] -> toDNF FTrue
    FAnd (f:fr) ->
      let dnf = toDNF f
          dnfs = toDNF (FAnd fr)
       in Set.map (uncurry Set.union) $ Set.cartesianProduct dnf dnfs
        -- Negation pushing
    FNot FTrue -> toDNF FFalse
    FNot FFalse -> toDNF FTrue
    FNot (FVar a) -> Set.singleton $ Set.singleton (a, False)
    FNot (FAnd fs) -> toDNF (FOr (map FNot fs))
    FNot (FOr fs) -> toDNF (FAnd (map FNot fs))
    FNot (FNot f) -> toDNF f
---------------------------------------------------------------------------------------------------
