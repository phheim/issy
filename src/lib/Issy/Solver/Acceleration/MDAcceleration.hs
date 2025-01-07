-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Issy.Solver.Acceleration.MDAcceleration where

-------------------------------------------------------------------------------
import Data.Bifunctor (second)
import qualified Data.Set as Set

import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import Issy.Base.Variables (Variables)
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config)
import Issy.Logic.FOL (Constant, Sort, Symbol, Term)
import qualified Issy.Logic.FOL as FOL
import qualified Issy.Logic.SMT as SMT
import Issy.Solver.Acceleration.Heuristics
import Issy.Solver.Acceleration.LoopScenario (loopScenario)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import qualified Issy.Utils.OpenList as OL (fromSet, pop, push)

-------------------------------------------------------------------------------
-- TODO: split until iterA, pipe out, (stAcc `get` loc, cfg, fixedInv)
accReach :: Config -> Int -> Player -> Arena -> Loc -> SymSt -> IO (Term -> ([Term], Term, CFG))
accReach ctx limit player g loc st = do
  let targetInv = g `inv` loc
  (gl, loc, loc', st, fixedInv) <- loopScenario ctx (Just (limit2size limit)) g loc st
  let (base, step, conc, lsym) = error "TODO IMPLEMENT: Probably without lsym!!!"
  pure $ \invar
    -- TODO FIXME: pring does not work like that!!!
   ->
    let st' = set st loc' $ FOL.orf [st `get` loc, FOL.andf [step, Vars.primeT (vars gl) invar]]
        (stAcc, cfg) = iterA player gl st' loc' $ CFG.loopCFG (loc, loc') st lsym step
        cons =
          [ Vars.forallX (vars g) $ FOL.andf [targetInv, base, invar] `FOL.impl` (st `get` loc)
          , Vars.forallX (vars g) $ FOL.andf [targetInv, conc, invar] `FOL.impl` (stAcc `get` loc)
          ]
     in (cons, FOL.andf [conc, fixedInv, invar], cfg)

iterA :: Player -> Arena -> SymSt -> Loc -> CFG -> (SymSt, CFG)
iterA player arena attr shadow = go (noVisits arena) (OL.fromSet (preds arena shadow)) attr
  where
    go vcnt open attr cfgl =
      case OL.pop open of
        Nothing -> (attr, cfgl)
        Just (l, open)
          | visits l vcnt < visitingThreshold ->
            go
              (visit l vcnt)
              (preds arena l `OL.push` open)
              (SymSt.disj attr l $ cpre player arena attr l)
              (CFG.addUpd attr arena l cfgl)
          | otherwise -> go vcnt open attr cfgl

--
-- TODO OVERALL alogrithm:
--
-- 1. guess lemma
-- 2. try a few explicit iterations to find invariant
--
-- TODO: integrate into overall accleration framework and try out!!
--
-- 3.1. try to use explicit CHC stuff  
-- 3.2. try to generalize, i.e. widening, implement in separate module
--
refineInv :: Config -> Int -> Player -> Arena -> Loc -> SymSt -> IO (Term, Bool)
refineInv = error "TODO IMPLEMENT"

-------------------------------------------------------------------------------
-- Manhatten distance lemma generation
--
-- TODO: Make more real number friendly!
-------------------------------------------------------------------------------
lemmaGuess :: Config -> Variables -> Term -> IO (Term, Term, Term)
lemmaGuess conf vars reach = do
  box <- mkBox conf vars reach
  -- TODO: emptiness check!
  let dist = manhatten box
  let base = boxTerm FOL.Const box
  -- TODO FIXME: priming does not work like that!!!
  let step = FOL.func ">" [dist, Vars.primeT vars dist]
  let conc = FOL.true
  pure (base, step, conc)

type Box a = [(Term, (Bool, a))]

boxTerm :: (a -> Term) -> Box a -> Term
boxTerm toTerm = FOL.andf . map go
  where
    go (term, (upper, bound))
      | upper = term `FOL.leqT` toTerm bound
      | otherwise = term `FOL.geqT` toTerm bound

manhatten :: Box Constant -> Term
manhatten = FOL.addT . map go
  where
    go (term, (upper, bound))
      | upper =
        FOL.ite (term `FOL.leqT` FOL.Const bound) FOL.zeroT $ FOL.func "-" [term, FOL.Const bound]
      | otherwise =
        FOL.ite (term `FOL.geqT` FOL.Const bound) FOL.zeroT $ FOL.func "-" [FOL.Const bound, term]

mkBox :: Config -> Variables -> Term -> IO (Box Constant)
mkBox conf vars reach = do
  let boxTerms = generateTerms (error "TODO: max size") vars reach
  (boxScheme, maxTerms) <- prepareBox conf reach boxTerms
  let query = Vars.forallX vars $ reach `FOL.impl` boxTerm (uncurry FOL.Var) boxScheme
  model <- SMT.satModelOpt conf SMT.Paetro query maxTerms
  pure
    $ case model of
        Nothing -> []
        Just model ->
          let toInteger = fmap $ fromConst . FOL.setModel model . uncurry FOL.Var
           in map (second toInteger) boxScheme
  where
    fromConst =
      \case
        FOL.Const c -> c
        _ -> error "assert: result should be an constant"

prepareBox :: Config -> Term -> [Term] -> IO (Box (Symbol, Sort), [Term])
prepareBox conf reach boxTerms = go [] [] boxTerms
  where
    go box maxTerms =
      \case
        [] -> pure (box, maxTerms)
        boxTerm:xr -> do
          let syms = FOL.symbols $ FOL.andf $ [reach] ++ boxTerms ++ map fst box
          let sort = FOL.SInt
          let newname upper
                | upper = FOL.uniqueName "upper" syms
                | otherwise = FOL.uniqueName "lower" syms
          let newvar upper = FOL.Var (newname upper) sort
          let newbox upper = (boxTerm, (upper, (newname upper, sort)))
          up <- boundIn conf True boxTerm reach
          lo <- boundIn conf False boxTerm reach
          case (lo, up) of
            (True, False) ->
              go (newbox False : box) (FOL.func "-" [FOL.zeroT, newvar False] : maxTerms) xr
            (False, True) -> go (newbox True : box) (newvar True : maxTerms) xr
            (True, True) ->
              go
                (newbox True : newbox False : box)
                (FOL.func "-" [newvar True, newvar False] : maxTerms)
                xr
            (False, False) -> go box maxTerms xr

boundIn :: Config -> Bool -> Term -> Term -> IO Bool
boundIn conf upper dimTerm reach = do
  let bound = FOL.ivarT $ FOL.unusedName "bound" $ FOL.andf [dimTerm, reach]
  let vars = Set.toList $ FOL.frees dimTerm `Set.union` FOL.frees reach
  let query =
        FOL.forAll vars
          $ FOL.impl reach
          $ if upper
              then FOL.leqT dimTerm bound
              else FOL.geqT dimTerm bound
  SMT.sat conf query

generateTerms :: Int -> Variables -> Term -> [Term]
generateTerms maxSize vars reach =
  concatMap combToTerms
    $ filter (not . null)
    $ boundPowerList
    $ map (\v -> FOL.Var v (Vars.sortOf vars v))
    $ filter (FOL.isNumber . Vars.sortOf vars)
    $ Set.toList
    $ FOL.frees reach
  where
    combToTerms :: [Term] -> [Term]
    combToTerms =
      map
        (\case
           [] -> error "assert: unreachable code"
           [x] -> x
           xs -> FOL.addT xs)
        . multCombs
    multCombs :: [Term] -> [[Term]]
    multCombs =
      \case
        [] -> error "assert: unreachable code"
        [x] -> [[x]]
        x:xr ->
          let rec = multCombs xr
           in map (x :) rec ++ map (FOL.func "-" [FOL.zeroT, x] :) rec
        --
    boundPowerList :: [a] -> [[a]]
    boundPowerList =
      \case
        [] -> [[]]
        x:xr ->
          let rec = boundPowerList xr
           in rec ++ map (x :) (filter ((< maxSize) . length) rec)
-------------------------------------------------------------------------------
-- Heurisitics
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
