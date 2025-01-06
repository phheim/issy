-------------------------------------------------------------------------------
module Issy.Solver.Acceleration.MDAcceleration where

-------------------------------------------------------------------------------
import Issy.Base.SymbolicState (SymSt, get, set)
import qualified Issy.Base.SymbolicState as SymSt
import qualified Issy.Base.Variables as Vars
import Issy.Config (Config)
import Issy.Logic.FOL
import qualified Issy.Logic.FOL as FOL
import Issy.Solver.Acceleration.Heuristics
import Issy.Solver.Acceleration.LoopScenario (loopScenario)
import Issy.Solver.ControlFlowGraph (CFG)
import qualified Issy.Solver.ControlFlowGraph as CFG
import Issy.Solver.GameInterface
import qualified Issy.Utils.OpenList as OL (fromSet, pop, push)

-------------------------------------------------------------------------------
accReach :: Config -> Int -> Ply -> Game -> Loc -> SymSt -> IO (Term -> ([Term], Term, CFG))
accReach ctx limit player g loc st = do
  let targetInv = g `inv` loc
  (gl, loc, loc', st, fixedInv) <- loopScenario ctx (Just (limit2size limit)) g loc st
  let (base, step, conc, lsym) = error "TODO IMPLEMENT: Probably without lsym!!!"
  pure $ \invar ->
    let st' = set st loc' $ orf [st `get` loc, FOL.andf [step, Vars.primeT (vars gl) invar]]
        (stAcc, cfg) = iterA player gl st' loc' $ CFG.loopCFG (loc, loc') st lsym step
        cons =
          [ Vars.forallX (vars g) $ andf [targetInv, base, invar] `impl` (st `get` loc)
          , Vars.forallX (vars g) $ andf [targetInv, conc, invar] `impl` (stAcc `get` loc)
          ]
     in (cons, andf [conc, fixedInv, invar], cfg)

iterA :: Ply -> Game -> SymSt -> Loc -> CFG -> (SymSt, CFG)
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
-------------------------------------------------------------------------------
{-
estimateTarget :: Config -> Term -> IO Term
estimateTarget = error "TODO IMPLEMENT"

generateTerms :: Config -> Variables -> Term -> [Term]
generateTerms = error "TODO IMPLEMENT"

boundIn :: Config -> Term -> Term -> IO Bool
boundIn = error "TODO IMPLEMENT"

type Box = [(Term, Just Integer, Just Integer)]

mkBox :: Config -> Term -> [Term] -> IO Box
mkBox = error "TODO IMPLEMENT"

mkManhatten :: Config -> Term -> Box -> IO Term
mkManhatten = error "TODO IMPLEMENT"

lemmaGuess :: Config -> Term -> IO (Term, Term, Term)
lemmaGuess = error "TODO IMPLEMENT"

-}
-------------------------------------------------------------------------------
