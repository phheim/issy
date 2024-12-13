module Issy.Translation
  ( tslToRPG
  , rpltlToSG
  , specToSG
  ) where

import Issy.Base.Objectives (Objective)
import Issy.Config (Config, pruneGame)
import qualified Issy.Logic.RPLTL as RPLTL (Spec)
import qualified Issy.Logic.TSLMT as TSLMT (Spec)
import qualified Issy.Monitor as Monitor (initializeRPLTL, initializeTSL)
import qualified Issy.Products.RPGMonitor as RPGMonitor (onTheFlyProduct)
import qualified Issy.Products.SGMonitor as SGMonitor (onTheFlyProduct)
import qualified Issy.Products.SymbolicGames as SGProd (intersection)
import qualified Issy.RPG as RPG (Game)
import qualified Issy.Specification as Spec
import qualified Issy.SymbolicArena as SG (Arena, simplifySG)
import qualified Issy.Translation.RPLTL2SG as RPLTL2SG (translate)
import qualified Issy.Translation.TSL2RPG as TSL2RPG (tsl2rpg)

tslToRPG :: Config -> TSLMT.Spec -> IO (RPG.Game, Objective)
tslToRPG cfg spec = do
  (game, obj) <- TSL2RPG.tsl2rpg cfg spec
  if pruneGame cfg
    then do
      monitor <- Monitor.initializeTSL cfg spec
      RPGMonitor.onTheFlyProduct cfg game obj monitor
    else return (game, obj)

rpltlToSG :: Config -> RPLTL.Spec -> IO (SG.Arena, Objective)
rpltlToSG cfg spec = do
  (arena, obj) <- RPLTL2SG.translate cfg spec
  if pruneGame cfg
    then do
      monitor <- Monitor.initializeRPLTL cfg spec
      SGMonitor.onTheFlyProduct cfg arena obj monitor
    else return (arena, obj)

specToSG :: Config -> Spec.Specification -> IO (SG.Arena, Objective)
specToSG cfg spec = do
  translatedGames <- mapM (rpltlToSG cfg) (Spec.formulas spec)
  SG.simplifySG cfg $ SGProd.intersection $ Spec.games spec ++ translatedGames
