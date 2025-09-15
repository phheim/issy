---------------------------------------------------------------------------------------------------
-- | 
-- Module      : Issy.Translation
-- Description : Procedures to translate specifications to their respective one-game representation
-- Copyright   : (c) Philippe Heim, 2025
-- License     : The Unlicense
--
---------------------------------------------------------------------------------------------------
module Issy.Translation
  ( tslToRPG
  , specToSG
  , rpgToSG
  ) where

---------------------------------------------------------------------------------------------------
import Issy.Prelude

import Issy.Config (pruneGame)
import qualified Issy.Logic.TSLMT as TSLMT
import qualified Issy.Logic.Temporal as TL
import qualified Issy.Monitor as Monitor
import qualified Issy.Products.RPGMonitor as RPGMonitor
import qualified Issy.Products.SGMonitor as SGMonitor
import qualified Issy.Products.SymbolicGames as SGProd
import qualified Issy.RPG as RPG
import qualified Issy.Specification as Spec
import qualified Issy.SymbolicArena as SG
import Issy.Translation.RPG2SG (rpgToSG)
import qualified Issy.Translation.RPLTL2SG as RPLTL2SG
import qualified Issy.Translation.TSL2RPG as TSL2RPG

---------------------------------------------------------------------------------------------------
-- | DOCUMENT
specToSG :: Config -> Spec.Specification -> IO (SG.Arena, Objective)
specToSG cfg spec = do
  translatedGames <- mapM (rpltlToSG cfg) (Spec.formulas spec)
  game <- SG.simplifySG cfg $ SGProd.intersection $ Spec.games spec ++ translatedGames
  check <- SG.check cfg $ fst game
  case check of
    Nothing -> pure game
    Just err -> die err

rpltlToSG :: Config -> TL.Spec Term -> IO (SG.Arena, Objective)
rpltlToSG cfg spec = do
  (arena, obj) <- RPLTL2SG.translate cfg spec
  if pruneGame cfg
    then do
      monitor <- Monitor.initializeRPLTL cfg spec
      SGMonitor.onTheFlyProduct cfg arena obj monitor
    else return (arena, obj)

---------------------------------------------------------------------------------------------------
-- | DOCUMENT
tslToRPG :: Config -> TL.Spec TSLMT.Atom -> IO (RPG.Game, Objective)
tslToRPG cfg spec = do
  (game, obj) <- TSL2RPG.tsl2rpg cfg spec
  if pruneGame cfg
    then do
      monitor <- Monitor.initializeTSL cfg spec
      RPGMonitor.onTheFlyProduct cfg game obj monitor
    else return (game, obj)
---------------------------------------------------------------------------------------------------
