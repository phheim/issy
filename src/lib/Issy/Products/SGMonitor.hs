module Issy.Products.SGMonitor
  ( onTheFlyProduct
  ) where

import Issy.Base.Objectives (Objective)

-- import qualified Issy.Base.Objectives as Obj
import Issy.Config (Config)

-- import Issy.Logic.FOL(Term)
-- import qualified Issy.Logic.FOL as FOL
import Issy.Monitor (Monitor)

-- import qualified Issy.Monitor as Mon
import Issy.SymbolicArena (Arena)

-- import qualified Issy.SymbolicArena as SG
onTheFlyProduct :: Config -> Arena -> Objective -> Monitor -> IO (Arena, Objective)
onTheFlyProduct = error "TODO FIX: SymbolicGame x Monitor product"
