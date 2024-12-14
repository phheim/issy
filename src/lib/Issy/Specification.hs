module Issy.Specification
  ( Specification
  , -- access
    variables
  , formulas
  , games
  , -- consturction
    empty
  , addFormula
  , addGame
  , -- checking
    checkSpecification
  ) where

import Issy.Base.Objectives (Objective)
import qualified Issy.Base.Objectives as Obj
import Issy.Base.Variables (Variables)
import Issy.Config (Config)
import qualified Issy.Logic.RPLTL as RPLTL
import qualified Issy.SymbolicArena as SG

-- Invariant: only one non-safety part and all the same variables
data Specification = Specification
  { variables :: Variables
  , formulas :: [RPLTL.Spec]
  , games :: [(SG.Arena, Objective)]
  , hadNonSafety :: Bool
  } deriving (Eq, Ord, Show)

empty :: Variables -> Specification
empty vars = Specification {variables = vars, formulas = [], games = [], hadNonSafety = False}

addFormula :: Specification -> RPLTL.Spec -> Either String Specification
addFormula spec formula
  | variables spec /= RPLTL.variables formula =
    error "assert: tried to add formula with different variables"
  | hadNonSafety spec && not (RPLTL.isSafety formula) = Left "Found second non-safety formula"
  | otherwise =
    Right
      $ spec
          { formulas = formulas spec ++ [formula]
          , hadNonSafety = hadNonSafety spec || not (RPLTL.isSafety formula)
          }

addGame :: Specification -> SG.Arena -> Objective -> Either String Specification
addGame spec arena obj
  | variables spec /= SG.variables arena =
    error "assert: tried to add formula with different variables"
  | hadNonSafety spec && not (Obj.isSafety obj) = Left "Found second non-safety game"
  | otherwise =
    Right
      $ spec
          { games = games spec ++ [(arena, obj)]
          , hadNonSafety = hadNonSafety spec || not (Obj.isSafety obj)
          }

checkSpecification :: Config -> Specification -> IO (Either String ())
checkSpecification cfg = go (1 :: Int) . games
  where
    go _ [] = pure $ Right ()
    go n (g:gr) = do
      check <- SG.check cfg (fst g)
      case check of
        Nothing -> go (n + 1) gr
        Just err -> pure $ Left $ "game number " ++ show n ++ " is invalid: " ++ err
