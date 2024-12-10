module Compiler.Checker
  ( check
  ) where

import Compiler.Base

check :: AstSpec -> PRes ()
check = const $ pure () -- TODO IMPLEMENT
