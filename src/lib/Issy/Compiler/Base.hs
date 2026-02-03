---------------------------------------------------------------------------------------------------
-- |
-- Module      : Issy.Compiler.Base
-- Description : Base components for the issy-format to llissy-format compiler
-- Copyright   : (c) Philippe Heim, 2026
-- License     : The Unlicense
--
-- This module contains the base components for the issy-to-llissy compiler. This
-- includes error, position, and token handling. It also includes the representation
-- of the specification AST.
---------------------------------------------------------------------------------------------------
{-# LANGUAGE Safe #-}

---------------------------------------------------------------------------------------------------
module Issy.Compiler.Base
  ( PRes
  , perr
  , perrGen
  , Pos
  , initPos
  , nextSymbol
  , nextLine
  , posStr
  , Token(..)
  , token
  , AstSpec
  , AstDef(..)
  , AstIO(..)
  , AstSort(..)
  , AstWC(..)
  , AstLogicStm(..)
  , AstTF(..)
  , ATUOP(..)
  , ATBOP(..)
  , AstGameStm(..)
  , AstTerm(..)
  , ABUOP(..)
  , ABBOP(..)
  , AstAtom(..)
  , AstGround(..)
  , AGUOP(..)
  , AGBOP(..)
  ) where

---------------------------------------------------------------------------------------------------
-- Positions
---------------------------------------------------------------------------------------------------
-- | The position inside an input string. It is composed of the line number and
-- the position within this line. The count of both positions starts with one.
data Pos = Pos
  { lineNum :: Int
  -- ^ the line number, starting from one
  , pos :: Int
  -- ^ the character count within the line
  } deriving (Eq, Ord, Show)

-- | 'initPos' is the initial position
initPos :: Pos
initPos = Pos {lineNum = 1, pos = 1}

-- | 'nextSymbol' is the next position within the same line
-- (i.e. for the next non-newline character)
nextSymbol :: Pos -> Pos
nextSymbol p = p {pos = pos p + 1}

-- | 'nextLine' is the position of the next line
nextLine :: Pos -> Pos
nextLine p = Pos {lineNum = lineNum p + 1, pos = 1}

-- | 'posStr' prints the position as an easy to read and interpretable string
posStr :: Pos -> String
posStr p = "[" ++ show (lineNum p) ++ ":" ++ show (pos p) ++ "]"

---------------------------------------------------------------------------------------------------
-- Errors
---------------------------------------------------------------------------------------------------
-- | Many steps of the compiler will either return some value or an error with an error message.
-- 'PRes' allows to write the respective return type compactly and uniformly.
type PRes a = Either String a

-- | 'perr' creates a compiler error at a specific position
perr :: Pos -> String -> Either String a
perr p msg = Left $ "Compiler error at " ++ posStr p ++ " : " ++ msg

-- | 'perrGen' creates a generic compiler error without a position
perrGen :: String -> Either String a
perrGen = Left . ("Compiler error : " ++)

---------------------------------------------------------------------------------------------------
-- Tokens
---------------------------------------------------------------------------------------------------
-- | Represents a token while parsing. A token has a value (which is a string)
-- and a position for error tracking.
data Token = Token
  { tpos :: Pos
  -- ^ 'tpos' is the position of the token. For multi-character tokens, e.g. keywords,
  -- this should be the location of the first character in the token
  , tval :: String
  -- ^ 'tval' is the content of the token, i.e. a sub-string of the overall input
  -- that represents this token
  } deriving (Eq, Ord, Show)

-- | Creates a token. The position of the token should be the position of
-- the first character of content string.
token :: Pos -> String -> Token
token p s = Token {tpos = p, tval = s}

---------------------------------------------------------------------------------------------------
-- Abstract Syntax Tree
---------------------------------------------------------------------------------------------------
-- | Representation of the full AST of a issy-format specification
type AstSpec = [AstDef]

-- | The AST representation of a definition in an specification
data AstDef
  = AstVar Pos AstIO AstSort String
  -- ^ this is a input or state variable definition
  | AstLogic Pos [AstLogicStm]
  -- ^ this is the definition of logic specification,
  -- the interpretation is that the conjunction of assumptions
  -- implies the conjunction of assertions
  | AstGame Pos AstWC String [AstGameStm]
  -- ^ this is the definition of a game specification
  | AstMacro Pos String AstTerm
  -- ^ this is a macro definition
  deriving (Eq, Ord, Show)

-- | AST enum for input and states
data AstIO
  = AInput
  -- ^ indicates an input
  | AState
  -- ^ indicates a state
  deriving (Eq, Ord, Show)

-- | AST enum for sorts
data AstSort
  = ABool
  -- ^ indicates a boolean sort
  | AInt
  -- ^ indicates a integer sort
  | AReal
  -- ^ indicates a real-value sort
  deriving (Eq, Ord, Show)

-- | AST enum for game winning conditions
data AstWC
  = ASafety
  -- ^ safety winning condition
  | AReachability
  -- ^ reachability winning condition
  | ABuechi
  -- ^ Büchi winning condition
  | ACoBuechi
  -- ^ co-Büchi winning condition
  | AParityMaxOdd
  -- ^ parity (max odd) winning condition
  deriving (Eq, Ord, Show)

-- | AST representation of assumptions and assertions (guarantees)
-- in a temporal logic specification. Note that those are interpreted
-- as a whole withing one temporal logic specification block
data AstLogicStm
  = AstAssert Pos AstTF
  -- ^ temporal logic assertions / guarantees
  | AstAssume Pos AstTF
  -- ^ temporal logic assumptions
  deriving (Eq, Ord, Show)

-- | AST representation of an RPLTL formula
data AstTF
  = AFAtom Pos AstAtom
  -- ^ first-order ground terms
  | AFUexp Pos ATUOP AstTF
  -- ^ unary temporal-logic expressions
  | AFBexp Pos ATBOP AstTF AstTF
  -- ^ binary temporal-logic expressions
  deriving (Eq, Ord, Show)

-- | AST enum for unary temporal-logic operators
data ATUOP
  = ATUNot
  -- ^ temporal-logic boolean negation
  | ATUNext
  -- ^ temporal-logic next operator
  | ATUGlobally
  -- ^ temporal-logic globally operator
  | ATUEventually
  -- ^ temporal-logic eventually operator
  deriving (Eq, Ord, Show)

-- | AST enum for binary temporal-logic operators
data ATBOP
  = ATBAnd
  -- ^ temporal-logic boolean conjunction
  | ATBOr
  -- ^ temporal-logic boolean disjunction
  | ATBImpl
  -- ^ temporal-logic boolean implication
  | ATBIff
  -- ^ temporal-logic boolean equivalence
  | ATBUntil
  -- ^ temporal-logic until
  | ATBWeak
  -- ^ temporal-logic weak until
  | ATBRelease
  -- ^ temporal-logic release
  deriving (Eq, Ord, Show)

-- | AST representation of statements inside a game block
data AstGameStm
  = ALoc Pos String Integer AstTerm
  -- ^ declaration of a location with name, rank (acceptance), and domain
  | ATrans Pos String String AstTerm
  -- ^ definition of a transition, with source and target location, and transition predicate
  deriving (Eq, Ord, Show)

-- | AST representation of boolean (non-temporal) terms that are used inside games
data AstTerm
  = ATAtom Pos AstAtom
  -- ^ an atom which itself is ground term (which could again be boolean)
  | ATBexp Pos ABBOP AstTerm AstTerm
  -- ^ boolean binary expression
  | ATUexp Pos ABUOP AstTerm
  -- ^ boolean unary expression
  deriving (Eq, Ord, Show)

-- | AST enum for unary operators in plain boolean terms
data ABUOP =
  ABUNot
  -- ^ boolean negation
  deriving (Eq, Ord, Show)

-- | AST enum for binary operators in plain boolean terms
data ABBOP
  = ABBAnd
  -- ^ boolean conjunction
  | ABBOr
  -- ^ boolean disjunction
  | ABBImpl
  -- ^ boolean implication
  | ABBIff
  -- ^ boolean equivalence
  deriving (Eq, Ord, Show)

-- | AST representation of an atom. An atom is one layer above ground terms
-- to avoid putting boolean constants, variables, and macros as bracketed terms.
-- This allows enables the "keep" and "havoc" statement.
data AstAtom
  = AABool Pos Bool
  -- ^ atom version of a boolean constant
  | AAGround Pos AstGround
  -- ^ ground term
  | AAVar Pos String
  -- ^ boolean variable name for input, state, primed state,
  -- or macro name for boolean macros
  | AAKeep Pos [String]
  -- ^ keep statement
  | AAHavoc Pos [String]
  -- ^ havoc statement
  deriving (Eq, Ord, Show)

-- | AST representation of ground terms
data AstGround
  = AConstInt Pos Integer
  -- ^ integer-value constant
  | AConstReal Pos Rational
  -- ^ real-value constant
  | AConstBool Pos Bool
  -- ^ boolean constant
  | AGVar Pos String
  -- ^ variable name for input, state, primed state, or macro name for term macros
  | AGBexp Pos AGBOP AstGround AstGround
  -- ^ binary expression ground term
  | AGUexp Pos AGUOP AstGround
  -- ^ unary expression ground term
  deriving (Eq, Ord, Show)

-- | AST enum for ground term unary operators
data AGUOP
  = AGUNot
  -- ^ ground-term boolean negation
  | AGUMinus
  -- ^ unary minus operator
  | AGUAbs
  -- ^ absolute value operator
  deriving (Eq, Ord, Show)

-- | AST enum for ground term unary operators
data AGBOP
  = AGBAnd
  -- ^ ground-term boolean conjunction
  | AGBOr
  -- ^ ground-term boolean disjunction
  | AGBEq
  -- ^ equal operator
  | AGBLt
  -- ^ less-than operator
  | AGBGt
  -- ^ greater-than operator
  | AGBLte
  -- ^ less-than-equal operator
  | AGBGte
  -- ^ greater-than-equal operator
  | AGBPlus
  -- ^ arithmetic addition operator
  | AGBMinus
  -- ^ arithmetic subtraction operator
  | AGBMult
  -- ^ arithmetic multiplication operator
  | AGBDiv
  -- ^ arithmetic division operator
  | AGBMod
  -- ^ integer modulo operator
  deriving (Eq, Ord, Show)
---------------------------------------------------------------------------------------------------
