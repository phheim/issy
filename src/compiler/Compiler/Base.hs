module Compiler.Base where

--
-- Error Handeling
--
type PRes a = Either String a

perr :: Pos -> String -> Either String a
perr p msg = Left $ "Compiler error [" ++ show (lineNum p) ++ ":" ++ show (pos p) ++ "] : " ++ msg

perrGen :: String -> Either String a
perrGen = Left . ("Compiler error : " ++)

--
-- Position Handeling
--
data Pos = Pos
  { lineNum :: Int
  , pos :: Int
  } deriving (Eq, Ord, Show)

initPos :: Pos
initPos = Pos {lineNum = 1, pos = 1}

nextSymbol :: Pos -> Pos
nextSymbol p = p {pos = pos p + 1}

nextLine :: Pos -> Pos
nextLine p = Pos {lineNum = lineNum p + 1, pos = 1}

--
-- Token
--
data Token = Token
  { tpos :: Pos
  , tval :: String
  } deriving (Eq, Ord, Show)

token :: Pos -> String -> Token
token p s = Token {tpos = p, tval = s}

--
-- AST
--
type AstSpec = [AstDef]

data AstDef
  = AstVar AstIO AstSort String
  | AstLogic [AstLogicStm]
  | AstGame AstWC String [AstGameStm]
  deriving (Eq, Ord, Show)

data AstIO
  = AInput
  | AState
  deriving (Eq, Ord, Show)

data AstSort
  = ABool
  | AInt
  | AReal
  deriving (Eq, Ord, Show)

newtype AstWC =
  AstWC String
  deriving (Eq, Ord, Show)

data AstLogicStm
  = AstAssert AstTF
  | AstAssume AstTF
  deriving (Eq, Ord, Show)

data AstTF
  = LAp AstTerm
  | LBConst Bool
  | LUExpr LUOp AstTF
  | LBExpr LBOp AstTF AstTF
  deriving (Eq, Ord, Show)

newtype LUOp =
  LUOp String
  deriving (Eq, Ord, Show)

newtype LBOp =
  LBOp String
  deriving (Eq, Ord, Show)

data AstGameStm
  = ALoc String Integer AstTerm
  | ATrans String String AstTerm
  deriving (Eq, Ord, Show)

data AstTerm
  = AConstInt Integer
  | AConstReal Rational
  | AConstBool Bool
  | ATermVar String
  | ATBexpr TBOP AstTerm AstTerm
  | ATUexpr TUOP AstTerm
  deriving (Eq, Ord, Show)

newtype TBOP =
  TBOP String
  deriving (Eq, Ord, Show)

newtype TUOP =
  TUP String
  deriving (Eq, Ord, Show)
