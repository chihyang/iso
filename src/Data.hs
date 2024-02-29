module Data (module Data) where

-- Type
data BaseType =
  BTyUnit
  | BTyInt
  | BTyVar String
  | BTySum BaseType BaseType
  | BTyProd BaseType BaseType
  | BTyMu String BaseType
  deriving (Eq, Ord)
instance Show BaseType where
  show BTyUnit = "Unit"
  show BTyInt = "Nat"
  show (BTyVar var) = show var
  show (BTySum lt rt) = "(" ++ show lt ++ " + " ++ show rt ++ ")"
  show (BTyProd lt rt) = "(" ++ show lt ++ " x " ++ show rt ++ ")"
  show (BTyMu var bodyT) = "mu." ++ show var ++ " " ++ show bodyT ++ ""

data IsoType =
  ITyBase BaseType BaseType
  | ITyFun BaseType BaseType IsoType
  deriving (Eq, Ord)
instance Show IsoType where
  show (ITyBase lt rt) = show lt ++ " <-> " ++ show rt
  show (ITyFun lt rt bodyT) = "(" ++ show lt ++ " <-> " ++ show rt ++ ") -> " ++ show bodyT

type ProgramType = Either BaseType IsoType

-- Syntax
data Value =
  ValUnit
  | ValInt Int
  | ValVar String
  | ValLInj Value
  | ValRInj Value
  | ValPair Value Value
  | ValAnn Value BaseType
  -- | ValFold Value
  deriving (Eq, Ord, Show)

data Exp =
  ExpVal Value
  | ExpLet Pattern Exp Exp
  deriving (Eq, Ord, Show)

data Pattern =
  PtSingleVar String
  | PtMultiVar [String]
  deriving (Eq, Ord, Show)

data Iso =
  IsoValue [Value] [Exp]
  | IsoVar String
  | IsoLam String BaseType BaseType Iso
  | IsoApp Iso Iso
  | IsoFix String Iso
  | IsoAnn Iso IsoType
  deriving (Eq, Ord, Show)

data Term =
  TmUnit
  | TmInt Int
  | TmVar String
  | TmLInj Term
  | TmRInj Term
  | TmPair Term Term
  | TmIsoApp Iso Term
  | TmLet Pattern Term Term
  | TmAnn Term BaseType
  -- | TmFold Term
  deriving (Eq, Ord, Show)

data Program =
  PgTm Term
  | PgIs Iso
  deriving (Eq, Ord, Show)

-- Value
data ProgramBaseValue =
  PBValUnit
  | PBValInt Int
  | PBValVar String
  | PBValLeft ProgramBaseValue
  | PBValRight ProgramBaseValue
  | PBValPair ProgramBaseValue ProgramBaseValue
  -- | PBValFold ProgramBaseValue
  deriving (Eq, Ord, Show)

data ProgramIsoValue =
  PIValBase [(ProgramBaseValue , ProgramBaseValue)] ValEnv
  | PIValLam String Iso ValEnv
  | PIValFix String Iso ValEnv
  deriving (Eq, Ord, Show)

data ProgramValue =
  PB ProgramBaseValue
  | PI ProgramIsoValue
  deriving (Eq, Ord, Show)

-- Value Environment
type ValEnv = [(String , ProgramValue)]
type TypEnv = [(String , ProgramType)]
