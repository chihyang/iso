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
  show BTyInt = "Int"
  show (BTyVar var) = show var
  show (BTySum lt rt) = "(" ++ show lt ++ " + " ++ show rt ++ ")"
  show (BTyProd lt rt) = "(" ++ show lt ++ " × " ++ show rt ++ ")"
  show (BTyMu var bodyT) = "Mu " ++ show var ++ ". " ++ show bodyT

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
  deriving (Eq, Ord)
instance Show Value where
  show ValUnit = "unit"
  show (ValInt n) = show n
  show (ValVar var) = show var
  show (ValLInj v) = "left " ++ show v
  show (ValRInj v) = "right " ++ show v
  show (ValPair l r) = "(" ++ show l ++ ", " ++ show r ++ ")"
  show (ValAnn v t) = "(" ++ show v ++ " :: " ++ show t ++ ")"

data Exp =
  ExpVal Value
  | ExpLet Pattern Iso Pattern Exp
  deriving (Eq, Ord)
instance Show Exp where
  show (ExpVal v) = show v
  show (ExpLet pat iso pat' body) =
    "let " ++ show pat ++ " = " ++ show iso ++ " " ++ show pat' ++ " in " ++ show body

data Pattern =
  PtSingleVar String
  | PtMultiVar [String]
  deriving (Eq, Ord)
instance Show Pattern where
  show (PtSingleVar var) = show var
  show (PtMultiVar vars) = show vars

data Iso =
  IsoValue [(Value, Exp)]
  | IsoVar String
  | IsoLam String BaseType BaseType Iso
  | IsoApp Iso Iso
  | IsoFix String Iso
  | IsoAnn Iso IsoType
  deriving (Eq, Ord)
instance Show Iso where
  show (IsoValue clauses) =
    "{\n" ++
    (foldl (++) ""
      $ map (\p -> ((show $ fst p) ++ " <-> " ++ (show $ snd p) ++ ";\n")) clauses)
    ++ "}"
  show (IsoVar var) = show var
  show (IsoLam var lhs rhs body) =
    "\\" ++
    show var ++ " :: (" ++ show lhs ++ " <-> " ++ show rhs ++ ")" ++
    "\n  -> " ++ show body
  show (IsoApp rator rand) = "(" ++ show rator ++ "\n " ++ show rand ++ ")"
  show (IsoFix var iso) = "fix " ++ show var ++ ". " ++ show iso
  show (IsoAnn iso ty) = "(" ++ show iso ++ " :: " ++ show ty ++ ")"

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
  deriving (Eq, Ord)
instance Show Term where
  show TmUnit = "unit"
  show (TmInt n) = show n
  show (TmVar var) = show var
  show (TmLInj v) = "left " ++ show v
  show (TmRInj v) = "right " ++ show v
  show (TmPair l r) = "(" ++ show l ++ ", " ++ show r ++ ")"
  show (TmIsoApp iso tm) = "(" ++ show iso ++ "\n " ++ show tm ++ ")"
  show (TmLet pat rhs body) =
    "let " ++ show pat ++ " = " ++ show rhs ++ "\nin " ++ show body
  show (TmAnn v t) = "(" ++ show v ++ " :: " ++ show t ++ ")"

data Program =
  PgTm Term
  | PgIs Iso
  deriving (Eq, Ord)
instance Show Program where
  show (PgTm tm) = show tm
  show (PgIs iso) = show iso

-- Value
data ProgramBaseValue =
  PBValUnit
  | PBValInt Int
  | PBValVar String
  | PBValLeft ProgramBaseValue
  | PBValRight ProgramBaseValue
  | PBValPair ProgramBaseValue ProgramBaseValue
  -- | PBValFold ProgramBaseValue
  deriving (Eq, Ord)
instance Show ProgramBaseValue where
  show PBValUnit = "unit"
  show (PBValInt n) = show n
  show (PBValVar var) = show var
  show (PBValLeft v) = "left " ++ show v
  show (PBValRight v) = "right " ++ show v
  show (PBValPair l r) = "(" ++ show l ++ ", " ++ show r ++ ")"

data ProgramIsoValue =
  PIValBase [(ProgramBaseValue , ProgramBaseValue)] ValEnv
  | PIValLam String Iso ValEnv
  | PIValFix String Iso ValEnv
  deriving (Eq, Ord)
instance Show ProgramIsoValue where
  show (PIValBase pairs _) =
    "{\n" ++
    (foldl (++) ""
      $ map (\p -> ((show $ fst p) ++ " <-> " ++ (show $ snd p) ++ ",\n")) pairs)
    ++ "}"
  show (PIValLam var iso _) = "\\" ++ show var ++ " -> " ++ show iso
  show (PIValFix var iso _) = "mu." ++ show var ++ " -> " ++ show iso

data ProgramValue =
  PB ProgramBaseValue
  | PI ProgramIsoValue
  deriving (Eq, Ord)
instance Show ProgramValue where
  show (PB v) = show v
  show (PI i) = show i

-- Value Environment
type ValEnv = [(String , ProgramValue)]
type TypEnv = [(String , ProgramType)]
