module Translate (transToPerplPg, PProg) where

import Data.Foldable
import Data.String
import qualified Perpl.Struct.Lib as Perpl
import Syntax
import Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Debug.Trace (trace)

type TypeTable = Map.Map ProgramType Perpl.Type
type Types = Set.Set ProgramType
type Names = Set.Set String
type PProg = Perpl.UsProgs

moduleName :: String
moduleName = "Translate To PERPL: "

err :: String -> Result a
err = reportErr moduleName

ctorZero :: String
ctorZero = "zero"

ctorSuc :: String
ctorSuc = "suc"

dataNat :: String
dataNat = "Nat"

ctorCons :: String
ctorCons = "cons"

ctorNil :: String
ctorNil = "nil"

dataList :: String
dataList = "List"

unitUsTm :: Perpl.UsTm
unitUsTm = (Perpl.UsProd Perpl.Multiplicative [])
{-
Given a TYPE ANNOTATED ISO program, translate it into a user level PERPL
program.
-}
transToPerplPg :: (Definitions, Program) -> Result Perpl.UsProgs
transToPerplPg (defs, prgm) = do
  types <- collectTypes (defs, prgm)
  names <- collectNames (defs, prgm)
  table <- translateTypes types names
  usdata <- translateData table
  usdefs <- translateDefs table names defs
  usprgm <- translatePg table names prgm
  return $ Perpl.UsProgs (usdata ++ usdefs) usprgm

translatePg :: TypeTable -> Names -> Program -> Result Perpl.UsTm
translatePg table names (PgTm tm) = transTerm table names tm
translatePg table names (PgIs iso) = transIso table names iso

{-
Translate a term.
-}
transTerm :: TypeTable -> Names -> Term -> Result Perpl.UsTm
transTerm table names (TmAnn tm ty) = transTmWithTyp table names ty tm
transTerm _ _ tm = err $ "Cannot translate an untype-checked term: " ++ show tm

transTmWithTyp :: TypeTable -> Names -> BaseType -> Term -> Result Perpl.UsTm
transTmWithTyp _ _ _ TmUnit = return $ unitUsTm
transTmWithTyp _ _ _ (TmInt n) = return $ makeNat n where
  makeNat 0 = makeUsVar ctorZero
  makeNat n' = Perpl.UsApp (makeUsVar ctorSuc) (makeNat (n' - 1))
-- NOTE: even though this can be "correctly" translated into a perpl program,
-- perpl cannot process a value of this type yet!
transTmWithTyp table _ (BTyList ty) TmEmpty = do
  lTy <- lookupBase (BTyList ty) table
  -- "nil" is always the first constructor from an instantiated list type
  ctor <- extractCtor lTy 0
  return $ makeUsVar ctor
-- NOTE: even though this can be "correctly" translated into a perpl program,
-- perpl cannot process a value of this type yet!
transTmWithTyp table names (BTyList ty) (TmCons l r) = do
  lTy <- lookupBase (BTyList ty) table
  -- "cons" is always the first constructor from an instantiated list type
  ctor <- extractCtor lTy 1
  r' <- transTmWithTyp table names (BTyList ty) r
  l' <- transTmWithTyp table names ty l
  return $ Perpl.UsApp (Perpl.UsApp (makeUsVar ctor) l') r'
transTmWithTyp _ _ _ (TmVar var) = return $ makeUsVar var
transTmWithTyp table names (BTySum l r) (TmLInj tm) = do
  pTy <- lookupBase (BTySum l r) table
  ctor <- extractCtor pTy 0
  ustm <- transTmWithTyp table names l tm
  makeDataApp (makeUsVar ctor) ustm l
transTmWithTyp table names (BTySum l r) (TmRInj tm) = do
  pTy <- lookupBase (BTySum l r) table
  ctor <- extractCtor pTy 1
  ustm <- transTmWithTyp table names l tm
  makeDataApp (makeUsVar ctor) ustm r
transTmWithTyp table names (BTyProd lT rT) (TmPair l r) = do
  pTy <- lookupBase (BTyProd lT rT) table
  ctor <- extractCtor pTy 0
  ustmL <- transTmWithTyp table names lT l
  ustmR <- transTmWithTyp table names rT r
  let app = Perpl.UsApp (makeUsVar ctor) ustmL
  return $ Perpl.UsApp app ustmR
transTmWithTyp table names _ (TmIsoApp rator rand) = do
  usRator <- transIso table names rator
  usRand <- transTerm table names rand
  return $ Perpl.UsApp usRator usRand
transTmWithTyp table names ty (TmLet pat (TmAnn rhs ty') body) = do
  rhs' <- transTmWithTyp table names ty' rhs
  body' <- transTmWithTyp table names ty body
  makePatApp table ty' ty pat rhs' body'
transTmWithTyp _ _ _ (TmLet _ rhs _) = err $ "Cannot translate an untype-checked term: " ++ show rhs
transTmWithTyp table names _ (TmAnn tm ty) = transTmWithTyp table names ty tm
transTmWithTyp _ _ (BTyMu v b) tm = err $ "Unsupported term: " ++ show tm ++ " : " ++ show (BTyMu v b)
transTmWithTyp _ _ ty tm = err $ "Term and type mismatched: " ++ show tm ++ " :: " ++ show ty

makeUsVar :: String -> Perpl.UsTm
makeUsVar var = Perpl.UsVar $ fromString var

extractCtor :: Perpl.Type -> Int -> Result String
extractCtor (Perpl.TpData _ tags _) idx = return $ tagName (tags !! idx) where
  tagName (Perpl.Tag t) = t
extractCtor ty idx = err $ "Unable to extract the constructor at index " ++
  show idx ++ " from non-data type" ++ show ty

makeDataApp :: Perpl.UsTm -> Perpl.UsTm -> BaseType -> Result Perpl.UsTm
makeDataApp rator _ BTyUnit = return rator
makeDataApp rator rand _ = return $ Perpl.UsApp rator rand

-- Given a pattern, a rhs, and a body, translate it into some kind of
-- application.
makePatApp :: TypeTable -> BaseType -> BaseType -> Pattern -> Perpl.UsTm -> Perpl.UsTm -> Result Perpl.UsTm
-- this translates to: (\var : varTy -> body) rhs
makePatApp table varTy _ (PtSingleVar var) rhs body = do
  vTy' <- lookupBase varTy table
  let func = Perpl.UsLam (fromString var) vTy' body
  return $ Perpl.UsApp func rhs
-- this translates to: case rhs of c v1 ... in body
makePatApp table _ bodyTy (PtMultiVar vars) rhs body = do
  pTy <- lookupBase bodyTy table
  ctor <- extractCtor pTy 0
  let cas = Perpl.CaseUs (fromString ctor) (map fromString vars) body
  return $ Perpl.UsCase rhs [cas]

{-
Translate an iso.
-}
transIso :: TypeTable -> Names -> Iso -> Result Perpl.UsTm
transIso table names (IsoAnn iso ty) = transIsoWithTyp table names ty iso
transIso _ _ iso = err $ "Cannot translate an untype-checked iso: " ++ show iso

transIsoWithTyp :: TypeTable -> Names -> IsoType -> Iso -> Result Perpl.UsTm
transIsoWithTyp table names (ITyBase vTy eTy) (IsoValue pairs) = do
  let var = freshVar names (Set.size names)
  let names' = Set.insert var names
  vTy' <- lookupBase vTy table
  pairs' <- transPairsWithTyp table names' (vTy, eTy) pairs
  let env = toTypeEnv table
  let pvar = (var, vTy')
  let e = toMatch pvar pairs'
  case compileMatch env names' e of
    Left Redundancy -> err $ "Redundant patterns in " ++ show (IsoValue pairs)
    Left Missing -> err $ "Non-exhaustive patterns in " ++ show (IsoValue pairs)
    Left er -> err $ "Impossible case: " ++ show er
    Right body -> return $ Perpl.UsLam (fromString var) (simplifyType vTy') body
transIsoWithTyp _ _ _ (IsoVar var) = return $ makeUsVar var
transIsoWithTyp table names _ (IsoLam var lTy rTy body) = do
  lTy' <- lookupBase lTy table
  rTy' <- lookupBase rTy table
  let newTy = Perpl.TpArr lTy' rTy'
  body' <- transIso table names body
  return $ Perpl.UsLam (fromString var) (simplifyType newTy) body'
transIsoWithTyp table names _ (IsoFix var lTy rTy body) =
  err $ "TODO: Unimplemented yet: " ++ show (IsoFix var lTy rTy body)
transIsoWithTyp table names _ (IsoApp rator rand) = do
  usRator <- transIso table names rator
  usRand <- transIso table names rand
  return $ Perpl.UsApp usRator usRand
transIsoWithTyp table names _ (IsoAnn iso ty) = transIsoWithTyp table names ty iso
transIsoWithTyp _ _ ty iso = err $ "Iso and type mismatched: " ++ show iso ++ " :: " ++ show ty

transIsoTyp :: TypeTable -> Names -> Iso -> Result Perpl.Type
transIsoTyp table _ (IsoAnn _ ty) = lookupIso ty table
transIsoTyp _ _ iso = err $ "Unable to find the type of a untype-checked global iso: " ++ show iso

simplifyType :: Perpl.Type -> Perpl.Type
simplifyType (Perpl.TpArr t1 t2) = Perpl.TpArr (simplifyType t1) (simplifyType t2)
simplifyType (Perpl.TpData (Perpl.TpN tag) _ _) = Perpl.TpVar $ fromString tag
simplifyType (Perpl.TpProd a tys) = Perpl.TpProd a (map simplifyType tys)
simplifyType t = t

{-
Compile pattern matching
-}
type TypeEnv = Map.Map String Perpl.Type
-- | Pattern is one of the following three forms:
--   upattern ::= c upattern ...
--     |   x
--     |   ()
data UsPattern =
  UUnit
  | UCtor String [UsPattern]
  | UVar String
  deriving (Eq, Ord)
instance Show UsPattern where
  show UUnit = "()"
  show (UCtor tag args) = "(" ++ tag ++ " " ++ show args ++ ")"
  show (UVar v) = v

-- | One pattern variable: a string together with its type:
type PatVar = (String, Perpl.Type)

-- | Extended pattern is of the following form:
--   epattern ::= [v is uspattern]
-- so that we can write
--   a1 is pat1, a2 is pat2, ...
type ExtPattern = Map.Map PatVar UsPattern

-- | A clause is an extended pattern together with a right hand side.
type Clause = (ExtPattern, Perpl.UsTm)

-- | A match expression is a list of clauses.
type MatchExp = [Clause]

-- | Test if a clause's condition is wildcard, i.e., there is no pattern
-- variable inside the condition.
isWildcard :: Clause -> Bool
isWildcard (pats, _) = Map.size pats == 0

-- | Convert a user pattern to a term.
toUsTm :: UsPattern -> Perpl.UsTm
toUsTm UUnit = unitUsTm
toUsTm (UCtor tag pats) = foldl Perpl.UsApp (makeUsVar tag) (map toUsTm pats)
toUsTm (UVar var) = makeUsVar var

toMatch :: PatVar -> [(UsPattern, Perpl.UsTm)] -> MatchExp
toMatch v pats = map f pats where
  f (pat, tm) = (Map.fromList [(v , pat)], tm)

-- | Compile a list of (pattern, exp) into a list of conditions.
-- The algorithm here is based on the following paper:
--   How to compile pattern matching by Jules Jacobs
compileMatch :: TypeEnv -> Names -> MatchExp -> Either MatchKind Perpl.UsTm
compileMatch env names e =
  let se = simplifyMatch e in
    case matchKind env $ se of
      Valid var -> return $ matchToUsTm var se
      Reducible -> reduceMatch env names se
      er -> Left er

reduceMatch :: TypeEnv -> Names -> MatchExp -> Either MatchKind Perpl.UsTm
reduceMatch env names e = do
  let var = pickVar e
  let pats = genPats env names var  -- [(UsPattern, [PatVar])]
  let es = dispatchMatch var e pats -- [MatchExp]
  let newPats = map (\(p,_) -> Map.fromList [(var,p)]) pats
  let binds = map snd pats
  tms <- reduceMatches env names $ zip binds es
  return $ matchToUsTm var (zip newPats tms)

reduceMatches :: TypeEnv -> Names -> [([PatVar], MatchExp)] -> Either MatchKind [Perpl.UsTm]
-- reduceMatches env names es
--   | trace ("reduceMatches " ++ show env ++ " " ++ show names ++ " " ++ show es) False = undefined
reduceMatches env names es = mapM f es where
  f :: ([PatVar], MatchExp) -> Either MatchKind Perpl.UsTm
  f (binds, e) = compileMatch env (g binds) e

  g :: [PatVar] -> Names
  g pats = foldr h names pats

  h :: PatVar -> Names -> Names
  h (v, _) r = Set.insert v r

-- | Given a pattern variable, generate all of its constructor patterns, a list
-- of constructors, and a list of bound pattern variables.
genPats :: TypeEnv -> Names -> PatVar -> [(UsPattern, [PatVar])]
genPats _ _ (var, ty) | ty == freshProd [] = [(UVar var, [(var, ty)])]
genPats env names (_, ty) = zip upats pbinds where
  ctors = clCtors env ty
  tags = map fst ctors
  tyss = map snd ctors
  varss = map ((freshVars names) . length) tyss
  upats = map (\(tag, args) -> UCtor tag $ map UVar args) $ zip tags varss
  pbinds = map f $ zip varss tyss
  f (vars, tys) = zip vars tys

-- | Given a pattern variable being matched, a match expression, a constructor
-- pattern corresponding to the given variable, return a bound match expression.
-- In the returned bound match expression, every clause matches the given
-- constructor pattern.
dispatchMatch :: PatVar -> MatchExp -> [(UsPattern, [PatVar])] -> [MatchExp]
-- dispatchMatch var cls pats
--   | trace ("dispatchMatch " ++ show (fst var) ++ " " ++ show cls ++ " " ++ show pats) False = undefined
dispatchMatch var cls pats = map (dispatchMatches var cls) pats

dispatchMatches :: PatVar -> MatchExp -> (UsPattern, [PatVar]) -> MatchExp
dispatchMatches var cls (pat, binds) = foldr dispatchClause [] cls where
  -- Dispatch a clause. If the given clause doesn't use the variable being
  -- matched, then it should match. If the given clause uses the given variable
  -- but its constructor doesn't match the constructor of the given pattern,
  -- then it doesn't match. Otherwise it should match.
  dispatchClause :: Clause -> MatchExp -> MatchExp
  dispatchClause (test, rhs) r =
    if Map.member var test
    then compareClause (test, rhs) r
    else (test, rhs):r

  -- Compare a clause with the variable being matched. This only processes the
  -- case where the variable being matched shows up in the given clause.
  compareClause :: Clause -> MatchExp -> MatchExp
  compareClause (test, rhs) r =
    let pat' = test Map.! var
        urst = unifyPat (pat, binds) pat'
    in case urst of
         Just v -> (Map.union v $ Map.delete var test, rhs):r
         Nothing -> r

  unifyPat :: (UsPattern, [PatVar]) -> UsPattern -> Maybe ExtPattern
  unifyPat (UCtor tag _, bs) (UCtor tag' args')
    | tag == tag' = Just $ Map.fromList $ zip bs args'
    | otherwise = Nothing
  unifyPat (UVar _, [b]) (UVar v') = Just $ Map.fromList $ [(b, UVar v')]
  unifyPat (UVar _, [b]) UUnit = Just $ Map.fromList $ [(b, UUnit)]
  unifyPat (UVar _, [_]) _ = Nothing
  unifyPat _ _ = error $ "Impossible case!"

toTypeEnv :: TypeTable -> TypeEnv
toTypeEnv table = Map.foldr' h Map.empty table where
  h (Perpl.TpData (Perpl.TpN dat) ctors typs) r =
    Map.insert dat (Perpl.TpData (Perpl.TpN dat) ctors typs) r
  h _ r = r

data MatchKind =
  Valid PatVar
  | Reducible
  | Redundancy
  | Missing
  deriving (Eq, Ord, Show)

{-- Check the kind of a match expression. --}
-- | A match expression can be in three states:
--   1. Valid, which can be converted to a UsTm directly, this includes:
--      (1). a match has only one clause and its test is wildcard
--      (2). a match in the following form:
--           {match#
--             var is ctor1 var1 ... -> e1
--             var is ctor2 var1 ... -> e2
--             ...}
--   2. Reducible, which requires more processing.
--   3. Redundancy, more than one pattern has the wildcard test
--   4. Missing, no clause in the expression
matchKind :: TypeEnv -> MatchExp -> MatchKind
matchKind _ [] = Missing
matchKind _ [pat] | isWildcard pat = Valid ("", freshProd [])
matchKind _ pats | (List.length $ List.filter isWildcard pats) > 1 = Redundancy
matchKind env pats = case isValidMatch env pats of
  Just var -> Valid var
  Nothing -> Reducible

-- | Check if a match expression is valid.
isValidMatch :: TypeEnv -> MatchExp -> Maybe PatVar
isValidMatch env clauses =
  if isValid clauses && a == b
  then return var else Nothing where
  keys = Map.keys $ fst $ clauses !! 0
  var = keys !! 0

  a = Set.fromList $ fromPatVar var
  b = Set.fromList $ matchArity var clauses

  -- Check if a match expression is valid.
  isValid :: MatchExp -> Bool
  isValid [] = error $ "Impossible case: match expression has 0 clause!"
  isValid (cl:cls) = (Map.size $ fst cl) == 1 && all (isValidClause var) (cl:cls)

  -- Check if a clause is valid.
  isValidClause :: PatVar -> Clause -> Bool
  isValidClause v (pats,_) = isValidExtPat v pats

  -- Check if an extended pattern is valid.
  isValidExtPat :: PatVar -> ExtPattern -> Bool
  isValidExtPat v pats = (Map.size pats) == 1 &&
    Map.member v pats &&
    (isUsCtor $ pats Map.! v)

  -- Check if a user pattern is a constructor pattern with all its arguments
  -- variables.
  isUsCtor :: UsPattern -> Bool
  isUsCtor (UCtor _ args) = all isUsVar args
  isUsCtor _ = False

  -- Check if a user pattern is a variable pattern.
  isUsVar :: UsPattern -> Bool
  isUsVar (UVar _) = True
  isUsVar _ = False

  -- Collect all constructors and their arities from a match expression.
  matchArity :: PatVar -> MatchExp -> [(String, Int)]
  matchArity v cs = map (\clause -> clauseArity $ (fst clause) Map.! v) cs

  -- Collect the constructor and its arity from a pattern.  Invoke this only
  -- when you are sure that the pattern of UCtor!
  clauseArity :: UsPattern -> (String, Int)
  clauseArity (UCtor ctor args) = (ctor, length args)
  clauseArity _ = error "Impossible case!"

  fromPatVar :: PatVar -> [(String, Int)]
  fromPatVar (_, ty) = map (\(v, tys) -> (v, length tys)) $ clCtors env ty

{-- Variable picker. --}
-- | Pick the variable that is most used as the next target pattern variable.
pickVar :: MatchExp -> PatVar
pickVar e = fst $ maxVar $ Map.toList $ foldr g Map.empty e where
  g :: Clause -> Map.Map PatVar Int -> Map.Map PatVar Int
  g (pat, _) freq = Map.foldrWithKey' h freq pat

  h :: PatVar -> UsPattern -> Map.Map PatVar Int -> Map.Map PatVar Int
  h k _ r = if Map.member k r then Map.adjust (+1) k r else Map.insert k 0 r

  maxVar :: [(PatVar, Int)] -> (PatVar, Int)
  maxVar ints = maximumBy (\(_, n1) (_, n2) -> compare n1 n2) ints

{-- Convert match expressions to terms. --}
-- | Convert a valid match expression into a UsTm.
-- Two valid cases for a match is described in matchKind.
matchToUsTm :: PatVar -> MatchExp -> Perpl.UsTm
-- matchToUsTm pvar cl | trace ("matchToUsTm " ++ show pvar ++ " " ++ show cl) False = undefined
matchToUsTm _ [(pats, tm)] | Map.empty == pats = tm
matchToUsTm (var, ty) cls = Perpl.UsCase (makeUsVar var) cases where
  cases = map (clauseToCase (var, ty)) cls

clauseToCase :: PatVar -> Clause -> Perpl.CaseUs
-- clauseToCase pvar cl | trace ("clauseToCase " ++ show pvar ++ " " ++ show cl) False = undefined
clauseToCase pvar (pats, tm) = Perpl.CaseUs ctor args tm where
  (ctor, args) = toUsCase $ pats Map.! pvar

  -- | Convert a user pattern to a case component.
  toUsCase :: UsPattern -> (Perpl.TmName, [Perpl.TmVar])
  toUsCase (UCtor tag pats') = ((fromString tag), (map fromString vars)) where
    vars = map toString pats'
  toUsCase pat = error $ "Impossible case: not a valid constructor pattern: " ++ show pat

  -- | Convert a variable user pattern to a string.
  toString :: UsPattern -> String
  toString (UVar v) = v
  toString pat = error $ "Impossible case, not a valid variable pattern: " ++ show pat

{-- Simplify a match expression. --}
simplifyMatch :: MatchExp -> MatchExp
-- simplifyMatch es | trace ("simplifyMatch " ++ show es) False = undefined
simplifyMatch es = map simplifyClause es

simplifyClause :: Clause -> Clause
simplifyClause (pats, tm) = Map.foldrWithKey' f (Map.empty, tm) pats where
  f (v,_) (UVar v') (pats', tm') = (pats', Perpl.UsLet (fromString v') (makeUsVar v) tm')
  f (v,_) UUnit (pats', tm') = (pats', Perpl.UsLet (fromString v) unitUsTm tm')
  f (v,t) pat (pats', tm') = (Map.insert (v,t) pat pats', tm')

{-- Helper functions. --}
-- | Given a data Type, return a list of constructors and the expected number of
-- arguments corresponding to each constructor.
clCtors :: TypeEnv -> Perpl.Type -> [(String, [Perpl.Type])]
-- clCtors env ty | trace ("clCtors " ++ show env ++ " " ++ show ty) False = undefined
clCtors _ (Perpl.TpData _ ctors tys) = map f $ zip ctors tys where
  f (Perpl.Tag ctor, ty) = (ctor, typSize ty)

  typSize (Perpl.TpProd _ tys') = tys'
  typSize ty = [ty]
clCtors env (Perpl.TpVar (Perpl.TpV v)) = clCtors env (env Map.! v)
clCtors _ ty = error $ "Impossible case: " ++ show ty

freshVars :: Names -> Int -> [String]
freshVars _ 0 = []
freshVars names n = (freshVar names n):(freshVars names (n-1))

freshVar :: Names -> Int -> String
freshVar names n = if Set.member name names then Set.findMax names ++ name else name where
  name = "_var" ++ show n

{-
Translate a pair
-}
transPairsWithTyp :: TypeTable -> Names -> (BaseType, BaseType) -> [(Value, Exp)] ->
  Result [(UsPattern, Perpl.UsTm)]
transPairsWithTyp table names ty pairs = mapM (transPairWithTyp table names ty) pairs

transPairWithTyp :: TypeTable -> Names -> (BaseType, BaseType) -> (Value, Exp) ->
  Result (UsPattern, Perpl.UsTm)
transPairWithTyp table names (vTy, eTy) (v, e) = do
  v' <- compileValWithTyp table names vTy v
  e' <- transExpWithTyp table names eTy e
  return $ (v', e')

{-
Translate a value
-}
compileValWithTyp :: TypeTable -> Names -> BaseType -> Value -> Result UsPattern
compileValWithTyp _ _ _ ValUnit = return $ UUnit
compileValWithTyp _ _ _ (ValInt n) = return $ makeNat n where
  makeNat 0 = UCtor ctorZero []
  makeNat n' = UCtor ctorSuc [(makeNat (n' - 1))]
-- NOTE: even though this can be "correctly" translated into a perpl program,
-- perpl cannot process a value of this type yet!
compileValWithTyp table _ (BTyList ty) ValEmpty = do
  lTy <- lookupBase (BTyList ty) table
  -- "nil" is always the first constructor from an instantiated list type
  ctor <- extractCtor lTy 0
  return $ UCtor ctor []
-- NOTE: even though this can be "correctly" translated into a perpl program,
-- perpl cannot process a value of this type yet!
compileValWithTyp table names (BTyList ty) (ValCons l r) = do
  lTy <- lookupBase (BTyList ty) table
  -- "cons" is always the first constructor from an instantiated list type
  ctor <- extractCtor lTy 1
  r' <- compileValWithTyp table names (BTyList ty) r
  l' <- compileValWithTyp table names ty l
  return $ UCtor ctor [l', r']
compileValWithTyp _ _ BTyUnit (ValVar _) = return $ UUnit
compileValWithTyp _ _ _ (ValVar var) = return $ UVar var
compileValWithTyp table names (BTySum l r) (ValLInj val) = do
  pTy <- lookupBase (BTySum l r) table
  ctor <- extractCtor pTy 0
  ustm <- compileValWithTyp table names l val
  return $ makeDataApp' ctor ustm l
compileValWithTyp table names (BTySum l r) (ValRInj val) = do
  pTy <- lookupBase (BTySum l r) table
  ctor <- extractCtor pTy 1
  ustm <- compileValWithTyp table names r val
  return $ makeDataApp' ctor ustm r
compileValWithTyp table names (BTyProd lT rT) (ValPair l r) = do
  pTy <- lookupBase (BTyProd lT rT) table
  ctor <- extractCtor pTy 0
  ustmL <- compileValWithTyp table names lT l
  ustmR <- compileValWithTyp table names rT r
  return $ UCtor ctor [ustmL, ustmR]
compileValWithTyp table names _ (ValAnn val ty) = compileValWithTyp table names ty val
compileValWithTyp _ _ ty val = err $ "Value and type mismatch: " ++ show val ++ " :: " ++ show ty

makeDataApp' :: String -> UsPattern -> BaseType -> UsPattern
-- makeDataApp' rator pat ty
--   | trace ("makeDataApp' " ++ show rator ++ " " ++ show pat ++ " " ++ show ty) False = undefined
makeDataApp' rator _ BTyUnit = UCtor rator []
makeDataApp' rator rand _ = UCtor rator [rand]

{-
Translate a value.
-}
transValWithTyp :: TypeTable -> Names -> BaseType -> Value -> Result Perpl.UsTm
transValWithTyp table names ty val = toUsTm <$> compileValWithTyp table names ty val

{-
Translate an expression.
-}
transExpWithTyp :: TypeTable -> Names -> BaseType -> Exp -> Result Perpl.UsTm
transExpWithTyp table names ty (ExpVal val) = transValWithTyp table names ty val
transExpWithTyp table names ty (ExpScale scale e) = do
  e' <- transExpWithTyp table names ty e
  if imagPart scale == 0
    then return $ Perpl.UsFactor (realPart scale) e'
    else err $ "TODO: complex scale is not supported yet!"
transExpWithTyp table names ty (ExpPlus es) = do
  es' <- mapM (transExpWithTyp table names ty) es
  return $ Perpl.UsAmb es'
transExpWithTyp table names ty (ExpLet pat iso pat' body) = do
  isoTm <- transIso table names iso
  rhs <- mkRhs isoTm pat'
  body' <- transExpWithTyp table names ty body
  mkLet pat rhs body' where
    mkRhs tm (PtSingleVar v) = mkApp tm v
    mkRhs tm (PtMultiVar vs) = foldlM mkApp tm vs

    mkApp tm v = return $ Perpl.UsApp tm (makeUsVar v)

    mkLet (PtSingleVar v) rhs b = return $ Perpl.UsLet (fromString v) rhs b
    mkLet (PtMultiVar vs) rhs b = return $ Perpl.UsElimMultiplicative rhs (map fromString vs) b

{-
Translate an algebraic data definition.
-}
translateData :: TypeTable -> Result [Perpl.UsProg]
translateData table = foldrM f [] table where
  f (Perpl.TpData name tags tys) r = do
    ctors <- makeCtors tags tys
    usdata <- makeUsData name ctors
    return $ usdata:r
  f _ r = return r

  makeUsData :: Perpl.TpName -> [Perpl.Ctor] -> Result Perpl.UsProg
  makeUsData name ctors = return $ Perpl.UsProgData name [] ctors

  makeCtors :: [Perpl.Tag] -> [Perpl.Type] -> Result [Perpl.Ctor]
  makeCtors tags tys = foldrM makeCtorsWithPair [] $ zip tags tys

  makeCtorsWithPair :: (Perpl.Tag, Perpl.Type) -> [Perpl.Ctor] -> Result [Perpl.Ctor]
  makeCtorsWithPair (tag,ty) r = do
    ctor <- makeCtor tag ty
    return $ ctor:r

  -- for each type in typs, if it is a data, extract the name as a new var,
  -- otherwise keep it as it is.
  makeCtor :: Perpl.Tag -> Perpl.Type -> Result Perpl.Ctor
  makeCtor (Perpl.Tag tag) (Perpl.TpProd _ tys) = return $ Perpl.Ctor (fromString tag) $ map purgeType tys
  makeCtor (Perpl.Tag tag) ty = return $ Perpl.Ctor (fromString tag) [purgeType ty]

  purgeType :: Perpl.Type -> Perpl.Type
  purgeType (Perpl.TpData (Perpl.TpN name) _ _) = Perpl.TpVar $ fromString name
  purgeType ty = ty

translateDefs :: TypeTable -> Names -> Definitions -> Result [Perpl.UsProg]
translateDefs table names defs = foldrM f [] defs where
  f (str, iso) r = do
    isoTm <- transIso table names iso
    isoTy <- transIsoTyp table names iso
    let isoNm = fromString str
    return $ (Perpl.UsProgDefine isoNm isoTm $ simplifyType isoTy):r

{-
Collect all types into a set (type variables are not considered yet)
-}
collectTypes :: (Definitions, Program) -> Result Types
collectTypes (defs, prgm) = do
  dfTys <- clTypDefs defs
  pgTys <- clTypPg prgm
  return $ Set.union dfTys pgTys

clTypDefs :: Definitions -> Result Types
clTypDefs defs = foldlM clTypDef Set.empty defs where
  clTypDef rst (_, iso) = do
    isoTys <- clTypIso iso
    return $ Set.union rst isoTys

clTypPg :: Program -> Result Types
clTypPg (PgTm tm) = clTypTm tm
clTypPg (PgIs iso) = clTypIso iso

clTypIso :: Iso -> Result Types
clTypIso (IsoValue pairs) = foldlM clIsoPair Set.empty pairs where
  clIsoPair rst (v, e) = do
    vTyp <- clTypValue v
    eTyp <- clTypExp e
    return $ Set.union vTyp $ Set.union eTyp rst
clTypIso (IsoVar _) = return Set.empty
clTypIso (IsoLam _ lTy rTy iso) = do
  tys <- clTypIso iso
  return $ Set.insert (Left lTy) $ Set.insert (Left rTy) tys
clTypIso (IsoApp rator rand) = do
  ratorTys <- clTypIso rator
  randTys <- clTypIso rand
  return $ Set.union ratorTys randTys
clTypIso (IsoFix _ lTy rTy iso) = do
  tys <- clTypIso iso
  return $ Set.insert (Left lTy) $ Set.insert (Left rTy) tys
clTypIso (IsoAnn iso ty) = do
  tys <- clTypIso iso
  return $ Set.insert (Right ty) tys

clTypValue :: Value -> Result Types
clTypValue ValUnit = return Set.empty
clTypValue (ValInt _) = return Set.empty
clTypValue (ValVar _) = return Set.empty
clTypValue ValEmpty = return Set.empty
clTypValue (ValCons l r) = do
  lTy <- clTypValue l
  rTy <- clTypValue r
  return $ Set.union lTy rTy
clTypValue (ValLInj v) = clTypValue v
clTypValue (ValRInj v) = clTypValue v
clTypValue (ValPair l r) = do
  lTy <- clTypValue l
  rTy <- clTypValue r
  return $ Set.union lTy rTy
clTypValue (ValAnn v ty) = do
  tys <- clTypValue v
  return $ Set.insert (Left ty) tys

clTypExp :: Exp -> Result Types
clTypExp (ExpVal v) = clTypValue v
clTypExp (ExpLet _ iso _ e) = do
  isoTys <- clTypIso iso
  eTys <- clTypExp e
  return $ Set.union isoTys eTys
clTypExp (ExpScale _ e) = clTypExp e
clTypExp (ExpPlus es) = foldlM clTypE Set.empty es where
  clTypE rst e = do
    eTys <- clTypExp e
    return $ Set.union rst eTys

clTypTm :: Term -> Result Types
clTypTm TmUnit = return Set.empty
clTypTm (TmInt _) = return Set.empty
clTypTm TmEmpty = return Set.empty
clTypTm (TmCons l r) = do
  lTys <- clTypTm l
  rTys <- clTypTm r
  return $ Set.union lTys rTys
clTypTm (TmVar _) = return Set.empty
clTypTm (TmLInj tm) = clTypTm tm
clTypTm (TmRInj tm) = clTypTm tm
clTypTm (TmPair l r) = do
  lTys <- clTypTm l
  rTys <- clTypTm r
  return $ Set.union lTys rTys
clTypTm (TmIsoApp iso tm) = do
  isoTys <- clTypIso iso
  tmTys <- clTypTm tm
  return $ Set.union isoTys tmTys
clTypTm (TmLet _ rhs body) = do
  rhsTys <- clTypTm rhs
  bodyTys <- clTypTm body
  return $ Set.union rhsTys bodyTys
clTypTm (TmAnn tm ty) = do
  tys <- clTypTm tm
  return $ Set.insert (Left ty) tys

{-
Collect all names into a set
-}
collectNames :: (Definitions, Program) -> Result Names
collectNames (defs, prgm) = do
  dfNms <- clNmDefs defs
  pgNms <- clNmPg prgm
  return $ Set.union dfNms pgNms

clNmDefs :: Definitions -> Result Names
clNmDefs defs = foldlM clNmDef Set.empty defs where
  clNmDef rst (nm, iso) = do
    isoTys <- clNmIso iso
    return $ Set.insert nm $ Set.union rst isoTys

clNmPg :: Program -> Result Names
clNmPg (PgTm tm) = clNmTm tm
clNmPg (PgIs iso) = clNmIso iso

clNmIso :: Iso -> Result Names
clNmIso (IsoValue pairs) = foldlM clIsoPair Set.empty pairs where
  clIsoPair rst (v, e) = do
    vNm <- clNmValue v
    eNm <- clNmExp e
    return $ Set.union vNm $ Set.union eNm rst
clNmIso (IsoVar _) = return $ Set.empty
clNmIso (IsoLam v _ _ iso) = do
  nms <- clNmIso iso
  return $ Set.insert v nms
clNmIso (IsoApp rator rand) = do
  ratorNms <- clNmIso rator
  randNms <- clNmIso rand
  return $ Set.union ratorNms randNms
clNmIso (IsoFix v _ _ iso) = do
  nms <- clNmIso iso
  return $ Set.insert v nms
clNmIso (IsoAnn iso _) = clNmIso iso

clNmValue :: Value -> Result Names
clNmValue ValUnit = return Set.empty
clNmValue (ValInt _) = return Set.empty
clNmValue (ValVar v) = return $ Set.singleton v
clNmValue ValEmpty = return Set.empty
clNmValue (ValCons l r) = do
  lTy <- clNmValue l
  rTy <- clNmValue r
  return $ Set.union lTy rTy
clNmValue (ValLInj v) = clNmValue v
clNmValue (ValRInj v) = clNmValue v
clNmValue (ValPair l r) = do
  lTy <- clNmValue l
  rTy <- clNmValue r
  return $ Set.union lTy rTy
clNmValue (ValAnn v _) = clNmValue v

clNmExp :: Exp -> Result Names
clNmExp (ExpVal v) = clNmValue v
clNmExp (ExpLet pat iso pat' e) = do
  patNms <- clNmPat pat
  isoNms <- clNmIso iso
  patNms' <- clNmPat pat'
  eNms <- clNmExp e
  return $ foldl Set.union patNms [isoNms, patNms', eNms]
clNmExp (ExpScale _ e) = clNmExp e
clNmExp (ExpPlus es) = foldlM clNmE Set.empty es where
  clNmE rst e = do
    eNms <- clNmExp e
    return $ Set.union rst eNms

clNmPat :: Pattern -> Result Names
clNmPat (PtSingleVar v) = return $ Set.singleton v
clNmPat (PtMultiVar vs) = return $ Set.fromList vs

clNmTm :: Term -> Result Names
clNmTm TmUnit = return Set.empty
clNmTm (TmInt _) = return Set.empty
clNmTm TmEmpty = return Set.empty
clNmTm (TmCons l r) = do
  lNms <- clNmTm l
  rNms <- clNmTm r
  return $ Set.union lNms rNms
clNmTm (TmVar _) = return Set.empty
clNmTm (TmLInj tm) = clNmTm tm
clNmTm (TmRInj tm) = clNmTm tm
clNmTm (TmPair l r) = do
  lNms <- clNmTm l
  rNms <- clNmTm r
  return $ Set.union lNms rNms
clNmTm (TmIsoApp iso tm) = do
  isoNms <- clNmIso iso
  tmNms <- clNmTm tm
  return $ Set.union isoNms tmNms
clNmTm (TmLet pat rhs body) = do
  patNms <- clNmPat pat
  rhsNms <- clNmTm rhs
  bodyNms <- clNmTm body
  return $ Set.union patNms $ Set.union rhsNms bodyNms
clNmTm (TmAnn tm _) = clNmTm tm

{-
Translate a set of types to algebraic types if necessary.
-}
translateTypes :: Types -> Names -> Result TypeTable
translateTypes tys names = foldlM f Map.empty tys where
  f table t = translateType table names t

translateType :: TypeTable -> Names -> ProgramType -> Result TypeTable
translateType table names (Left bTy) = transBaseType table names bTy
translateType table names (Right iTy) = transIsoType table names iTy

transBaseType :: TypeTable -> Names -> BaseType -> Result TypeTable
transBaseType table names ty = case Map.lookup (Left ty) table of
  Just _ -> return table
  Nothing -> transBaseType' table names ty

transBaseType' :: TypeTable -> Names -> BaseType -> Result TypeTable
transBaseType' table _ BTyUnit = return $ insertBase BTyUnit (freshProd []) table
transBaseType' table _ BTyInt = return $ insertBase BTyInt (freshData d ctors tys) table where
  d = dataNat
  ctors = [ctorZero, ctorSuc]
  zTyp = freshProd []
  sTyp = Perpl.TpVar $ fromString d
  tys = [zTyp, sTyp]
transBaseType' table names (BTyList ty) = do
  table' <- transBaseType table names ty
  ty' <- lookupBase ty table'
  let dVar = freshDataName table' names
  let d = dataList ++ dVar
  let ctors = [ctorNil ++ d, ctorCons ++ d]
  let nilTyp = freshProd []
  let consTyp = freshProd [ty', Perpl.TpVar $ fromString d]
  return $ insertBase (BTyList ty) (freshData d ctors [nilTyp, consTyp]) table
transBaseType' _ _ (BTyVar var) = err $ moduleName ++ "Unsupported type: " ++ (show (BTyVar var))
transBaseType' table names (BTySum l r) = do
  table' <- transBaseType table names l
  table'' <- transBaseType table' names r
  tl <- lookupBase l table''
  tr <- lookupBase r table''
  let datName = freshDataName table'' names
  let ctr1Name = freshCtorName names datName 0
  let ctr2Name = freshCtorName names datName 1
  let dat = freshData datName [ctr1Name, ctr2Name] [tl, tr]
  return $ insertBase (BTySum l r) dat table''
transBaseType' table names (BTyProd l r) = do
  table' <- transBaseType table names l
  table'' <- transBaseType table' names r
  tl <- lookupBase l table''
  tr <- lookupBase r table''
  let datName = freshDataName table'' names
  let ctr1Name = freshCtorName names datName 0
  let prod = freshProd [tl, tr]
  let dat = freshData datName [ctr1Name] [prod]
  return $ insertBase (BTyProd l r) dat table''
transBaseType' _ _ (BTyMu v b) = err $ moduleName ++ "Unsupported type: " ++ (show (BTyMu v b))

transIsoType :: TypeTable -> Names -> IsoType -> Result TypeTable
transIsoType table names ty =  case Map.lookup (Right ty) table of
  Just _ -> return table
  Nothing -> transIsoType' table names ty

transIsoType' :: TypeTable -> Names -> IsoType -> Result TypeTable
transIsoType' table names (ITyBase l r) = do
  table' <- transBaseType table names l
  table'' <- transBaseType table' names r
  tl <- lookupBase l table''
  tr <- lookupBase r table''
  return $ insertIso (ITyBase l r) (Perpl.TpArr tl tr) table''
transIsoType' table names (ITyFun l r body) = do
  table' <- transBaseType table names l
  table'' <- transBaseType table' names r
  table''' <- transIsoType table'' names body
  tl <- lookupBase l table'''
  tr <- lookupBase r table'''
  tb <- lookupIso body table'''
  return $ insertIso (ITyFun l r body) (Perpl.TpArr (Perpl.TpArr tl tr) tb) table'''

freshDataName :: TypeTable -> Names -> String
freshDataName table names = if Set.member n names then n ++ Set.findMax names else n where
  n = "DTy" ++ (show $ Map.size table)

freshCtorName :: Names -> String -> Int -> String
freshCtorName names name i = if Set.member n names then n ++ Set.findMax names else n where
  n = "ctr" ++ name ++ show i

freshData :: String -> [String] -> [Perpl.Type] -> Perpl.Type
freshData name tags tys = Perpl.TpData pname ptags tys where
  pname = fromString name
  ptags = map fromString tags

freshProd :: [Perpl.Type] -> Perpl.Type
freshProd tys = Perpl.TpProd Perpl.Multiplicative tys

lookupBase :: BaseType -> TypeTable -> Result Perpl.Type
lookupBase ty table = case Map.lookup (Left ty) table of
  Just r -> return r
  Nothing -> err $ "Unable to find the translated base type " ++ show ty ++ " in the type table"

lookupIso :: IsoType -> TypeTable -> Result Perpl.Type
lookupIso ty table = case Map.lookup (Right ty) table of
  Just r -> return r
  Nothing -> err $ moduleName ++ "Unable to find the translated iso type " ++ show ty ++ " in the type table"

insertBase :: BaseType -> Perpl.Type -> TypeTable -> TypeTable
insertBase k v table = Map.insert (Left k) v table

insertIso :: IsoType -> Perpl.Type -> TypeTable -> TypeTable
insertIso k v table = Map.insert (Right k) v table
