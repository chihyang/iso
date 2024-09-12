module PatternMatch (compileMatch, MatchKind(..), UsPattern(..), TypeEnv) where

import Data.Foldable
import Data.String
import qualified Perpl.Struct.Lib as Perpl
import Syntax
import Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Debug.Trace (trace)

type TypeTable = Map.Map ProgramType Perpl.Type
type Names = Set.Set String

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

data MatchKind =
  Valid PatVar
  | Reducible
  | Redundancy
  | Missing
  deriving (Eq, Ord, Show)

unitUsTm :: Perpl.UsTm
unitUsTm = Perpl.UsProd Perpl.Multiplicative []

makeUsVar :: String -> Perpl.UsTm
makeUsVar var = Perpl.UsVar $ fromString var

freshProd :: [Perpl.Type] -> Perpl.Type
freshProd = Perpl.TpProd Perpl.Multiplicative

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
toMatch v = map f where
  f (pat, tm) = (Map.fromList [(v , pat)], tm)

-- | Compile a list of (pattern, exp) into a list of conditions.
-- The algorithm here is based on the following paper:
--   How to compile pattern matching by Jules Jacobs
compileMatch :: TypeEnv -> Names -> MatchExp -> Either MatchKind Perpl.UsTm
compileMatch env names e =
  let se = simplifyMatch e in
    case matchKind env se of
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
reduceMatches env names = mapM f where
  f :: ([PatVar], MatchExp) -> Either MatchKind Perpl.UsTm
  f (binds, e) = compileMatch env (g binds) e

  g :: [PatVar] -> Names
  g = foldr h names

  h :: PatVar -> Names -> Names
  h (v, _) = Set.insert v

-- | Given a pattern variable, generate all of its constructor patterns, a list
-- of constructors, and a list of bound pattern variables.
genPats :: TypeEnv -> Names -> PatVar -> [(UsPattern, [PatVar])]
genPats _ _ (var, ty) | ty == freshProd [] = [(UVar var, [(var, ty)])]
genPats env names (_, ty) = zip upats pbinds where
  ctors = clCtors env ty
  tags = map fst ctors
  tyss = map snd ctors
  varss = map (freshVars names . length) tyss
  upats = zipWith (\tag args -> UCtor tag $ map UVar args) tags varss
  pbinds = zipWith zip varss tyss

-- | Given a pattern variable being matched, a match expression, a constructor
-- pattern corresponding to the given variable, return a bound match expression.
-- In the returned bound match expression, every clause matches the given
-- constructor pattern.
dispatchMatch :: PatVar -> MatchExp -> [(UsPattern, [PatVar])] -> [MatchExp]
-- dispatchMatch var cls pats
--   | trace ("dispatchMatch " ++ show (fst var) ++ " " ++ show cls ++ " " ++ show pats) False = undefined
dispatchMatch var cls = map (dispatchMatches var cls)

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
  unifyPat (UVar _, [b]) (UVar v') = Just $ Map.fromList [(b, UVar v')]
  unifyPat (UVar _, [b]) UUnit = Just $ Map.fromList [(b, UUnit)]
  unifyPat (UVar _, [_]) _ = Nothing
  unifyPat _ _ = error "Impossible case!"

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
matchKind _ pats | List.length (List.filter isWildcard pats) > 1 = Redundancy
matchKind env pats = maybe Reducible Valid (isValidMatch env pats)

-- | Check if a match expression is valid.
isValidMatch :: TypeEnv -> MatchExp -> Maybe PatVar
isValidMatch env clauses =
  if isValid clauses && a == b
  then return var else Nothing where
  keys = Map.keys $ fst $ head clauses
  var = head keys

  a = Set.fromList $ fromPatVar var
  b = Set.fromList $ matchArity var clauses

  -- Check if a match expression is valid.
  isValid :: MatchExp -> Bool
  isValid [] = error "Impossible case: match expression has 0 clause!"
  isValid (cl:cls) = Map.size (fst cl) == 1 && all (isValidClause var) (cl:cls)

  -- Check if a clause is valid.
  isValidClause :: PatVar -> Clause -> Bool
  isValidClause v (pats,_) = isValidExtPat v pats

  -- Check if an extended pattern is valid.
  isValidExtPat :: PatVar -> ExtPattern -> Bool
  isValidExtPat v pats = Map.size pats == 1 &&
    Map.member v pats && isUsCtor (pats Map.! v)

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
  matchArity v = map (\clause -> clauseArity $ fst clause Map.! v)

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
  maxVar = maximumBy (\(_, n1) (_, n2) -> compare n1 n2)

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
  toUsCase (UCtor tag pats') = (fromString tag, map fromString vars) where
    vars = map toString pats'
  toUsCase pat = error $ "Impossible case: not a valid constructor pattern: " ++ show pat

  -- | Convert a variable user pattern to a string.
  toString :: UsPattern -> String
  toString (UVar v) = v
  toString pat = error $ "Impossible case, not a valid variable pattern: " ++ show pat

{-- Simplify a match expression. --}
simplifyMatch :: MatchExp -> MatchExp
-- simplifyMatch es | trace ("simplifyMatch " ++ show es) False = undefined
simplifyMatch = map simplifyClause

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
clCtors _ (Perpl.TpData _ ctors tys) = zipWith f ctors tys where
  f (Perpl.Tag ctor) ty = (ctor, typSize ty)

  typSize (Perpl.TpProd _ tys') = tys'
  typSize ty = [ty]
clCtors env (Perpl.TpVar (Perpl.TpV v)) = clCtors env (env Map.! v)
clCtors _ ty = error $ "Impossible case: " ++ show ty

freshVars :: Names -> Int -> [String]
freshVars _ 0 = []
freshVars names n = freshVar names n:freshVars names (n-1)

freshVar :: Names -> Int -> String
freshVar names n = if Set.member name names then Set.findMax names ++ name else name where
  name = "_var" ++ show n
