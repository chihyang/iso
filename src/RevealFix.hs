module RevealFix (revealFix, toList, toListFix, lookupFix, lookupFixVar, FvsSet, FixMap) where

import Syntax
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Debug.Trace (trace)

moduleName :: String
moduleName = "RevealFix: "

-- Maps from argument to the set of free variables
type FvsSet = (Set.Set String, Map.Map String IsoType)
type FixMap = (Map.Map String Iso, Map.Map Iso FvsSet)

-- Operations on free variable set.
empty :: FvsSet
empty = (Set.empty, Map.empty)

singleton :: (String, IsoType) -> FvsSet
singleton (var,ty) = (Set.singleton var, Map.singleton var ty)

insert :: (String, IsoType) -> FvsSet -> FvsSet
insert (v,t) (s,m) = (Set.insert v s, Map.insert v t m)

member :: String -> FvsSet -> Bool
member v (s,_) = Set.member v s

delete :: String -> FvsSet -> FvsSet
delete v (s,m) = (Set.delete v s, Map.delete v m)

union :: FvsSet -> FvsSet -> FvsSet
union (s1,m1) (s2,m2) = (s1 `Set.union` s2, m1 `Map.union` m2)

toList :: FvsSet -> [(String, IsoType)]
toList (_,m) = foldr f [] (Map.toList m) where
  f (name,ty) r = (name,ty):r

-- | Remove every string in vs from s
difference :: FvsSet -> Set.Set String -> FvsSet
difference = Set.foldr' f where
  f v r = if v `member` r then delete v r else r

infixl 9 \\

(\\) :: FvsSet -> Set.Set String -> FvsSet
fvs1 \\ vars = difference fvs1 vars

emptyFix :: FixMap
emptyFix = (Map.empty, Map.empty)

insertFix :: String -> Iso -> FvsSet -> FixMap -> FixMap
insertFix v i s (m1, m2) = (Map.insert v i m1, Map.insert i s m2)

toListFix :: FixMap -> [(Iso, FvsSet)]
toListFix (_, m2) = Map.toList m2

lookupFix :: Iso -> FixMap -> Maybe FvsSet
lookupFix iso (_,m2) = Map.lookup iso m2

lookupFixVar :: String -> FixMap -> Maybe (Iso, FvsSet)
lookupFixVar s m@(m1,_) = case Map.lookup s m1 of
  Just i -> (\fvs -> (i,fvs)) <$> lookupFix i m
  Nothing -> Nothing

-- | This module tries to find all locally defined recursive iso.  It must come
-- after uniquify because we use the argument of fix as the key.  No two keys
-- should be the same.
revealFix :: (Definitions, Program) -> Result FixMap
revealFix (defs, prgm) = return fvsets where
  fvsets = foldr (\i@(IsoAnn (IsoFix v _ _ _) _) r -> insertFix v i (fvsIso i \\ globalNames) r) emptyFix fixIso
  fixIso = concatMap cfDef defs ++ cfProg prgm
  globalNames = Set.fromList $ map fst defs

{-- Collect all fix iso --}
-- | Collect all IsoFix from a definition.
cfDef :: Definition -> [Iso]
cfDef (_, iso) = cfIso iso

-- | Collect all IsoFix from a program.
cfProg :: Program -> [Iso]
cfProg (PgTm tm) = cfTm tm
cfProg (PgIs iso) = cfIso iso

-- | Collect all IsoFix from an iso.
cfIso :: Iso -> [Iso]
cfIso (IsoValue pairs) = concatMap (cfExp . snd) pairs
cfIso (IsoVar _) = []
cfIso (IsoLam _ _ _ body) = cfIso body
cfIso (IsoApp l r) = cfIso l ++ cfIso r
cfIso f@(IsoAnn (IsoFix _ _ _ body) _) = f:cfIso body
cfIso f@(IsoFix {}) = error $ "Impossible case: every variable should be type annoated, given " ++ show f
cfIso (IsoAnn iso _) = cfIso iso

-- | Collect all IsoFix from an exp.
cfExp :: Exp -> [Iso]
cfExp (ExpVal _) = []
cfExp (ExpLet _ iso _ body) = cfIso iso ++ cfExp body
cfExp (ExpScale _ e) = cfExp e
cfExp (ExpPlus es) = concatMap cfExp es

-- | Collect all IsoFix from an term.
cfTm :: Term -> [Iso]
cfTm TmUnit = []
cfTm (TmInt _) = []
cfTm TmEmpty = []
cfTm (TmCons l r) = cfTm l ++ cfTm r
cfTm (TmVar _) = []
cfTm (TmLInj tm) = cfTm tm
cfTm (TmRInj tm) = cfTm tm
cfTm (TmPair l r) = cfTm l ++ cfTm r
cfTm (TmIsoApp iso tm) = cfIso iso ++ cfTm tm
cfTm (TmLet _ rhs body) = cfTm rhs ++ cfTm body
cfTm (TmAnn tm _) = cfTm tm

{-- Collect free variables --}
-- | Collect all iso free variables in an iso.
fvsIso :: Iso -> FvsSet
fvsIso (IsoValue pairs) = foldr (union . fvsExp . snd) empty pairs
fvsIso (IsoAnn (IsoVar var) ty) = singleton (var, ty)
fvsIso (IsoVar var) = error $ moduleName ++ "Impossible case: every variable should be type annoated, given " ++ var
fvsIso (IsoLam var _ _ body) = fvsIso body \\ Set.singleton var
fvsIso (IsoApp l r) = fvsIso l `union` fvsIso r
fvsIso (IsoFix var _ _ body) = fvsIso body \\ Set.singleton var
fvsIso (IsoAnn iso _) = fvsIso iso

-- | Collect all iso free variables in an expression.
fvsExp :: Exp -> FvsSet
fvsExp (ExpVal _) = empty
fvsExp (ExpLet _ iso _ body) = fvsIso iso `union` fvsExp body
fvsExp (ExpScale _ e) = fvsExp e
fvsExp (ExpPlus es) = foldr (union . fvsExp) empty es
