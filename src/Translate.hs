module Translate (transToPerplPg, PProg) where

import Data.Foldable
import Data.String
import qualified Perpl.Struct.Lib as Perpl
import PatternMatch
import Syntax
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Debug.Trace (trace)

type TypeTable = Map.Map ProgramType Perpl.Type
type Types = Set.Set ProgramType
type Names = Set.Set String
type PProg = Perpl.UsProgs
type Info = (TypeTable, Names)

lookupBaseInfo :: BaseType -> Info -> Result Perpl.Type
lookupBaseInfo ty (table,_) = lookupBase ty table

lookupIsoInfo :: IsoType -> Info -> Result Perpl.Type
lookupIsoInfo ty (table,_) = lookupIso ty table

getNames :: Info -> Names
getNames (_,names) = names

freshVar :: Info -> String
freshVar (_,names) = f names (Set.size names) where
  f names' n = if Set.member name names' then Set.findMax names' ++ name else name where
    name = "_var" ++ show n

insertNameInfo :: String -> Info -> Info
insertNameInfo name (table,names) = (table,names') where
  names' = Set.insert name names

getTypeEnv :: Info -> TypeEnv
getTypeEnv (table,_) = toTypeEnv table

toTypeEnv :: TypeTable -> TypeEnv
toTypeEnv = Map.foldr' h Map.empty where
  h (Perpl.TpData (Perpl.TpN dat) ctors typs) r =
    Map.insert dat (Perpl.TpData (Perpl.TpN dat) ctors typs) r
  h _ r = r

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
unitUsTm = Perpl.UsProd Perpl.Multiplicative []
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
  let info = (table, names)
  usdefs <- translateDefs info defs
  usprgm <- translatePg info prgm
  return $ Perpl.UsProgs (usdata ++ usdefs) usprgm

translatePg :: Info -> Program -> Result Perpl.UsTm
translatePg info (PgTm tm) = transTerm info tm
translatePg info (PgIs iso) = transIso info iso

{-
Translate a term.
-}
transTerm :: Info -> Term -> Result Perpl.UsTm
transTerm info (TmAnn tm ty) = transTmWithTyp info ty tm
transTerm _ tm = err $ "Cannot translate an untype-checked term: " ++ show tm

transTmWithTyp :: Info -> BaseType -> Term -> Result Perpl.UsTm
transTmWithTyp _ _ TmUnit = return unitUsTm
transTmWithTyp _ _ (TmInt n) = return $ makeNat n where
  makeNat 0 = makeUsVar ctorZero
  makeNat n' = Perpl.UsApp (makeUsVar ctorSuc) (makeNat (n' - 1))
-- NOTE: even though this can be "correctly" translated into a perpl program,
-- perpl cannot process a value of this type yet!
transTmWithTyp info ty@(BTyList _) TmEmpty = do
  lTy <- lookupBaseInfo ty info
  -- "nil" is always the first constructor from an instantiated list type
  ctor <- extractCtor lTy 0
  return $ makeUsVar ctor
-- NOTE: even though this can be "correctly" translated into a perpl program,
-- perpl cannot process a value of this type yet!
transTmWithTyp info ty@(BTyList ety) (TmCons l r) = do
  lTy <- lookupBaseInfo ty info
  -- "cons" is always the first constructor from an instantiated list type
  ctor <- extractCtor lTy 1
  r' <- transTmWithTyp info (BTyList ty) r
  l' <- transTmWithTyp info ety l
  return $ Perpl.UsApp (Perpl.UsApp (makeUsVar ctor) l') r'
transTmWithTyp _ _ (TmVar var) = return $ makeUsVar var
transTmWithTyp info ty@(BTySum l _) (TmLInj tm) = do
  pTy <- lookupBaseInfo ty info
  ctor <- extractCtor pTy 0
  ustm <- transTmWithTyp info l tm
  makeDataApp (makeUsVar ctor) ustm l
transTmWithTyp info ty@(BTySum _ r) (TmRInj tm) = do
  pTy <- lookupBaseInfo ty info
  ctor <- extractCtor pTy 1
  ustm <- transTmWithTyp info r tm
  makeDataApp (makeUsVar ctor) ustm r
transTmWithTyp info ty@(BTyProd lT rT) (TmPair l r) = do
  pTy <- lookupBaseInfo ty info
  ctor <- extractCtor pTy 0
  ustmL <- transTmWithTyp info lT l
  ustmR <- transTmWithTyp info rT r
  let app = Perpl.UsApp (makeUsVar ctor) ustmL
  return $ Perpl.UsApp app ustmR
transTmWithTyp info _ (TmIsoApp rator rand) = do
  usRator <- transIso info rator
  usRand <- transTerm info rand
  return $ Perpl.UsApp usRator usRand
transTmWithTyp info ty (TmLet pat (TmAnn rhs ty') body) = do
  rhs' <- transTmWithTyp info ty' rhs
  body' <- transTmWithTyp info ty body
  makePatApp info ty' pat rhs' body'
transTmWithTyp _ _ (TmLet _ rhs _) = err $ "Cannot translate an untype-checked term: " ++ show rhs
transTmWithTyp info _ (TmAnn tm ty) = transTmWithTyp info ty tm
transTmWithTyp _ (BTyMu v b) tm = err $ "Unsupported term: " ++ show tm ++ " : " ++ show (BTyMu v b)
transTmWithTyp _ ty tm = err $ "Term and type mismatched: " ++ show tm ++ " :: " ++ show ty

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
makePatApp :: Info -> BaseType -> Pattern -> Perpl.UsTm -> Perpl.UsTm -> Result Perpl.UsTm
-- this translates to: let var = rhs in body
makePatApp _ _ (PtSingleVar var) rhs body = do
  return $ Perpl.UsLet (fromString var) rhs body
makePatApp _ _ (PtMultiVar []) _ body = return body
makePatApp _ _ (PtMultiVar [var]) rhs body =
  return $ Perpl.UsLet (fromString var) rhs body
-- this translates to: case rhs of c v1 ... in body
makePatApp info ty@(BTyProd _ rT) (PtMultiVar (var:vars)) rhs body = do
  pTy <- lookupBaseInfo ty info
  ctor <- extractCtor pTy 0
  body' <- makePatApp (insertNameInfo newVar info) rT (PtMultiVar vars) rhs' body
  let cas = Perpl.CaseUs (fromString ctor) (map fromString [var, newVar]) body'
  return $ Perpl.UsCase rhs [cas] where
    newVar = freshVar info
    rhs' = makeUsVar newVar
makePatApp _ ty (PtMultiVar vars) _ _ =
  Left $ "makePatApp: the number of variables <" ++ show vars ++
  "> doesn't match the type " ++ show ty

{-
Translate an iso.
-}
transIso :: Info -> Iso -> Result Perpl.UsTm
transIso info (IsoAnn iso ty) = transIsoWithTyp info ty iso
transIso _ iso = err $ "Cannot translate an untype-checked iso: " ++ show iso

transIsoWithTyp :: Info -> IsoType -> Iso -> Result Perpl.UsTm
transIsoWithTyp info (ITyBase vTy eTy) (IsoValue pairs) = do
  let var = freshVar info
  let info' = insertNameInfo var info
  vTy' <- lookupBaseInfo vTy info
  pairs' <- transPairsWithTyp info' (vTy, eTy) pairs
  let env = getTypeEnv info
  let pvar = (var, vTy')
  let e = toMatch pvar pairs'
  case compileMatch env (getNames info') e of
    Left Redundancy -> err $ "Redundant patterns in " ++ show (IsoValue pairs)
    Left Missing -> err $ "Non-exhaustive patterns in " ++ show (IsoValue pairs)
    Left er -> err $ "Impossible case: " ++ show er
    Right body -> return $ Perpl.UsLam (fromString var) (simplifyType vTy') body
transIsoWithTyp _ _ (IsoVar var) = return $ makeUsVar var
transIsoWithTyp info _ (IsoLam var lTy rTy body) = do
  lTy' <- lookupBaseInfo lTy info
  rTy' <- lookupBaseInfo rTy info
  let newTy = Perpl.TpArr lTy' rTy'
  body' <- transIso info body
  return $ Perpl.UsLam (fromString var) (simplifyType newTy) body'
transIsoWithTyp _ _ (IsoFix var lTy rTy body) =
  err $ "TODO: Unimplemented yet: " ++ show (IsoFix var lTy rTy body)
transIsoWithTyp info _ (IsoApp rator rand) = do
  usRator <- transIso info rator
  usRand <- transIso info rand
  return $ Perpl.UsApp usRator usRand
transIsoWithTyp info _ (IsoAnn iso ty) = transIsoWithTyp info ty iso
transIsoWithTyp _ ty iso = err $ "Iso and type mismatched: " ++ show iso ++ " :: " ++ show ty

transIsoTyp :: Info -> Iso -> Result Perpl.Type
transIsoTyp info (IsoAnn _ ty) = lookupIsoInfo ty info
transIsoTyp _ iso = err $ "Unable to find the type of a untype-checked global iso: " ++ show iso

simplifyType :: Perpl.Type -> Perpl.Type
simplifyType (Perpl.TpArr t1 t2) = Perpl.TpArr (simplifyType t1) (simplifyType t2)
simplifyType (Perpl.TpData (Perpl.TpN tag) _ _) = Perpl.TpVar $ fromString tag
simplifyType (Perpl.TpProd a tys) = Perpl.TpProd a (map simplifyType tys)
simplifyType t = t

{-
Compile pattern matching
-}
-- | Pattern is one of the following three forms:
--   upattern ::= c upattern ...
--     |   x
--     |   ()

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

-- | Convert a user pattern to a term.
toUsTm :: UsPattern -> Perpl.UsTm
toUsTm UUnit = unitUsTm
toUsTm (UCtor tag pats) = foldl Perpl.UsApp (makeUsVar tag) (map toUsTm pats)
toUsTm (UVar var) = makeUsVar var

toMatch :: PatVar -> [(UsPattern, Perpl.UsTm)] -> MatchExp
toMatch v = map f where
  f (pat, tm) = (Map.fromList [(v , pat)], tm)

{-
Translate a pair
-}
transPairsWithTyp :: Info -> (BaseType, BaseType) -> [(Value, Exp)] ->
  Result [(UsPattern, Perpl.UsTm)]
transPairsWithTyp info ty = mapM (transPairWithTyp info ty)

transPairWithTyp :: Info -> (BaseType, BaseType) -> (Value, Exp) ->
  Result (UsPattern, Perpl.UsTm)
transPairWithTyp info (vTy, eTy) (v, e) = do
  v' <- compileValWithTyp info vTy v
  e' <- transExpWithTyp info eTy e
  return (v', e')

{-
Translate a value
-}
compileValWithTyp :: Info -> BaseType -> Value -> Result UsPattern
compileValWithTyp _ _ ValUnit = return UUnit
compileValWithTyp _ _ (ValInt n) = return $ makeNat n where
  makeNat 0 = UCtor ctorZero []
  makeNat n' = UCtor ctorSuc [makeNat (n' - 1)]
compileValWithTyp info BTyInt (ValSuc n) = do
  n' <- compileValWithTyp info BTyInt n
  return $ UCtor ctorSuc [n']
-- NOTE: even though this can be "correctly" translated into a perpl program,
-- perpl cannot process a value of this type yet!
compileValWithTyp info ty@(BTyList _) ValEmpty = do
  lTy <- lookupBaseInfo ty info
  -- "nil" is always the first constructor from an instantiated list type
  ctor <- extractCtor lTy 0
  return $ UCtor ctor []
-- NOTE: even though this can be "correctly" translated into a perpl program,
-- perpl cannot process a value of this type yet!
compileValWithTyp info ty@(BTyList ety) (ValCons l r) = do
  lTy <- lookupBaseInfo ty info
  -- "cons" is always the second constructor from an instantiated list type
  ctor <- extractCtor lTy 1
  r' <- compileValWithTyp info ty r
  l' <- compileValWithTyp info ety l
  return $ UCtor ctor [l', r']
compileValWithTyp _ BTyUnit (ValVar _) = return UUnit
compileValWithTyp _ _ (ValVar var) = return $ UVar var
compileValWithTyp info ty@(BTySum l r) (ValLInj val) = do
  pTy <- lookupBaseInfo ty info
  ctor <- extractCtor pTy 0
  ustm <- compileValWithTyp info l val
  return $ makeDataApp' ctor ustm l
compileValWithTyp info ty@(BTySum l r) (ValRInj val) = do
  pTy <- lookupBaseInfo ty info
  ctor <- extractCtor pTy 1
  ustm <- compileValWithTyp info r val
  return $ makeDataApp' ctor ustm r
compileValWithTyp info ty@(BTyProd lT rT) (ValPair l r) = do
  pTy <- lookupBaseInfo ty info
  ctor <- extractCtor pTy 0
  ustmL <- compileValWithTyp info lT l
  ustmR <- compileValWithTyp info rT r
  return $ UCtor ctor [ustmL, ustmR]
compileValWithTyp info _ (ValAnn val ty) = compileValWithTyp info ty val
compileValWithTyp _ ty val = err $ "Value and type mismatch: " ++ show val ++ " :: " ++ show ty

makeDataApp' :: String -> UsPattern -> BaseType -> UsPattern
-- makeDataApp' rator pat ty
--   | trace ("makeDataApp' " ++ show rator ++ " " ++ show pat ++ " " ++ show ty) False = undefined
makeDataApp' rator _ BTyUnit = UCtor rator []
makeDataApp' rator rand _ = UCtor rator [rand]

{-
Translate a value.
-}
transValWithTyp :: Info -> BaseType -> Value -> Result Perpl.UsTm
transValWithTyp info ty val = toUsTm <$> compileValWithTyp info ty val

{-
Translate an expression.
-}
transExpWithTyp :: Info -> BaseType -> Exp -> Result Perpl.UsTm
transExpWithTyp info ty (ExpVal val) = transValWithTyp info ty val
transExpWithTyp info ty (ExpScale scale e) = do
  e' <- transExpWithTyp info ty e
  if imagPart scale == 0
    then return $ Perpl.UsFactor (realPart scale) e'
    else err "TODO: complex scale is not supported yet!"
transExpWithTyp info ty (ExpPlus es) = do
  es' <- mapM (transExpWithTyp info ty) es
  return $ Perpl.UsAmb es'
transExpWithTyp info ty (ExpLet pat (IsoAnn iso (ITyBase lTy rTy)) pat' body) = do
  isoTm <- transIsoWithTyp info (ITyBase lTy rTy) iso
  rhs <- Perpl.UsApp isoTm <$> mkRhs lTy pat'
  body' <- transExpWithTyp info ty body
  makePatApp info rTy pat rhs body' where
    mkRhs BTyUnit (PtSingleVar _) = return unitUsTm
    mkRhs _ (PtSingleVar v) = return $ makeUsVar v
    mkRhs BTyUnit (PtMultiVar [_]) = return unitUsTm
    mkRhs _ (PtMultiVar [v]) = return $ makeUsVar v
    mkRhs (BTyProd t t') (PtMultiVar (v:vs)) = do
      pLTy <- lookupBaseInfo (BTyProd t t') info
      ctorL <- extractCtor pLTy 0
      rVal <- mkRhs t' (PtMultiVar vs)
      return $ Perpl.UsApp (Perpl.UsApp (makeUsVar ctorL) (makeUsVar v)) rVal
    mkRhs t (PtMultiVar vs) = Left $ moduleName ++ "Invalid pattern " ++ show (PtMultiVar vs) ++
      " of type " ++ show t
transExpWithTyp _ _ (ExpLet _ (IsoAnn iso ty) _ _) =
  Left $ moduleName ++ "Not a base iso: " ++ show iso ++ ":" ++ show ty
transExpWithTyp _ _ (ExpLet _ iso _ _) =
  Left $ moduleName ++ "Cannot translate an untype-checked iso: " ++ show iso

{-
Translate an algebraic data definition.
-}
translateData :: TypeTable -> Result [Perpl.UsProg]
translateData = foldrM f [] where
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

translateDefs :: Info -> Definitions -> Result [Perpl.UsProg]
translateDefs info = foldrM f [] where
  f (str, iso) r = do
    isoTm <- transIso info iso
    isoTy <- transIsoTyp info iso
    let isoNm = fromString str
    return $ Perpl.UsProgDefine isoNm isoTm (simplifyType isoTy):r

{-
Collect all types into a set (type variables are not considered yet)
-}
collectTypes :: (Definitions, Program) -> Result Types
collectTypes (defs, prgm) = do
  dfTys <- clTypDefs defs
  pgTys <- clTypPg prgm
  return $ Set.union dfTys pgTys

clTypDefs :: Definitions -> Result Types
clTypDefs = foldlM clTypDef Set.empty where
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
clTypValue (ValSuc v) = clTypValue v
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
clNmDefs = foldlM clNmDef Set.empty where
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
clNmIso (IsoVar _) = return Set.empty
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
clNmValue (ValSuc v) = clNmValue v
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
transBaseType' _ _ (BTyVar var) = err $ moduleName ++ "Unsupported type: " ++ show (BTyVar var)
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
transBaseType' _ _ (BTyMu v b) = err $ moduleName ++ "Unsupported type: " ++ show (BTyMu v b)

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
  n = "DTy" ++ show (Map.size table)

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
