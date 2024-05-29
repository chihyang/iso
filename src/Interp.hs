module Interp (interp, interpDefsPg, interpEnv, applyIso) where

import Syntax
import Data.List (sortBy)
import Debug.Trace (trace)
import OrthoCheck (unify, orthoList)

moduleName :: String
moduleName = "Interpreter: "

interpDefsPg :: (Definitions, Program) -> Result ProgramValue
interpDefsPg (defs, pg) = do
  env <- interpDefs defs
  let env' = replaceVal env env
  interpEnv env' pg
  where
    replaceVal _ EmptyVEnv = EmptyVEnv
    replaceVal env (ExtendIsoVEnv var iso env') =
      extendIsoEnv var (replaceIsoEnv env iso) (replaceVal env env')
    replaceVal env (ExtendBaseVEnv var val env') =
      extendBaseEnv var val (replaceVal env env')
    replaceVal env (ExtendIsoRecEnv var body env') =
      extendIsoRecEnv var body (replaceVal env env')

    replaceIsoEnv env (PIValBase pairs _) = PIValBase pairs env
    replaceIsoEnv env (PIValLam var iso _) = PIValLam var iso env

interpDefs :: Definitions -> Result ValEnv
interpDefs [] = return emptyEnv
interpDefs ((var,def):defs) = do
  isos <- interpDefs defs
  iso <- interpIso emptyEnv def
  return $ extendIsoEnv var iso isos

interp :: Program -> Result ProgramValue
interp pg = interpEnv emptyEnv pg

interpEnv :: ValEnv -> Program -> Result ProgramValue
interpEnv env (PgTm tm) = do
  v <- (interpTm env tm)
  return (PQ v)
interpEnv env (PgIs iso) = do
  v <- interpIso env iso
  return (PI v)

{---------- Interpretation of Terms ----------}
interpTm :: ValEnv -> Term -> Result EntangledValue
interpTm _ TmUnit = return [(1, PBValUnit)]
interpTm _ (TmInt n) = return [(1, PBValInt n)]
interpTm _ TmEmpty = return [(1, PBValEmpty)]
interpTm env (TmCons v vs) = do
  v' <- interpTm env v
  vs' <- interpTm env vs
  return $ distrib2 PBValCons v' vs'
interpTm env (TmVar var) = lookupBase env var
interpTm env (TmLInj tm) = do
  v <- interpTm env tm
  return $ distrib1 PBValLeft v
interpTm env (TmRInj tm) = do
  v <- interpTm env tm
  return $ distrib1 PBValRight v
interpTm env (TmPair t1 t2) = do
  v1 <- interpTm env t1
  v2 <- interpTm env t2
  return $ distrib2 PBValPair v1 v2
interpTm env (TmIsoApp iso tm) = do
  fun <- interpIso env iso
  arg <- interpTm env tm
  applyIso fun arg
interpTm env (TmLet pat rhs body) = do
  vRhs <- interpTm env rhs
  newEnv <- extScalePat env pat vRhs
  interpTm newEnv body
interpTm env (TmAnn tm _) = interpTm env tm

{---------- Interpretation of Isos ----------}
interpIso :: ValEnv -> Iso -> Result ProgramIsoValue
interpIso env (IsoValue ps) = do
  let pats = map fst ps
  let exps = map snd ps
  pats' <- interpPats env pats
  pats'' <- orthoList pats'
  return (PIValBase (zip pats'' exps) env)
interpIso env (IsoVar var) = lookupIso env var
interpIso env (IsoLam var _ _ body) = return (PIValLam var body env)
interpIso env (IsoApp lhs rhs) = do
  lval <- interpIso env lhs
  rval <- interpIso env rhs
  applyIsoLam lval rval
interpIso _ (IsoFix var lTy rTy body) =
  Left $ moduleName ++ "Untyped fix iso " ++ show (IsoFix var lTy rTy body) ++ " cannot be evaluated!"
interpIso env (IsoAnn (IsoFix var lTy rTy body) otype) =
  interpIso newEnv (IsoVar res) where
    res = uniqueName env
    body' = translateFix res var lTy rTy body otype
    newEnv = extendIsoRecEnv res body' env
interpIso env (IsoAnn iso _) = interpIso env iso

translateFix :: String -> String -> BaseType -> BaseType -> Iso -> IsoType -> Iso
translateFix res var lTy rTy body ty =
  makeIsoLam body' baseVar vars ty where
    baseVar = newName res
    vars = genBinds baseVar ty
    rator = IsoLam var lTy rTy body
    rand = makeIsoApp (IsoVar res) vars
    body' = makeIsoApp (IsoApp rator rand) vars

genBinds :: String -> IsoType -> [String]
genBinds base (ITyBase _ _) = []
genBinds base (ITyFun _ _ b) = newId : genBinds newId b where
  newId = newName base

makeIsoApp :: Iso -> [String] -> Iso
-- makeIsoApp iso vars | trace ("makeIsoApp " ++ show iso ++ " " ++ show vars) False = undefined
makeIsoApp iso vars = foldl (\acc var -> (IsoApp acc (IsoVar var))) iso vars

makeIsoLam :: Iso -> String -> [String] -> IsoType -> Iso
-- At bottom, we need an extra iso that looks like:
-- {
--   v <-> let out = (((\f -> w) (res f1 ...)) f1 ...) v in out
-- }
makeIsoLam body baseVar [] (ITyBase _ _) =
  IsoValue [(ValVar baseVar,
             ExpLet (PtSingleVar baseVar) body (PtSingleVar baseVar)
             (ExpVal (ValVar baseVar)))]
makeIsoLam body baseVar (var:vars) (ITyFun lTy rTy bodyTy) =
  IsoLam var lTy rTy (makeIsoLam body baseVar vars bodyTy)
makeIsoLam _ _ vars ty =
  error $ moduleName ++ "variable list " ++ show vars ++ " and iso type " ++ show ty ++ " mismatch!"

{---------- Applying An Iso To A Term ----------}
applyIso :: ProgramIsoValue -> EntangledValue -> Result EntangledValue
-- applyIso l r | trace ("applyIso " ++ show l ++ " " ++ show r) False = undefined
applyIso (PIValBase pairs env) rhs = patternMatchEnt env pairs rhs
applyIso iso base = Left $ moduleName ++ "Cannot apply iso " ++ show iso ++ " to " ++ show base

{---------- Applying An Iso To An Iso ----------}
applyIsoLam :: ProgramIsoValue -> ProgramIsoValue -> Result ProgramIsoValue
-- applyIsoLam l r | trace ("applyIsoLam " ++ show l ++ " " ++ show r) False = undefined
applyIsoLam (PIValLam var body env) rhs = interpIso (extendIsoEnv var rhs env) body
applyIsoLam (PIValBase pairs env) _ =
  error $ "Expect an Iso Lambda, given an Iso Base " ++ show (PIValBase pairs env)

{---------- Interpretation of Values on the Right hand side ----------}
interpValue :: ValEnv -> Value -> Result EntangledValue
interpValue _ ValUnit = return [(1, PBValUnit)]
interpValue _ (ValInt n) = return [(1, PBValInt n)]
interpValue _ ValEmpty = return [(1, PBValEmpty)]
interpValue env (ValCons v vs) = do
  v' <- interpValue env v
  vs' <- interpValue env vs
  return $ distrib2 PBValCons v' vs'
interpValue env (ValVar var) = lookupBase env var
interpValue env (ValLInj lhs) = do
  v <- interpValue env lhs
  return $ distrib1 PBValLeft v
interpValue env (ValRInj rhs) = do
  v <- interpValue env rhs
  return $ distrib1 PBValRight v
interpValue env (ValPair lhs rhs) = do
  v1 <- interpValue env lhs
  v2 <- interpValue env rhs
  return $ distrib2 PBValPair v1 v2
interpValue env (ValAnn val _) = interpValue env val
--  TODO: ValFold

{---------- Interpretation of Patterns in LHS ----------}
interpPats :: ValEnv -> [Value] -> Result [ProgramBaseValue]
interpPats _ [] = return []
interpPats env (v:vs) = do
  v' <- interpPat env v
  vs' <- interpPats env vs
  return (v' : vs')

{---------- Interpretation of One Pattern in LHS ----------}
interpPat :: ValEnv -> Value -> Result ProgramBaseValue
interpPat _ ValUnit = return PBValUnit
interpPat _ (ValInt n) = return $ PBValInt n
interpPat _ ValEmpty = return $ PBValEmpty
interpPat env (ValCons v vs) = do
  v' <- interpPat env v
  vs' <- interpPat env vs
  return $ PBValCons v' vs'
interpPat _ (ValVar var) = return $ PBValVar var
interpPat env (ValLInj lhs) = do
  rst <- interpPat env lhs
  return $ PBValLeft rst
interpPat env (ValRInj rhs) = do
  rst <- interpPat env rhs
  return $ PBValRight rst
interpPat env (ValPair lhs rhs) = do
  v1 <- interpPat env lhs
  v2 <- interpPat env rhs
  return $ PBValPair v1 v2
interpPat env (ValAnn val _) = interpPat env val
--  TODO: ValFold

{---------- Interpretation of Expressions ----------}
interpExp :: ValEnv -> Exp -> Result EntangledValue
-- interpExp env e | trace ("interpExp " ++ show env ++ " " ++ show e) False = undefined
interpExp env (ExpVal v) = interpValue env v
interpExp env (ExpLet pat iso pat' body) = do
  rhsIso <- interpIso env iso
  rhsVal <- interpRhsPat env pat'
  vRhs <- applyIso rhsIso rhsVal
  newEnv <- extScalePat env pat vRhs
  interpExp newEnv body
interpExp env (ExpScale s e) = do
  es <- interpExp env e
  return $ sortBy (\(_,a) (_,b) -> compare a b) $ scaleEnt s es
interpExp _ (ExpPlus []) = return []
interpExp env (ExpPlus (e:es)) = do
  v <- interpExp env e
  vs <- interpExp env (ExpPlus es)
  return $ mergeEnt v vs

{---------- Interpretation of Patterns in iso RHS' RHS  ----------}
interpRhsPat :: ValEnv -> Pattern -> Result EntangledValue
-- interpRhsPat env pat | trace ("interpRhsPat " ++ show env ++ " " ++ show pat) False = undefined
interpRhsPat env (PtSingleVar var) = lookupBase env var
interpRhsPat env (PtMultiVar (var : [])) = lookupBase env var
interpRhsPat env (PtMultiVar (var : vars)) = do
  val <- lookupBase env var
  vals <- interpRhsPat env (PtMultiVar vars)
  return $ distrib2 PBValPair val vals
interpRhsPat _ pat = Left $ moduleName ++ "Invalid pattern: " ++ show pat

{---------- Given a pattern value and an entangled value, try to evaluate it. ----------}
patternMatchEnt :: ValEnv -> [(ProgramBaseValue , Exp)] -> EntangledValue -> Result EntangledValue
-- patternMatchEnt env pair val | trace ("patternMatchEnt " ++ show env ++ " " ++ show pair ++ " " ++ show val) False = undefined
patternMatchEnt env pairs [(s,v)] = do
  vs <- patternMatch env pairs v
  return $ scaleEnt s vs
patternMatchEnt env pairs ((s,v):vs) = do
  rst <- patternMatch env pairs v
  rst' <- patternMatchEnt env pairs vs
  let scaledRst = scaleEnt s rst
  return $ mergeEnt scaledRst rst'
patternMatchEnt _ _ [] = Left $ moduleName ++ "At least one value should be in the entangled value!"

{---------- Pattern Matching in iso RHS ----------}
patternMatch :: ValEnv -> [(ProgramBaseValue , Exp)] -> ProgramBaseValue -> Result EntangledValue
-- patternMatch env pair val | trace ("patternMatch " ++ show env ++ " " ++ show pair ++ " " ++ show val) False = undefined
patternMatch _ [] val = Left $ moduleName ++ "Invalid pattern: no match for the value " ++ show val
patternMatch env ((lhs , rhs) : tl) v = do
  case unify [] lhs v of
    Just pairs -> let env' = foldl (\acc (var, val) ->
                                      extendBaseEnv var [(1, val)] acc)
                             env pairs
                  in interpExp env' rhs
    Nothing -> patternMatch env tl v

{---------- Extending Environments With Patterns For A List of Values ----------}
extScalePat :: ValEnv -> Pattern -> EntangledValue -> Result ValEnv
-- extScalePat env pat val | trace ("extScalePat " ++ show env ++ " " ++ show pat ++ " " ++ show val) False = undefined
extScalePat env (PtSingleVar var) val  = return $ extendBaseEnv var val env
extScalePat env (PtMultiVar (var : [])) val  = return $ extendBaseEnv var val env
extScalePat env (PtMultiVar (var : vars)) val =
  if allPair val
  then do
    let hds = map (\v -> (fst v, getHead $ snd v)) val
    let tls = map (\v -> (fst v, getTail $ snd v)) val
    newTl <- extScalePat env (PtMultiVar vars) tls
    return $ extendBaseEnv var hds newTl
  else
    Left $ moduleName ++ "Mismatched pattern and value: " ++ show (var:vars) ++ ", " ++ show val
  where
    allPair vals = everyPair $ map snd vals

    everyPair [] = True
    everyPair (v:vs) = if isPair v then everyPair vs else False

    isPair (PBValPair _ _) = True
    isPair _ = False

    getHead (PBValPair hd _) = hd
    getHead _ = error "getHead shouldn't be used here!"

    getTail (PBValPair _ tl) = tl
    getTail _ = error "getTail shouldn't be used here!"
extScalePat _ pat val = Left $ moduleName ++ "Mismatched pattern and value: " ++ show pat ++ ", " ++ show val

{---------- Environment Lookup ----------}
emptyEnv :: ValEnv
emptyEnv = EmptyVEnv

extendBaseEnv :: String -> EntangledValue -> ValEnv -> ValEnv
extendBaseEnv var val env = ExtendBaseVEnv var val env

extendIsoEnv :: String -> ProgramIsoValue -> ValEnv -> ValEnv
extendIsoEnv var val env = ExtendIsoVEnv var val env

extendIsoRecEnv :: String -> Iso -> ValEnv -> ValEnv
extendIsoRecEnv var body env = ExtendIsoRecEnv var body env

uniqueName :: ValEnv -> String
uniqueName env = "id_" ++ (show $ envLength env) where
  envLength :: ValEnv -> Int
  envLength EmptyVEnv = 0
  envLength (ExtendIsoVEnv var _ env') = max (length var) (envLength env')
  envLength (ExtendBaseVEnv var _ env') = max (length var) (envLength env')
  envLength (ExtendIsoRecEnv var _ env') = max (length var) (envLength env')

newName :: String -> String
newName var = "_" ++ var

lookupBase :: ValEnv -> String -> Result EntangledValue
-- lookupBase env var | trace ("lookupBase " ++ show env ++ " " ++ show var) False = undefined
lookupBase EmptyVEnv var = Left $ moduleName ++ "Cannot find the value " ++ var
lookupBase (ExtendIsoVEnv var _ env) var'
  | var == var' = Left $ moduleName ++ var ++ " is not a base value!"
  | otherwise = lookupBase env var'
lookupBase (ExtendIsoRecEnv var _ env) var'
  | var == var' = Left $ moduleName ++ var ++ " is not a base value!"
  | otherwise = lookupBase env var'
lookupBase (ExtendBaseVEnv var val env) var'
  | var == var' = return val
  | otherwise = lookupBase env var'

lookupIso :: ValEnv -> String -> Result ProgramIsoValue
-- lookupIso env var | trace ("lookupIso " ++ show env ++ " " ++ show var) False = undefined
lookupIso EmptyVEnv var = Left $ moduleName ++ "Cannot find the value " ++ var
lookupIso (ExtendIsoVEnv var iso env) var'
  | var == var' = return iso
  | otherwise = lookupIso env var'
lookupIso (ExtendIsoRecEnv var (IsoLam bVar lTy rTy bBody) env) var'
  | var == var' = return $ PIValLam bVar bBody (ExtendIsoRecEnv var (IsoLam bVar lTy rTy bBody) env)
  | otherwise = lookupIso env var'
lookupIso (ExtendIsoRecEnv var (IsoValue [(ValVar v, exp)]) env) var'
  | var == var' = return $ PIValBase [(PBValVar v, exp)] (ExtendIsoRecEnv var (IsoValue [(ValVar v, exp)]) env)
  | otherwise = lookupIso env var'
lookupIso (ExtendIsoRecEnv var body env) var'
  | var == var' = Left $ "Invalid recursive environment binding: " ++ show var ++ " = " ++ show body
  | otherwise = lookupIso env var'
lookupIso (ExtendBaseVEnv var _ env) var'
  | var == var' = Left $ moduleName ++ var ++ " is not an iso value!"
  | otherwise = lookupIso env var'
