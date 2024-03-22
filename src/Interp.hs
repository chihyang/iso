module Interp (interp, interpEnv, applyIso) where

import Syntax
import Debug.Trace (trace)
import OrthoCheck (unify, orthoList)

moduleName :: String
moduleName = "Interpreter: "

interp :: Program -> Result ProgramValue
interp pg = interpEnv [] pg

interpEnv :: ValEnv -> Program -> Result ProgramValue
interpEnv env (PgTm tm) = do
  v <- (interpTm env tm)
  return (PB v)
interpEnv env (PgIs iso) = do
  v <- interpIso env iso
  return (PI v)

{---------- Interpretation of Terms ----------}
interpTm :: ValEnv -> Term -> Result ProgramBaseValue
interpTm _ TmUnit = return PBValUnit
interpTm _ (TmInt n) = return (PBValInt n)
interpTm env (TmVar var) = lookupBase env var
interpTm env (TmLInj tm) = do
  v <- interpTm env tm
  return (PBValLeft v)
interpTm env (TmRInj tm) = do
  v <- interpTm env tm
  return (PBValRight v)
interpTm env (TmPair t1 t2) = do
  v1 <- interpTm env t1
  v2 <- interpTm env t2
  return (PBValPair v1 v2)
interpTm env (TmIsoApp iso tm) = do
  fun <- interpIso env iso
  arg <- interpTm env tm
  applyIso fun arg
interpTm env (TmLet pat rhs body) = do
  vRhs <- interpTm env rhs
  newEnv <- extPat env pat vRhs
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
interpIso _ (IsoFix _ _) = error "Evaluation of IsoFix is not supported yet!"
interpIso env (IsoAnn iso _) = interpIso env iso

{---------- Applying An Iso To A Term ----------}
applyIso :: ProgramIsoValue -> ProgramBaseValue -> Result ProgramBaseValue
-- applyIso l r | trace ("applyIso " ++ show l ++ " " ++ show r) False = undefined
applyIso (PIValBase pairs env) rhs = patternMatch env pairs rhs
applyIso iso base = Left $ moduleName ++ "Cannot apply iso " ++ show iso ++ " to " ++ show base

{---------- Applying An Iso To An Iso ----------}
applyIsoLam :: ProgramIsoValue -> ProgramIsoValue -> Result ProgramIsoValue
-- applyIsoLam l r | trace ("applyIsoLam " ++ show l ++ " " ++ show r) False = undefined
applyIsoLam (PIValLam var body env) rhs = interpIso ((var , (PI rhs)) : env) body
applyIsoLam (PIValFix var body env) _ =
  error $ "Application of IsoFix is not supported yet, given " ++ show (PIValFix var body env)
applyIsoLam (PIValBase pairs env) _ =
  error $ "Expect an Iso Lambda, given an Iso Base " ++ show (PIValBase pairs env)

{---------- Interpretation of Values ----------}
interpValue :: ValEnv -> Value -> Result ProgramBaseValue
interpValue _ ValUnit = return PBValUnit
interpValue _ (ValInt n) = return (PBValInt n)
interpValue env (ValVar var) = lookupBase env var
interpValue env (ValLInj lhs) = do
  v <- interpValue env lhs
  return (PBValLeft v)
interpValue env (ValRInj rhs) = do
  v <- interpValue env rhs
  return (PBValRight v)
interpValue env (ValPair lhs rhs) = do
  v1 <- interpValue env lhs
  v2 <- interpValue env rhs
  return (PBValPair v1 v2)
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
interpExp :: ValEnv -> Exp -> Result ProgramBaseValue
interpExp env (ExpVal v) = interpValue env v
interpExp env (ExpLet pat iso pat' body) = do
  rhsIso <- interpIso env iso
  rhsVal <- interpRhsPat env pat'
  vRhs <- applyIso rhsIso rhsVal
  newEnv <- extPat env pat vRhs
  interpExp newEnv body

{---------- Interpretation of Patterns in iso RHS' RHS  ----------}
interpRhsPat :: ValEnv -> Pattern -> Result ProgramBaseValue
interpRhsPat env (PtSingleVar var) = lookupBase env var
interpRhsPat env (PtMultiVar (var : [])) = lookupBase env var
interpRhsPat env (PtMultiVar (var : vars)) = do
  val <- lookupBase env var
  vals <- interpRhsPat env (PtMultiVar vars)
  return $ PBValPair val vals
interpRhsPat _ pat = Left $ moduleName ++ "Invalid pattern: " ++ show pat

{---------- Pattern Matching in iso RHS ----------}
patternMatch :: ValEnv -> [(ProgramBaseValue , Exp)] -> ProgramBaseValue
  -> Result ProgramBaseValue
-- patternMatch env pair val
--   | trace ("patternMatch " ++ show env ++ " " ++ show pair ++ " " ++ show val) False =
--       undefined
patternMatch _ [] val = Left $ moduleName ++ "Invalid pattern: no match for the value " ++ show val
patternMatch env ((lhs , rhs) : tl) v = do
  case unify [] lhs v of
    Just pairs -> let env' = map (\p -> (fst p, PB $ snd p)) pairs in
                    interpExp (env' ++ env) rhs
    Nothing -> patternMatch env tl v

{---------- Extending Environments With Patterns ----------}
extPat :: ValEnv -> Pattern -> ProgramBaseValue -> Result ValEnv
extPat env (PtSingleVar var) val  = return ((var , PB val) : env)
extPat env (PtMultiVar (var : [])) val  = return ((var , PB val) : env)
extPat env (PtMultiVar (var : vars)) (PBValPair hd tl) = do
  newTl <- extPat env (PtMultiVar vars) tl
  return ((var , (PB hd)) : newTl)
extPat _ pat val = Left $ moduleName ++ "Mismatched pattern and value: " ++ show pat ++ ", " ++ show val

{---------- Environment Lookup ----------}
lookupBase :: ValEnv -> String -> Result ProgramBaseValue
-- lookupBase env var | trace ("lookupBase " ++ show env ++ " " ++ show var) False = undefined
lookupBase env var = do
  case lookup var env of
    Just (PB bv) -> return bv
    _ -> Left $ moduleName ++ "Cannot find the value " ++ show var

lookupIso :: ValEnv -> String -> Result ProgramIsoValue
-- lookupIso env var | trace ("lookupIso " ++ show env ++ " " ++ show var) False = undefined
lookupIso env var = do
  case lookup var env of
    Just (PI bv) -> return bv
    _ -> Left $ moduleName ++ "Cannot find the iso " ++ show var
