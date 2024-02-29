module Interp (interp) where

import Data
import Debug.Trace (trace)

interp :: ValEnv -> Program -> Maybe ProgramValue
interp env (PgTm tm) = do {
  v <- (interpTerm env tm)
  ; Just (PB v)
  }
interp env (PgIs iso) = do {
  v <- interpIso env iso
  ; Just (PI v)
  }

interpTerm :: ValEnv -> Term -> Maybe ProgramBaseValue
interpTerm _ TmUnit = Just PBValUnit
interpTerm _ (TmInt n) = Just (PBValInt n)
interpTerm env (TmVar var) = lookupBase env var
interpTerm env (TmLInj tm) = do {
  v <- interpTerm env tm
  ; Just (PBValLeft v)
  }
interpTerm env (TmRInj tm) = do {
  v <- interpTerm env tm
  ; Just (PBValRight v)
  }
interpTerm env (TmPair t1 t2) = do {
  v1 <- interpTerm env t1
  ; v2 <- interpTerm env t2
  ; Just (PBValPair v1 v2)
  }
interpTerm env (TmIsoApp iso tm) = do {
  fun <- interpIso env iso
  ; arg <- interpTerm env tm
  ; applyIsoTerm fun arg
  }
interpTerm env (TmLet pat rhs body) = do {
  vRhs <- interpTerm env rhs
  ; newEnv <- extendPattern env pat vRhs
  ; interpTerm newEnv body
  }
interpTerm env (TmAnn tm _) = interpTerm env tm

interpIsoPattern :: ValEnv -> (Value, Exp) -> (Maybe ProgramBaseValue, Maybe ProgramBaseValue)
interpIsoPattern env (pat, e) = (lhs, rhs) where
  lhsPair = interpPattern env pat
  lhs = Just $ fst lhsPair
  vars = map (\x -> (x , PB (PBValVar x))) (snd lhsPair)
  rhs = interpExp (vars ++ env) e

interpIso :: ValEnv -> Iso -> Maybe ProgramIsoValue
interpIso env (IsoValue vs es) = do {
  let pairs = map (interpIsoPattern env) $ zip vs es
  ; newPairs <- zipValues pairs
  ; Just (PIValBase newPairs env)
  }
interpIso env (IsoVar var) = do {
  v <- lookup var env
  ; case v of
      PI iv -> Just iv
      _ -> Nothing
  }
interpIso env (IsoLam var _ _ body) =
  Just (PIValLam var body env)
interpIso env (IsoApp lhs rhs) = do {
  lval <- interpIso env lhs
  ; rval <- interpIso env rhs
  ; applyIsoIso lval rval
  }
interpIso _ (IsoFix _ _) = error "Evaluation of IsoFix is not supported yet!"
interpIso env (IsoAnn iso _) = interpIso env iso

interpPattern :: ValEnv -> Value -> (ProgramBaseValue, [String])
interpPattern _ ValUnit = (PBValUnit , [])
interpPattern _ (ValInt n) = (PBValInt n , [])
interpPattern _ (ValVar var) = (PBValVar var , [var])
interpPattern env (ValLInj lhs) = (PBValLeft $ fst rst , snd rst) where
  rst = interpPattern env lhs
interpPattern env (ValRInj rhs) = (PBValRight $ fst rst , snd rst) where
  rst = interpPattern env rhs
interpPattern env (ValPair lhs rhs) =
  (PBValPair (fst v1) (fst v2) , (snd v1) ++ (snd v2)) where
    v1 = interpPattern env lhs
    v2 = interpPattern env rhs
interpPattern env (ValAnn val _) = interpPattern env val
--  TODO: ValFold

interpValue :: ValEnv -> Value -> Maybe ProgramBaseValue
interpValue _ ValUnit = Just PBValUnit
interpValue _ (ValInt n) = Just (PBValInt n)
interpValue env (ValVar var) = lookupBase env var
interpValue env (ValLInj lhs) =  do {
  v <- interpValue env lhs
  ; Just (PBValLeft v)
  }
interpValue env (ValRInj rhs) =  do {
  v <- interpValue env rhs
  ; Just (PBValRight v)
  }
interpValue env (ValPair lhs rhs) =  do {
  v1 <- interpValue env lhs
  ; v2 <- interpValue env rhs
  ; Just (PBValPair v1 v2)
  }
interpValue env (ValAnn val _) = interpValue env val
--  TODO: ValFold

interpExp :: ValEnv -> Exp -> Maybe ProgramBaseValue
interpExp env (ExpVal v) = interpValue env v
interpExp env (ExpLet pat rhs body) = do {
  vRhs <- interpExp env rhs
  ; newEnv <- extendPattern env pat vRhs
  ; interpExp newEnv body
  }

lookupBase :: ValEnv -> String -> Maybe ProgramBaseValue
lookupBase env var = do {
  v <- lookup var env
  ; case v of
      PB bv -> Just bv
      _ -> Nothing
  }

isMatch :: ProgramBaseValue -> ProgramBaseValue -> Bool
isMatch PBValUnit PBValUnit = True
isMatch (PBValInt n1) (PBValInt n2) = (n1 == n2)
isMatch (PBValVar _) _ = True
isMatch (PBValLeft v1) (PBValLeft v2) = isMatch v1 v2
isMatch (PBValRight v1) (PBValRight v2) = isMatch v1 v2
isMatch (PBValPair l1 r1) (PBValPair l2 r2) = isMatch l1 l2 && isMatch r1 r2
isMatch _ _ = False

extracPatterns :: ProgramBaseValue -> ProgramBaseValue -> ValEnv
extracPatterns PBValUnit _ = []
extracPatterns (PBValInt _) _ = []
extracPatterns (PBValVar var) val = [(var , PB val)]
extracPatterns (PBValLeft v1) (PBValLeft v2) = extracPatterns v1 v2
extracPatterns (PBValRight v1) (PBValRight v2) = extracPatterns v1 v2
extracPatterns (PBValPair l1 r1) (PBValPair l2 r2) = extracPatterns l1 l2 ++ extracPatterns r1 r2
extracPatterns _ _ = []

interpExpValue :: ValEnv -> ProgramBaseValue -> Maybe ProgramBaseValue
interpExpValue _ PBValUnit = Just PBValUnit
interpExpValue _ (PBValInt n) = Just (PBValInt n)
interpExpValue env (PBValVar var) = lookupBase env var
interpExpValue env (PBValLeft l) = do {
  lVal <- interpExpValue env l
  ; Just (PBValLeft lVal)
  }
interpExpValue env (PBValRight l) = do {
  lVal <- interpExpValue env l
  ; Just (PBValRight lVal)
  }
interpExpValue env (PBValPair l r) = do {
  lVal <- interpExpValue env l
  ; rVal <- interpExpValue env r
  ; Just (PBValPair lVal rVal)
  }

patternMatch :: ValEnv -> [(ProgramBaseValue , ProgramBaseValue)] -> ProgramBaseValue
  -> Maybe ProgramBaseValue
patternMatch _ [] _ = Nothing
patternMatch env ((lhs , rhs) : tl) v =
  if isMatch lhs v
  then let pairs = extracPatterns lhs v
           newEnv = pairs ++ env
       in interpExpValue newEnv rhs
  else patternMatch env tl v

applyIsoTerm :: ProgramIsoValue -> ProgramBaseValue -> Maybe ProgramBaseValue
-- applyIsoTerm l r | trace ("applyIsoTerm " ++ show l ++ " " ++ show r) False = undefined
applyIsoTerm (PIValBase isos env) rhs = patternMatch env isos rhs
applyIsoTerm _ _ = Nothing

applyIsoIso :: ProgramIsoValue -> ProgramIsoValue -> Maybe ProgramIsoValue
applyIsoIso (PIValLam var body env) rhs = interpIso ((var , (PI rhs)) : env) body
applyIsoIso (PIValFix var body env) _ =
  error $ "Application of IsoFix is not supported yet, given" ++ show (PIValFix var body env)
applyIsoIso (PIValBase pairs env) _ =
  error $ "Expect an Iso Lambda, given an Iso Base " ++ show (PIValBase pairs env)

extendPattern :: ValEnv -> Pattern -> ProgramBaseValue -> Maybe ValEnv
extendPattern env (PtSingleVar var) val  = Just ((var , PB val) : env)
extendPattern env (PtMultiVar (var : [])) val  = Just ((var , PB val) : env)
extendPattern env (PtMultiVar (var : vars)) (PBValPair hd tl)  = do {
  newTl <- extendPattern env (PtMultiVar vars) tl
  ; Just ((var , (PB hd)) : newTl)
  }
extendPattern _ _ _ = Nothing

zipValues :: [(Maybe ProgramBaseValue, Maybe ProgramBaseValue)] ->
  Maybe [(ProgramBaseValue, ProgramBaseValue)]
zipValues [] = Just []
zipValues (((Just lh), (Just rh)) : tl) = do {
  let hd = (lh , rh)
  ; newTl <- zipValues tl
  ; Just (hd : newTl)
  }
zipValues _ = Nothing
