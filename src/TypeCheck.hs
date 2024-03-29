module TypeCheck (typeInfer, typeInferEnv) where

import Syntax

moduleName :: String
moduleName = "Type Check: "

typeInfer :: Program -> Result Program
typeInfer pg = typeInferEnv [] pg

typeInferEnv :: TypEnv -> Program -> Result Program
typeInferEnv env (PgTm tm) = do
  rst <- tiTm env tm
  return $ PgTm $ snd rst
typeInferEnv env (PgIs iso) = do
  rst <- tiIso env iso
  return $ PgIs $ snd rst

{---------- Bidirectional type checking for Terms ----------}
-- Return a type annotated term together with its type.
tiTm :: TypEnv -> Term -> Result (BaseType, Term)
tiTm _ TmUnit = return (BTyUnit , TmAnn TmUnit BTyUnit)
tiTm _ (TmInt n) = return (BTyInt , TmAnn (TmInt n) BTyInt)
tiTm env (TmVar var) = do
  ty <- applyBaseEnv env var
  return (ty , TmAnn (TmVar var) ty)
tiTm _ (TmLInj tm) = Left $ moduleName ++ "Type annotation is required for the term " ++ show (TmLInj tm)
tiTm _ (TmRInj tm) = Left $ moduleName ++ "Type annotation is required for the term " ++ show (TmLInj tm)
tiTm env (TmPair l r) = do
  rstL <- tiTm env l
  rstR <- tiTm env r
  let lTy = fst rstL
  let rTy = fst rstR
  let lTm = snd rstL
  let rTm = snd rstR
  let oType = (BTyProd lTy rTy)
  return (oType , TmAnn (TmPair lTm rTm) oType)
tiTm env (TmIsoApp iso tm) = do
  isoRst <- tiIso env iso
  let isoTy = fst isoRst
  let iso' = snd isoRst
  pair <- tcRator iso' isoTy
  let randTy = fst pair
  let bodyTy = snd pair
  rst <- tcTm env tm randTy
  let tm' = snd rst
  return (bodyTy , (TmAnn (TmIsoApp iso' tm') bodyTy))
tiTm env (TmLet pat rhs body) = do
  rhsRst <- tiTm env rhs
  let rhsTy = fst rhsRst
  let rhs' = snd rhsRst
  newEnv <- extPatEnv env pat rhsTy
  bodyRst <- tiTm newEnv body
  let bodyTy = fst bodyRst
  let body' = snd bodyRst
  return (bodyTy , TmAnn (TmLet pat rhs' body') bodyTy)
tiTm env (TmAnn tm ty) = tcTm env tm ty

tcTm :: TypEnv -> Term -> BaseType -> Result (BaseType, Term)
tcTm env TmUnit ty =
  if typeEqual env BTyUnit ty
  then return (BTyUnit , TmAnn TmUnit BTyUnit)
  else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show BTyUnit ++ " in " ++ show TmUnit
tcTm env (TmInt n) ty =
  if typeEqual env BTyInt ty
  then return (BTyInt , TmAnn (TmInt n) BTyInt)
  else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show BTyInt ++ " in " ++ show (TmInt n)
tcTm env (TmVar var) ty = do
  ty' <- applyBaseEnv env var
  if typeEqual env ty' ty
    then return (ty, TmAnn (TmVar var) ty)
    else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show ty' ++ " in " ++ show (TmVar var)
tcTm env (TmLInj tm) (BTySum lTy rTy) = do
  rst <- tcTm env tm lTy
  let tm' = snd rst
  let rstTy = BTySum lTy rTy
  return (rstTy , TmAnn (TmLInj tm') rstTy)
tcTm env (TmRInj tm) (BTySum lTy rTy) = do
  rst <- tcTm env tm rTy
  let tm' = snd rst
  let rstTy = BTySum lTy rTy
  return (rstTy , TmAnn (TmRInj tm') rstTy)
tcTm env (TmPair lhs rhs) (BTyProd lTy rTy) = do
  lRst <- tcTm env lhs lTy
  rRst <- tcTm env rhs rTy
  let lhs' = snd lRst
  let rhs' = snd rRst
  let oType = (BTyProd lTy rTy)
  return (oType , (TmAnn (TmPair lhs' rhs') oType))
tcTm env (TmIsoApp iso tm) ty = do
  isoRst <- tiIso env iso
  let isoTy = fst isoRst
  let iso' = snd isoRst
  pair <- tcRator iso' isoTy
  let randTy = fst pair
  let bodyTy = snd pair
  rst <- tcTm env tm randTy
  let argType = fst rst
  let tm' = snd rst
  if typeEqual env bodyTy ty
    then return (bodyTy , (TmAnn (TmIsoApp iso' tm') bodyTy))
    else Left $ moduleName ++ "The operand " ++ show tm ++ " has the type " ++ show argType ++ " , expect " ++ show randTy
tcTm env (TmLet pat rhs body) ty = do
  rhsRst <- tiTm env rhs
  let rhsTy = fst rhsRst
  let rhs' = snd rhsRst
  newEnv <- extPatEnv env pat rhsTy
  bodyRst <- tcTm newEnv body ty
  let body' = snd bodyRst
  return (ty , TmAnn (TmLet pat rhs' body') ty)
tcTm env (TmAnn tm ty) ty' =
  if typeEqual env ty ty'
  then tcTm env tm ty'
  else Left $ moduleName ++ "Expect " ++ show tm ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
tcTm _ tm ty = Left $ moduleName ++ "Expect " ++ show tm ++ " to have type " ++ show ty

{---------- Bidirectional type checking for Isos ----------}
tiIso :: TypEnv -> Iso -> Result (IsoType, Iso)
tiIso env (IsoValue pairs) = do
  otype <- tiIsoPairs env pairs
  let ov = IsoAnn (IsoValue pairs) otype
  return (otype , ov)
tiIso env (IsoVar var) = do
  otype <- applyIsoEnv env var
  let ov = IsoAnn (IsoVar var) otype
  return (otype , ov)
tiIso env (IsoLam var vLhsTy vRhsTy body) = do
  let newEnv = extIsoEnv env var (ITyBase vLhsTy vRhsTy)
  rst <- tiIso newEnv body
  let bodyTy = fst rst
  let body' = snd rst
  let otype = ITyFun vLhsTy vRhsTy bodyTy
  let ov = IsoAnn (IsoLam var vLhsTy vRhsTy body') otype
  return (otype , ov)
tiIso env (IsoApp rator rand) = do
  ratorRst <- tiIso env rator
  let ratorTy = fst ratorRst
  let rator' = snd ratorRst
  randRst <- tiIso env rand
  let randTy = fst randRst
  let rand' = snd randRst
  case (ratorTy , randTy) of
    (ITyFun lhsTy rhsTy bodyTy, ITyBase randLhsTy randRhsTy) ->
      if typeEqual env lhsTy randLhsTy && typeEqual env rhsTy randRhsTy
      then return (bodyTy , IsoAnn (IsoApp rator' rand') bodyTy)
      else Left $ moduleName ++ "Expect " ++ show rator ++ " and " ++ show rand  ++ " to have matched type!"
    (_, _) -> Left $ moduleName ++ "Expect " ++ show rator ++ " to have the type (Iso -> Iso)!"
tiIso _ (IsoFix _ _) = Left $ moduleName ++ "IsoFix is not supported yet!"
tiIso _ (IsoAnn _ _) = Left $ moduleName ++ "IsoAnn is an internal node!"

tiIsoPairs :: TypEnv -> [(Value, Exp)] -> Result IsoType
tiIsoPairs _ [] = Left $ moduleName ++ "There must be at least one pair of values in an iso, given zero!"
tiIsoPairs env (hd:tl) = do
  ty <- tiIsoPair env hd
  let lhsTy = fst ty
  let rhsTy = snd ty
  tcIsoPairs env tl lhsTy rhsTy

tcIsoPairs :: TypEnv -> [(Value, Exp)] -> BaseType -> BaseType -> Result IsoType
tcIsoPairs _ [] lhsTy rhsTy = return $ ITyBase lhsTy rhsTy
tcIsoPairs env (hd:tl) lhsTy rhsTy = do
  rst <- tcIsoPair env hd lhsTy rhsTy
  let lhsTy' = fst rst
  let rhsTy' = snd rst
  tcIsoPairs env tl lhsTy' rhsTy'

tiIsoPair :: TypEnv -> (Value, Exp) -> Result (BaseType, BaseType)
tiIsoPair env (lhs, rhs) = do
  lRst <- tiValue env lhs
  let lTy = fst $ fst lRst
  let lBinds = snd lRst
  let newEnv = extMultiBaseEnv env lBinds
  rTy <- tiExp newEnv rhs
  return (lTy , rTy)

tcIsoPair :: TypEnv -> (Value, Exp) -> BaseType -> BaseType -> Result (BaseType, BaseType)
tcIsoPair env (lhs , rhs) lTy rTy = do
  lRst <- tcVal env lhs lTy
  let lTy' = fst $ fst lRst
  let lBinds = snd lRst
  let newEnv = extMultiBaseEnv env lBinds
  rTy' <- tcExp newEnv rhs rTy
  return (lTy' , rTy')

{---------- Bidirectional type checking for Values -----------}
-- Return the type of the given value, the type annotated value, and all pattern
-- variables and the corresponding type in this value.
tiValue :: TypEnv -> Value -> Result ((BaseType, Value), [(String, BaseType)])
tiValue _ ValUnit = return ((BTyUnit, ValAnn ValUnit BTyUnit) , [])
tiValue _ (ValInt n) = return ((BTyInt, ValAnn (ValInt n) BTyInt) , [])
tiValue _ (ValVar var) = Left $ moduleName ++ "Type annotation is required for a single pattern var " ++ var ++ "!"
tiValue _ (ValLInj v) = Left $ moduleName ++ "Type annotation is required for a Left value " ++ show v ++ "!"
tiValue _ (ValRInj v) = Left $ moduleName ++ "Type annotation is required for a Right value " ++ show v ++ "!"
tiValue env (ValPair l r) = do
  lRst <- tiValue env l
  rRst <- tiValue env r
  let lTy = fst $ fst lRst
  let rTy = fst $ fst rRst
  let l' = snd $ fst lRst
  let r' = snd $ fst rRst
  let otype = BTyProd lTy rTy
  let ov = ValAnn (ValPair l' r') otype
  let lBinds = snd lRst
  let rBinds = snd rRst
  return ((otype , ov), lBinds ++ rBinds)
tiValue env (ValAnn v ty) = tcVal env v ty

tcVal :: TypEnv -> Value -> BaseType -> Result ((BaseType, Value), [(String, BaseType)])
tcVal env ValUnit ty =
  if typeEqual env BTyUnit ty
  then return ((BTyUnit , ValAnn ValUnit BTyUnit) , [])
  else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show BTyUnit ++ " in " ++ show TmUnit
tcVal env (ValInt n) ty =
  if typeEqual env BTyInt ty
  then return ((BTyInt , ValAnn (ValInt n) BTyInt) , [])
  else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show BTyInt ++ " in " ++ show (TmInt n)
-- special case, Var is a pattern
tcVal _ (ValVar var) ty = return ((ty, ValAnn (ValVar var) ty), [(var , ty)])
tcVal env (ValLInj tm) (BTySum lTy rTy) = do
  rst <- tcVal env tm lTy
  let lTy' = fst $ fst rst
  let tm' = snd $ fst rst
  let otype = BTySum lTy' rTy
  let ov = ValAnn (ValLInj tm') otype
  let binds = snd rst
  return ((otype, ov) , binds)
tcVal env (ValRInj tm) (BTySum lTy rTy) = do
  rst <- tcVal env tm rTy
  let rTy' = fst $ fst rst
  let tm' = snd $ fst rst
  let otype = BTySum lTy rTy'
  let ov = ValAnn (ValRInj tm') otype
  let binds = snd rst
  return ((otype, ov) , binds)
tcVal env (ValPair lhs rhs) (BTyProd lTy rTy) = do
  lRst <- tcVal env lhs lTy
  rRst <- tcVal env rhs rTy
  let lTy' = fst $ fst lRst
  let rTy' = fst $ fst rRst
  let lhs' = snd $ fst lRst
  let rhs' = snd $ fst rRst
  let otype = BTyProd lTy' rTy'
  let ov = ValAnn (ValPair lhs' rhs') otype
  let lBinds = snd lRst
  let rBinds = snd rRst
  return ((otype, ov) , lBinds ++ rBinds)
tcVal env (ValAnn v ty) ty' =
  if typeEqual env ty ty'
  then tcVal env v ty'
  else Left $ moduleName ++ "Expect " ++ show v ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
tcVal _ tm ty = Left $ moduleName ++ "Expect " ++ show tm ++ " to have type " ++ show ty

{-- Bidirectional type checking for Values (Non-pattern) --}
-- Return the type of the given value.
tiValNoPat :: TypEnv -> Value -> Result (BaseType , Value)
tiValNoPat _ ValUnit = return (BTyUnit , ValAnn ValUnit BTyUnit)
tiValNoPat _ (ValInt n) = return (BTyInt , ValAnn (ValInt n) BTyInt)
tiValNoPat env (ValVar var) = do
  ty <- applyBaseEnv env var
  return (ty , ValAnn (ValVar var) ty)
tiValNoPat _ (ValLInj v) =
  Left $ moduleName ++ "Type annotation is required for a Left value " ++ show v ++ "!"
tiValNoPat _ (ValRInj v) =
  Left $ moduleName ++ "Type annotation is required for a Right value " ++ show v ++ "!"
tiValNoPat env (ValPair l r) = do
  lRst <- tiValNoPat env l
  rRst <- tiValNoPat env r
  let lTy = fst lRst
  let rTy = fst rRst
  let l' = snd lRst
  let r' = snd rRst
  let otype = BTyProd lTy rTy
  let ov = ValAnn (ValPair l' r') otype
  return (otype, ov)
tiValNoPat env (ValAnn v ty) = tcValNoPat env v ty

tcValNoPat :: TypEnv -> Value -> BaseType -> Result (BaseType , Value)
tcValNoPat env ValUnit ty =
  if typeEqual env BTyUnit ty
  then return (BTyUnit , ValAnn ValUnit BTyUnit)
  else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show BTyUnit ++ " in " ++ show TmUnit
tcValNoPat env (ValInt n) ty =
  if typeEqual env BTyInt ty
  then return (BTyInt , ValAnn (ValInt n) BTyInt)
  else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show BTyInt ++ " in " ++ show (TmInt n)
tcValNoPat env (ValVar var) ty = do
  ty' <- applyBaseEnv env var
  if typeEqual env ty' ty
    then return (ty , ValAnn (ValVar var) ty)
    else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show ty' ++ " in " ++ show (ValVar var)
tcValNoPat env (ValLInj tm) (BTySum lTy rTy) = do
  rst <- tcValNoPat env tm lTy
  let lTy' = fst rst
  let tm' = snd rst
  let otype = BTySum lTy' rTy
  let ov = ValAnn (ValLInj tm') otype
  return (otype , ov)
tcValNoPat env (ValRInj tm) (BTySum lTy rTy) = do
  rst <- tcValNoPat env tm rTy
  let rTy' = fst rst
  let tm' = snd rst
  let otype = BTySum lTy rTy'
  let ov = ValAnn (ValLInj tm') otype
  return (otype , ov)
tcValNoPat env (ValPair lhs rhs) (BTyProd lTy rTy) = do
  lRst <- tcValNoPat env lhs lTy
  rRst <- tcValNoPat env rhs rTy
  let lTy' = fst lRst
  let rTy' = fst rRst
  let lhs' = snd lRst
  let rhs' = snd lRst
  let otype = BTyProd lTy' rTy'
  let ov = ValAnn (ValPair lhs' rhs') otype
  return (otype , ov)
tcValNoPat env (ValAnn v ty) ty' =
  if typeEqual env ty ty'
  then tcValNoPat env v ty'
  else Left $ moduleName ++ "Expect " ++ show v ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
tcValNoPat _ tm ty =
  Left $ moduleName ++ "Expect " ++ show tm ++ " to have type " ++ show ty

{---------- Bidirectional type checking for Exps ----------}
tiExp :: TypEnv -> Exp -> Result BaseType
tiExp env (ExpVal val) = do
  rst <- tiValNoPat env val
  return $ fst rst
tiExp env (ExpLet pat iso pat' body) = do
  isoRst <- tiIso env iso
  let isoTy = fst isoRst
  let iso' = snd isoRst
  pair <- tcRator iso' isoTy
  let randTy = fst pair
  let bodyTy = snd pair
  patTy <- tcRhsPat env randTy pat'
  newEnv <- extPatEnv env pat bodyTy
  tiExp newEnv body

tcExp :: TypEnv -> Exp -> BaseType -> Result BaseType
tcExp env (ExpVal val) ty = do
  rst <- tcValNoPat env val ty
  return $ fst rst
tcExp env (ExpLet pat iso pat' body) ty = do
  isoRst <- tiIso env iso
  let isoTy = fst isoRst
  let iso' = snd isoRst
  pair <- tcRator iso' isoTy
  let randTy = fst pair
  let bodyTy = snd pair
  patTy <- tcRhsPat env randTy pat'
  newEnv <- extPatEnv env pat bodyTy
  tcExp newEnv body ty

tcRator :: (Show a) => a -> IsoType -> Result (BaseType , BaseType)
tcRator rator ratorTy =
  case ratorTy of
    ITyBase lT rT -> return (lT , rT)
    _ -> Left $ moduleName ++ "The operator " ++ show rator ++ " should be an IsoBase, got " ++ show ratorTy

tcRhsPat :: TypEnv -> BaseType -> Pattern -> Result BaseType
tcRhsPat env ty (PtSingleVar var) = do
  ty' <- applyBaseEnv env var
  if typeEqual env ty ty'
    then return ty
    else Left $ moduleName ++ "Invalid pattern type " ++ show ty' ++ ", expect " ++ show ty
tcRhsPat env ty (PtMultiVar (var : [])) = do
  ty' <- applyBaseEnv env var
  if typeEqual env ty ty'
    then return ty
    else Left $ moduleName ++ "Invalid pattern type " ++ show ty' ++ ", expect " ++ show ty
tcRhsPat env ty (PtMultiVar (var : vars)) = do
  hd <- applyBaseEnv env var
  tl <- tcRhsPat env ty (PtMultiVar vars)
  let ty' = (BTyProd hd tl)
  if typeEqual env ty ty'
    then return (BTyProd hd tl)
    else Left $ moduleName ++ "Invalid pattern type " ++ show ty' ++ ", expect " ++ show ty
tcRhsPat _ _ pat = Left $ moduleName ++ "Invalid pattern " ++ show pat

{-------------- Helper functions --------------}
typeEqual :: TypEnv -> BaseType -> BaseType -> Bool
typeEqual _ ty ty' = (ty == ty')

applyBaseEnv :: TypEnv -> String -> Result BaseType
applyBaseEnv env var = case (lookup var env) of
  Just (Left bTy) -> return bTy
  _ -> Left $ moduleName ++ "Cannot find the base type variable " ++ show var

applyIsoEnv :: TypEnv -> String -> Result IsoType
applyIsoEnv env var = case (lookup var env) of
  Just (Right iTy) -> return iTy
  _ -> Left $ moduleName ++ "Cannot find the iso variable " ++ show var

extIsoEnv :: TypEnv -> String -> IsoType -> TypEnv
extIsoEnv env var ty = (var, Right ty) : env

extBaseEnv :: TypEnv -> String -> BaseType -> TypEnv
extBaseEnv env var ty = (var , Left ty) : env

extMultiBaseEnv :: TypEnv -> [(String , BaseType)] -> TypEnv
extMultiBaseEnv env binds = map f binds ++ env where
  f = \x -> (fst x, Left $ snd x)

extPatEnv :: TypEnv -> Pattern -> BaseType -> Result TypEnv
extPatEnv env (PtSingleVar var) ty = return $ extBaseEnv env var ty
extPatEnv env (PtMultiVar vars) ty = extend env vars ty where
  extend env' (var : []) ty' = return $ extBaseEnv env' var ty'
  extend env' (var : vars') (BTyProd lhsTy rhsTy) =
    extend (extBaseEnv env' var lhsTy) vars' rhsTy
  extend _ _ _ = Left $ moduleName ++ "The number of pattern variables " ++ show vars ++ " don't match the type " ++ show ty
