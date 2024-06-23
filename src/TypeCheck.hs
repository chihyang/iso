module TypeCheck (typeInfer, typeInferDefsPg, typeInferEnv) where

import Syntax
import Debug.Trace (trace)

moduleName :: String
moduleName = "Type Check: "

{---------- Type infer declarations ----------}
typeInferDefsPg :: (Definitions, Program) -> Result (Definitions, Program)
typeInferDefsPg (defs, pgm) = do
  env <- collectTypes defs
  defs' <- checkDefs env defs
  pgm' <- typeInferEnv env pgm
  return (defs', pgm')

-- Given a sorted list of declarations, return a list of possibly type
-- annotated isos.
collectTypes :: Definitions -> Result TypEnv
collectTypes [] = return emptyTypEnv
collectTypes ((var, (IsoAnn _ ty)):ds) = do
  env <- collectTypes ds
  return $ extIsoEnv env var ty
collectTypes ((var, d):_) = Left $ "Invalid definition: " ++ var ++ " = " ++ show d

checkDefs :: TypEnv -> Definitions -> Result Definitions
checkDefs _ [] = return []
checkDefs env ((var,(IsoAnn d ty)):ds) = do
  defs <- checkDefs env ds
  (ty', d') <- tcIso env d ty
  return $ (var,(IsoAnn d' ty')):defs
checkDefs _ ((var,_):_) = Left $ moduleName ++ var ++ " doesn't have a type declaration!"

{---------- Type infer program ----------}
typeInfer :: Program -> Result Program
typeInfer pg = typeInferEnv emptyTypEnv pg

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
tiTm _ TmEmpty = Left $ moduleName ++ "Type annotation is required for empty list!"
tiTm env (TmCons v vs) = do
  (ty, v') <- tiTm env v
  (_, vs') <- tcTm env vs (BTyList ty)
  return (BTyList ty, TmAnn (TmCons v' vs') (BTyList ty))
tiTm env (TmVar var) = do
  ty <- applyBaseEnv env var
  return (ty , TmAnn (TmVar var) ty)
tiTm _ (TmLInj tm) = Left $ moduleName ++ "Type annotation is required for the term " ++ show (TmLInj tm)
tiTm _ (TmRInj tm) = Left $ moduleName ++ "Type annotation is required for the term " ++ show (TmLInj tm)
tiTm env (TmPair l r) = do
  (lTy, lTm) <- tiTm env l
  (rTy, rTm) <- tiTm env r
  let oType = (BTyProd lTy rTy)
  return (oType , TmAnn (TmPair lTm rTm) oType)
tiTm env (TmIsoApp iso tm) = do
  (isoTy, iso') <- tiIso env iso
  (randTy, bodyTy) <- tcRator iso' isoTy
  (_, tm') <- tcTm env tm randTy
  return (bodyTy , (TmAnn (TmIsoApp iso' tm') bodyTy))
tiTm env (TmLet pat rhs body) = do
  (rhsTy, rhs') <- tiTm env rhs
  newEnv <- extPatEnv env pat rhsTy
  (bodyTy, body') <- tiTm newEnv body
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
tcTm _ TmEmpty (BTyList ty) = return (BTyList ty, TmAnn TmEmpty (BTyList ty))
tcTm env (TmCons v vs) (BTyList ty) = do
  (_, v') <- tcTm env v ty
  (_, vs') <- tcTm env vs (BTyList ty)
  return (BTyList ty, TmAnn (TmCons v' vs') (BTyList ty))
tcTm env (TmVar var) ty = do
  ty' <- applyBaseEnv env var
  if typeEqual env ty' ty
    then return (ty, TmAnn (TmVar var) ty)
    else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show ty' ++ " in " ++ show (TmVar var)
tcTm env (TmLInj tm) (BTySum lTy rTy) = do
  (_, tm') <- tcTm env tm lTy
  let rstTy = BTySum lTy rTy
  return (rstTy , TmAnn (TmLInj tm') rstTy)
tcTm env (TmRInj tm) (BTySum lTy rTy) = do
  (_, tm') <- tcTm env tm rTy
  let rstTy = BTySum lTy rTy
  return (rstTy , TmAnn (TmRInj tm') rstTy)
tcTm env (TmPair lhs rhs) (BTyProd lTy rTy) = do
  (_, lhs') <- tcTm env lhs lTy
  (_, rhs') <- tcTm env rhs rTy
  let oType = (BTyProd lTy rTy)
  return (oType , (TmAnn (TmPair lhs' rhs') oType))
tcTm env (TmIsoApp iso tm) ty = do
  (isoTy, iso') <- tiIso env iso
  (randTy, bodyTy) <- tcRator iso' isoTy
  (argType, tm') <- tcTm env tm randTy
  if typeEqual env bodyTy ty
    then return (bodyTy , (TmAnn (TmIsoApp iso' tm') bodyTy))
    else Left $ moduleName ++ "The operand " ++ show tm ++ " has the type " ++ show argType ++
         " , expect " ++ show randTy
tcTm env (TmLet pat rhs body) ty = do
  (rhsTy, rhs') <- tiTm env rhs
  newEnv <- extPatEnv env pat rhsTy
  (_, body') <- tcTm newEnv body ty
  return (ty , TmAnn (TmLet pat rhs' body') ty)
tcTm env (TmAnn tm ty) ty' =
  if typeEqual env ty ty'
  then tcTm env tm ty'
  else Left $ moduleName ++ "Expect " ++ show tm ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
tcTm _ tm ty = Left $ moduleName ++ "Expect " ++ show tm ++ " to have type " ++ show ty

{---------- Bidirectional type checking for Isos ----------}
tiIso :: TypEnv -> Iso -> Result (IsoType, Iso)
tiIso env (IsoValue pairs) = do
  (otype,pairs') <- tiIsoPairs env pairs
  let ov = IsoAnn (IsoValue pairs') otype
  return (otype , ov)
tiIso env (IsoVar var) = do
  otype <- applyIsoEnv env var
  let ov = IsoAnn (IsoVar var) otype
  return (otype , ov)
tiIso env (IsoLam var vLhsTy vRhsTy body) = do
  let newEnv = extIsoEnv env var (ITyBase vLhsTy vRhsTy)
  (bodyTy, body') <- tiIso newEnv body
  let otype = ITyFun vLhsTy vRhsTy bodyTy
  let ov = IsoAnn (IsoLam var vLhsTy vRhsTy body') otype
  return (otype , ov)
tiIso env (IsoApp rator rand) = do
  (ratorTy, rator') <- tiIso env rator
  (randTy, rand') <- tiIso env rand
  case (ratorTy , randTy) of
    (ITyFun lhsTy rhsTy bodyTy, ITyBase randLhsTy randRhsTy) ->
      if typeEqual env lhsTy randLhsTy && typeEqual env rhsTy randRhsTy
      then return (bodyTy , IsoAnn (IsoApp rator' rand') bodyTy)
      else Left $ moduleName ++ "Expect " ++ show rator ++ " and " ++ show rand  ++ " to have matched type!"
    (_, _) -> Left $ moduleName ++ "Expect " ++ show rator ++ " to have the type (Iso -> Iso)!"
-- TODO: structural recursion check
tiIso env (IsoFix var lhs rhs body) = do
  let newEnv = extIsoEnv env var (ITyBase lhs rhs)
  (bodyTy, body') <- tiIso newEnv body
  let ov = IsoAnn (IsoFix var lhs rhs body') bodyTy
  return (bodyTy , ov)
tiIso env (IsoAnn iso ty) = tcIso env iso ty

tcIso :: TypEnv -> Iso -> IsoType -> Result (IsoType, Iso)
tcIso env (IsoValue pairs) (ITyBase lhsTy rhsTy) = do
  (otype,pairs') <- tcIsoPairs env pairs lhsTy rhsTy
  let ov = IsoAnn (IsoValue pairs') otype
  return (otype , ov)
tcIso env (IsoVar var) ty = do
  ty' <- applyIsoEnv env var
  if isoTypeEqual env ty' ty
    then return (ty, IsoAnn (IsoVar var) ty)
    else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show ty' ++ " in " ++ show (IsoVar var)
tcIso env (IsoLam var vLhsTy vRhsTy body) ty =
  case ty of
    ITyFun vLhsTy' vRhsTy' bodyTy
      | typeEqual env vLhsTy vLhsTy' && typeEqual env vRhsTy vRhsTy' ->
        do let newEnv = extIsoEnv env var (ITyBase vLhsTy vRhsTy)
           (bodyTy', body') <- tcIso newEnv body bodyTy
           let otype = ITyFun vLhsTy vRhsTy bodyTy'
           let ov = IsoAnn (IsoLam var vLhsTy vRhsTy body') otype
           return (otype , ov)
    _ -> Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show (IsoLam var vLhsTy vRhsTy body)
tcIso env (IsoApp rator rand) ty = do
  (ratorTy, rator') <- tiIso env rator
  case ratorTy of
    ITyFun lhsTy rhsTy bodyTy
      | isoTypeEqual env bodyTy ty ->
        do
          (_, rand') <- tcIso env rand (ITyBase lhsTy rhsTy)
          return $ (ty, (IsoAnn (IsoApp rator' rand') ty))
    _ -> Left $ moduleName ++ "Expect " ++ show rator ++ " to have the type (Iso -> Iso)!"
-- TODO: structural recursion check
tcIso env (IsoFix var lhs rhs body) ty = do
  let newEnv = extIsoEnv env var (ITyBase lhs rhs)
  (bodyTy, body') <- tcIso newEnv body ty
  let ov = IsoAnn (IsoFix var lhs rhs body') bodyTy
  return (bodyTy , ov)
tcIso env (IsoAnn iso ty) ty' | isoTypeEqual env ty ty' = tcIso env iso ty'
tcIso _ (IsoAnn iso ty) ty' =
  Left $ moduleName ++ "IsoAnn " ++ show iso ++ " has two different type declarations: " ++
  show ty ++ ", " ++ show ty'
tcIso _ iso ty =
  Left $ moduleName ++ "IsoAnn " ++ show iso ++ " has incorrect type: " ++ show ty

tiIsoPairs :: TypEnv -> [(Value, Exp)] -> Result (IsoType, [(Value, Exp)])
tiIsoPairs _ [] = Left $ moduleName ++ "There must be at least one pair of values in an iso, given zero!"
tiIsoPairs env (hd:tl) = do
  ((lhsTy,rhsTy),(v,e)) <- tiIsoPair env hd
  (ty,tl') <- tcIsoPairs env tl lhsTy rhsTy
  return (ty,(v,e):tl')

tcIsoPairs :: TypEnv -> [(Value, Exp)] -> BaseType -> BaseType -> Result (IsoType, [(Value, Exp)])
tcIsoPairs _ [] lhsTy rhsTy = return $ (ITyBase lhsTy rhsTy,[])
tcIsoPairs env (hd:tl) lhsTy rhsTy = do
  ((lhsTy',rhsTy'),(v,e)) <- tcIsoPair env hd lhsTy rhsTy
  (ty,tl') <- tcIsoPairs env tl lhsTy' rhsTy'
  return $ (ty,(v,e):tl')

tiIsoPair :: TypEnv -> (Value, Exp) -> Result ((BaseType, BaseType), (Value, Exp))
tiIsoPair env (lhs, rhs) = do
  ((lTy,lhs'),lBinds) <- tiValue env lhs
  let newEnv = extMultiBaseEnv env lBinds
  (rTy,rhs') <- tiExp newEnv rhs
  return ((lTy,rTy),(lhs',rhs'))

tcIsoPair :: TypEnv -> (Value, Exp) -> BaseType -> BaseType -> Result ((BaseType, BaseType), (Value, Exp))
tcIsoPair env (lhs,rhs) lTy rTy = do
  ((lTy',lhs'),lBinds) <- tcVal env lhs lTy
  let newEnv = extMultiBaseEnv env lBinds
  (rTy',rhs') <- tcExp newEnv rhs rTy
  return ((lTy',rTy'),(lhs',rhs'))

{---------- Bidirectional type checking for Values -----------}
-- Return the type of the given value, the type annotated value, and all pattern
-- variables and the corresponding type in this value.
tiValue :: TypEnv -> Value -> Result ((BaseType, Value), [(String, BaseType)])
tiValue _ ValUnit = return ((BTyUnit, ValAnn ValUnit BTyUnit) , [])
tiValue _ (ValInt n) = return ((BTyInt, ValAnn (ValInt n) BTyInt) , [])
tiValue _ ValEmpty = Left $ moduleName ++ "Type annotation is required for empty list!"
tiValue env (ValCons v vs) = do
  ((ty, v'), vars) <- tiValue env v
  ((_, vs'), vars') <- tcVal env vs (BTyList ty)
  return ((BTyList ty, ValAnn (ValCons v' vs') (BTyList ty)), vars ++ vars')
tiValue _ (ValVar var) = Left $ moduleName ++ "Type annotation is required for a single pattern var " ++ var ++ "!"
tiValue _ (ValLInj v) = Left $ moduleName ++ "Type annotation is required for a Left value " ++ show v ++ "!"
tiValue _ (ValRInj v) = Left $ moduleName ++ "Type annotation is required for a Right value " ++ show v ++ "!"
tiValue env (ValPair l r) = do
  ((lTy,l'),lBinds) <- tiValue env l
  ((rTy,r'),rBinds) <- tiValue env r
  let otype = BTyProd lTy rTy
  let ov = ValAnn (ValPair l' r') otype
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
tcVal _ ValEmpty (BTyList ty) = return (((BTyList ty), ValAnn ValEmpty (BTyList ty)) , [])
tcVal env (ValCons v vs) (BTyList ty) = do
  ((_, v') , vars) <- tcVal env v ty
  ((_, vs') , vars') <- tcVal env vs (BTyList ty)
  return (((BTyList ty), ValAnn (ValCons v' vs') (BTyList ty)) , vars ++ vars')
-- special case, Var is a pattern
tcVal _ (ValVar var) ty = return ((ty, ValAnn (ValVar var) ty), [(var , ty)])
tcVal env (ValLInj tm) (BTySum lTy rTy) = do
  ((lTy',tm'),binds) <- tcVal env tm lTy
  let otype = BTySum lTy' rTy
  let ov = ValAnn (ValLInj tm') otype
  return ((otype, ov) , binds)
tcVal env (ValRInj tm) (BTySum lTy rTy) = do
  ((rTy',tm'),binds) <- tcVal env tm rTy
  let otype = BTySum lTy rTy'
  let ov = ValAnn (ValRInj tm') otype
  return ((otype, ov) , binds)
tcVal env (ValPair lhs rhs) (BTyProd lTy rTy) = do
  ((lTy',lhs'),lBinds) <- tcVal env lhs lTy
  ((rTy',rhs'),rBinds) <- tcVal env rhs rTy
  let otype = BTyProd lTy' rTy'
  let ov = ValAnn (ValPair lhs' rhs') otype
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
tiValNoPat _ ValEmpty = Left $ moduleName ++ "Type annotation is required for empty list!"
tiValNoPat env (ValCons v vs) = do
  (ty, v') <- tiValNoPat env v
  (_, vs') <- tcValNoPat env vs (BTyList ty)
  return (BTyList ty, ValAnn (ValCons v' vs') (BTyList ty))
tiValNoPat env (ValVar var) = do
  ty <- applyBaseEnv env var
  return (ty , ValAnn (ValVar var) ty)
tiValNoPat _ (ValLInj v) =
  Left $ moduleName ++ "Type annotation is required for a Left value " ++ show v ++ "!"
tiValNoPat _ (ValRInj v) =
  Left $ moduleName ++ "Type annotation is required for a Right value " ++ show v ++ "!"
tiValNoPat env (ValPair l r) = do
  (lTy, l') <- tiValNoPat env l
  (rTy, r') <- tiValNoPat env r
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
tcValNoPat _ ValEmpty (BTyList ty) = return (BTyList ty , ValAnn ValEmpty (BTyList ty))
tcValNoPat env (ValCons v vs) (BTyList ty) = do
  (_, v') <- tcValNoPat env v ty
  (_, vs') <- tcValNoPat env vs (BTyList ty)
  return (BTyList ty , ValAnn (ValCons v' vs') (BTyList ty))
tcValNoPat env (ValVar var) ty = do
  ty' <- applyBaseEnv env var
  if typeEqual env ty' ty
    then return (ty , ValAnn (ValVar var) ty)
    else Left $ moduleName ++ "Expect " ++ show ty ++ ", got " ++ show ty' ++ " in " ++ show (ValVar var)
tcValNoPat env (ValLInj tm) (BTySum lTy rTy) = do
  (_, tm') <- tcValNoPat env tm lTy
  let otype = BTySum lTy rTy
  let ov = ValAnn (ValLInj tm') otype
  return (otype , ov)
tcValNoPat env (ValRInj tm) (BTySum lTy rTy) = do
  (_, tm') <- tcValNoPat env tm rTy
  let otype = BTySum lTy rTy
  let ov = ValAnn (ValRInj tm') otype
  return (otype , ov)
tcValNoPat env (ValPair lhs rhs) (BTyProd lTy rTy) = do
  (_, lhs') <- tcValNoPat env lhs lTy
  (_, rhs') <- tcValNoPat env rhs rTy
  let otype = BTyProd lTy rTy
  let ov = ValAnn (ValPair lhs' rhs') otype
  return (otype , ov)
tcValNoPat env (ValAnn v ty) ty' =
  if typeEqual env ty ty'
  then tcValNoPat env v ty'
  else Left $ moduleName ++ "Expect " ++ show v ++ " to have type " ++ show ty ++ ", conflict with " ++ show ty'
tcValNoPat _ tm ty =
  Left $ moduleName ++ "Expect " ++ show tm ++ " to have type " ++ show ty

{---------- Bidirectional type checking for Exps ----------}
tiExp :: TypEnv -> Exp -> Result (BaseType, Exp)
-- tiExp env e | trace ("tiExp " ++ show env ++ " " ++ show e) False = undefined
tiExp env (ExpVal val) = do
  (ty,val') <- tiValNoPat env val
  return $ (ty,ExpVal val')
tiExp env (ExpLet pat iso pat' body) = do
  (isoTy, iso') <- tiIso env iso
  (randTy, rstTy) <- tcRator iso' isoTy
  _ <- tcRhsPat env randTy pat'
  newEnv <- extPatEnv env pat rstTy
  (bodyTy',body') <- tiExp newEnv body
  return (bodyTy', (ExpLet pat iso' pat' body'))
tiExp env (ExpScale s e) = do
  (ty, e') <- tiExp env e
  return (ty, ExpScale s e')
tiExp _ (ExpPlus []) = Left $ moduleName ++ "Given zero operand, cannot infer the type of an ExpPlus expression!"
tiExp env (ExpPlus (e:es)) = do
  (lhsTy,e') <- tiExp env e
  (_,es') <- tcExps env es lhsTy
  return (lhsTy, ExpPlus (e':es'))

tcExps :: TypEnv -> [Exp] -> BaseType -> Result (BaseType, [Exp])
tcExps _ [] ty = return (ty, [])
tcExps env (e:es) ty = do
  (_,e') <- tcExp env e ty
  (_,es') <- tcExps env es ty
  return (ty, e':es')

tcExp :: TypEnv -> Exp -> BaseType -> Result (BaseType, Exp)
-- tcExp env e ty | trace ("tcExp " ++ show env ++ " " ++ show e ++ " " ++ show ty) False = undefined
tcExp env (ExpVal val) ty = do
  (_,val') <- tcValNoPat env val ty
  return $ (ty,ExpVal val')
tcExp env (ExpLet pat iso pat' body) ty = do
  (isoTy, iso') <- tiIso env iso
  (randTy, rstTy) <- tcRator iso' isoTy
  _ <- tcRhsPat env randTy pat'
  newEnv <- extPatEnv env pat rstTy
  (_, body') <- tcExp newEnv body ty
  return (ty, ExpLet pat iso' pat' body')
tcExp env (ExpScale s e) ty = do
  (_,e') <- tcExp env e ty
  return (ty,ExpScale s e')
tcExp env (ExpPlus es) ty = do
  (_,es') <- tcExps env es ty
  return (ty,ExpPlus es')

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
tcRhsPat env (BTyProd hd tl) (PtMultiVar (var : vars)) = do
  hd' <- applyBaseEnv env var
  tl' <- tcRhsPat env tl (PtMultiVar vars)
  let ty' = (BTyProd hd' tl')
  if typeEqual env (BTyProd hd tl) ty'
    then return (BTyProd hd tl)
    else Left $ moduleName ++ "Invalid pattern type " ++ show ty' ++ ", expect " ++ show (BTyProd hd tl)
tcRhsPat _ _ pat = Left $ moduleName ++ "Invalid pattern " ++ show pat

{-------------- Helper functions --------------}
isoTypeEqual :: TypEnv -> IsoType -> IsoType -> Bool
isoTypeEqual _ ty ty' = (ty == ty')

typeEqual :: TypEnv -> BaseType -> BaseType -> Bool
typeEqual _ ty ty' = (ty == ty')

emptyTypEnv :: TypEnv
emptyTypEnv = []

applyBaseEnv :: TypEnv -> String -> Result BaseType
-- applyBaseEnv env var | trace ("applyBaseEnv " ++ show env ++ " " ++ show var) False = undefined
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
-- extPatEnv env pat ty | trace ("extPatEnv " ++ show env ++ " " ++ show pat ++ " " ++ show ty) False = undefined
extPatEnv env (PtSingleVar var) ty = return $ extBaseEnv env var ty
extPatEnv env (PtMultiVar vars) ty = extend env vars ty where
  extend env' (var : []) ty' = return $ extBaseEnv env' var ty'
  extend env' (var : vars') (BTyProd lhsTy rhsTy) =
    extend (extBaseEnv env' var lhsTy) vars' rhsTy
  extend _ _ _ = Left $ moduleName ++ "The number of pattern variables " ++ show vars ++ " don't match the type " ++ show ty
