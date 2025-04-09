module Uniquify (uniquify) where

import Data.Foldable
import Syntax
import qualified Data.Map.Strict as Map
import Debug.Trace (trace)

type NameEnv = Map.Map String String
type NameRecord = Map.Map String Int

moduleName :: String
moduleName = "Uniquify: "

{--
Operations on name environment.
--}
newEnv :: NameEnv
newEnv = Map.empty

extendEnv :: NameEnv -> String -> String -> NameEnv
extendEnv table name name' = Map.insert name name' table

lookupEnv :: NameEnv -> String -> Result String
lookupEnv env name = case Map.lookup name env of
  (Just n) -> return n
  _ -> Left $ moduleName ++  "Unbound variable " ++ show name

{--
Operations on name table.
--}
newTable :: NameRecord
newTable = Map.empty

insertTable :: NameRecord -> String -> NameRecord
insertTable table name = case Map.lookup name table of
  Just n -> f (n+1)
  Nothing -> f 0
  where
  f n = if Map.member (name ++ "_" ++ show n) table
    then f (n+1)
    else Map.insert name n table

lookupTable :: NameRecord -> String -> Result String
lookupTable table name = case Map.lookup name table of
  (Just 0) -> return $ name
  (Just n) -> return $ name ++ "_" ++ show n
  _ -> Left $ moduleName ++ "Unbound variable " ++ show name

updateName :: String -> NameEnv -> NameRecord -> Result (String, NameEnv, NameRecord)
updateName name env table = do
  let table' = insertTable table name
  name' <- lookupTable table' name
  let env' = extendEnv env name name'
  return (name', env', table')

-- Make sure no two names are identical to each other
uniquify :: (Definitions, Program) -> Result (Definitions, Program)
uniquify (defs, prgm) = do
  (defs', env, table) <- uniquifyDefs defs newEnv newTable
  prgm' <- uniquifyProg prgm env table
  return (defs', prgm')

uniquifyNames :: [String] -> NameEnv -> NameRecord -> Result ([String], NameEnv, NameRecord)
uniquifyNames names env table = foldrM f ([], env, table) names where
  f name (names', env', table') = do
    (name', env'', table'') <- updateName name env' table'
    return (name':names', env'', table'')

uniquifyIsos :: [Iso] -> NameEnv -> NameRecord -> Result ([Iso], NameRecord)
uniquifyIsos isos env table = foldrM f ([], table) isos where
  f iso (isos', table') = do
    (iso', table'') <- uniquifyIso iso env table'
    return (iso':isos', table'')

uniquifyDefs :: Definitions -> NameEnv -> NameRecord -> Result (Definitions, NameEnv, NameRecord)
uniquifyDefs defs env table = do
  (names, env', table') <- uniquifyNames (map fst defs) env table
  (isos, table'') <- uniquifyIsos (map snd defs) env' table'
  return (zip names isos, env', table'')

uniquifyProg :: Program -> NameEnv -> NameRecord -> Result Program
uniquifyProg (PgTm tm) env table = do
  (tm', _) <- uniquifyTerm tm env table
  return $ PgTm tm'
uniquifyProg (PgIs iso) env table = do
  (iso', _) <- uniquifyIso iso env table
  return $ PgIs iso'

uniquifyIso :: Iso -> NameEnv -> NameRecord -> Result (Iso, NameRecord)
uniquifyIso (IsoValue pairs) env table = do
  (pairs', table') <- uniquifyPairs pairs env table
  return (IsoValue pairs', table')
uniquifyIso (IsoVar var) env table = do
  var' <- lookupEnv env var
  return (IsoVar var', table)
uniquifyIso (IsoLam var lTy rTy body) env table = do
  (var', env', table') <- updateName var env table
  (body', table'') <- uniquifyIso body env' table'
  return (IsoLam var' lTy rTy body', table'')
uniquifyIso (IsoApp lhs rhs) env table = do
  (lhs', table') <- uniquifyIso lhs env table
  (rhs', table'') <- uniquifyIso rhs env table'
  return (IsoApp lhs' rhs', table'')
uniquifyIso (IsoFix var lTy rTy body) env table = do
  (var', env', table') <- updateName var env table
  (body', table'') <- uniquifyIso body env' table'
  return (IsoFix var' lTy rTy body', table'')
uniquifyIso (IsoAnn iso ty) env table = do
  (iso', table') <- uniquifyIso iso env table
  return (IsoAnn iso' ty, table')

uniquifyPairs :: [(Value, Exp)] -> NameEnv -> NameRecord -> Result ([(Value, Exp)], NameRecord)
uniquifyPairs [] _ table = return ([], table)
uniquifyPairs (cl:cls) env table = do
  (cl', table') <- uniquifyPair cl env table
  (cls', table'') <- uniquifyPairs cls env table'
  return (cl':cls', table'')

uniquifyPair :: (Value, Exp) -> NameEnv -> NameRecord -> Result ((Value, Exp), NameRecord)
uniquifyPair (v, e) env table = do
  (v', env', table') <- uniquifyVal True v env table
  (e', table'') <- uniquifyExp e env' table'
  return ((v', e'), table'')

uniquifyVal :: Bool -> Value -> NameEnv -> NameRecord -> Result (Value, NameEnv, NameRecord)
uniquifyVal _ ValUnit env table = return (ValUnit, env, table)
uniquifyVal _ (ValInt n) env table = return ((ValInt n), env, table)
uniquifyVal isPat (ValSuc n) env table = do
  (n', env', table') <- uniquifyVal isPat n env table
  return (ValSuc n', env', table')
uniquifyVal _ ValEmpty env table = return (ValEmpty, env, table)
uniquifyVal isPat (ValCons l r) env table = do
  (l', env', table') <- uniquifyVal isPat l env table
  (r', env'', table'') <- uniquifyVal isPat r env' table'
  return (ValCons l' r', env'', table'')
uniquifyVal isPat (ValVar var) env table = if isPat
  then
  do (var', env', table') <- updateName var env table
     return (ValVar var', env', table')
  else
  do var' <- lookupEnv env var
     return (ValVar var', env, table)
uniquifyVal isPat (ValLInj v) env table = do
  (v', env', table') <- uniquifyVal isPat v env table
  return (ValLInj v', env', table')
uniquifyVal isPat (ValRInj v) env table = do
  (v', env', table') <- uniquifyVal isPat v env table
  return (ValRInj v', env', table')
uniquifyVal isPat (ValPair l r) env table = do
  (l', env', table') <- uniquifyVal isPat l env table
  (r', env'', table'') <- uniquifyVal isPat r env' table'
  return (ValPair l' r', env'', table'')
uniquifyVal isPat (ValAnn v t) env table = do
  (v', env', table') <- uniquifyVal isPat v env table
  return (ValAnn v' t, env', table')

uniquifyExp :: Exp -> NameEnv -> NameRecord -> Result (Exp, NameRecord)
uniquifyExp (ExpVal v) env table = do
  (v', _, table') <- uniquifyVal False v env table
  return (ExpVal v', table')
uniquifyExp (ExpLet pat iso pat' body) env table = do
  pat''' <- lookupPat env pat'
  (iso', table') <- uniquifyIso iso env table
  (pat'', env'', table'') <- uniquifyPat pat env table'
  (body', table''') <- uniquifyExp body env'' table''
  return (ExpLet pat'' iso' pat''' body', table''')
uniquifyExp (ExpScale s e) env table = do
  (e', table') <- uniquifyExp e env table
  return (ExpScale s e', table')
uniquifyExp (ExpPlus es) env table = do
  (es', table') <- foldrM f ([], table) es
  return (ExpPlus es', table')
  where
  f e (es', table') = do
    (e', table'') <- uniquifyExp e env table'
    return (e':es', table'')

lookupPat :: NameEnv -> Pattern -> Result Pattern
lookupPat env (PtSingleVar var) = do
  var' <- lookupEnv env var
  return (PtSingleVar var')
lookupPat env (PtMultiVar vars) = do
  vars' <- mapM (lookupEnv env) vars
  return (PtMultiVar vars')

uniquifyPat :: Pattern -> NameEnv -> NameRecord -> Result (Pattern, NameEnv, NameRecord)
uniquifyPat (PtSingleVar var) env table = do
  (var', env', table') <- updateName var env table
  return (PtSingleVar var', env', table')
uniquifyPat (PtMultiVar vars) env table = do
  (vars', env', table') <- foldrM f ([], env, table) vars
  return (PtMultiVar vars', env', table')
  where
  f v (vs', env', table') = do
    (v', env'', table'') <- updateName v env' table'
    return $ (v':vs', env'', table'')

uniquifyTerm :: Term -> NameEnv -> NameRecord -> Result (Term, NameRecord)
uniquifyTerm TmUnit _ table = return (TmUnit, table)
uniquifyTerm (TmInt n) _ table = return (TmInt n, table)
uniquifyTerm TmEmpty _ table = return (TmEmpty, table)
uniquifyTerm (TmCons l r) env table = do
  (l', table') <- uniquifyTerm l env table
  (r', table'') <- uniquifyTerm r env table'
  return (TmCons l' r', table'')
uniquifyTerm (TmVar var) env table = do
  var' <- lookupEnv env var
  return (TmVar var', table)
uniquifyTerm (TmLInj v) env table = do
  (v', table') <- uniquifyTerm v env table
  return (TmLInj v', table')
uniquifyTerm (TmRInj v) env table = do
  (v', table') <- uniquifyTerm v env table
  return (TmRInj v', table')
uniquifyTerm (TmPair l r) env table = do
  (l', table') <- uniquifyTerm l env table
  (r', table'') <- uniquifyTerm r env table'
  return (TmPair l' r', table'')
uniquifyTerm (TmIsoApp iso tm) env table = do
  (iso', table') <- uniquifyIso iso env table
  (tm', table'') <- uniquifyTerm tm env table'
  return (TmIsoApp iso' tm', table'')
uniquifyTerm (TmLet pat tm body) env table = do
  (tm', table') <- uniquifyTerm tm env table
  (pat', env', table'') <- uniquifyPat pat env table'
  (body', table''') <- uniquifyTerm body env' table''
  return (TmLet pat' tm' body', table''')
uniquifyTerm (TmAnn tm ty) env table = do
  (tm', table') <- uniquifyTerm tm env table
  return (TmAnn tm' ty, table')
