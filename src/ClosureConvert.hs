module ClosureConvert (closureConvert) where

import Data.Foldable
import RevealFix as RF
import Syntax
import Debug.Trace (trace)

moduleName :: String
moduleName = "ClosureConvert: "

closureConvert :: (Definitions, Program) -> Result (Definitions, Program)
closureConvert (defs, prgm) = do
  fvmap <- revealFix (defs, prgm)
  fix' <- convertFix fvmap
  defs' <- convertDefs fvmap (fix' ++ defs)
  prgm' <- convertProg fvmap prgm
  return (defs', prgm')

convertDefs :: FixMap -> Definitions -> Result Definitions
convertDefs fvmap defs = foldrM f [] defs where
  f (name, iso) r = do
    iso' <- convertIso fvmap iso
    return ((name, iso'):r)

convertProg :: FixMap -> Program -> Result Program
convertProg fvmap (PgTm tm) = PgTm <$> convertTerm fvmap tm
convertProg fvmap (PgIs iso) = PgIs <$> convertIso fvmap iso

convertFix :: FixMap -> Result Definitions
convertFix fvmap = foldrM f [] (toListFix fvmap) where
  f (IsoAnn (IsoFix var _ _ body) t,fvset) r =
    return $ (var,IsoAnn (genIso varTys body) (genType varTys t)):r where
    varTys = RF.toList fvset

    genType vts t' = foldr g t' vts
    g (_,ITyBase lTy rTy) r' = ITyFun lTy rTy r'
    g (v,t') _ = error $ moduleName ++ "Impossible case: free iso variable with higher order type: " ++
      show v ++ ", " ++ show t'

    genIso vts i = foldr h i vts
    h (v,ITyBase lTy rTy) b@(IsoAnn _ bTy) = IsoAnn (IsoLam v lTy rTy b) (ITyFun lTy rTy bTy)
    h (v,t') _ = error $ moduleName ++ "Impossible case: free iso variable with higher order type: " ++
      show v ++ ", " ++ show t'
  f (iso,_) _ = Left $ moduleName ++ "Impossible case: not a type annotated iso: " ++ show iso
convertIso :: FixMap -> Iso -> Result Iso
convertIso fvmap (IsoValue pairs) = IsoValue <$> convertPairs fvmap pairs
convertIso fvmap vt@(IsoAnn (IsoVar var) ty) = case lookupFixVar var fvmap of
  Just (_,fvset) -> return $ f (IsoVar var) (genType varTys ty) (reverse varTys) varTys where
    varTys = RF.toList fvset

    -- f b t vs rvs | trace ("f " ++ show b ++ " " ++ show t ++ " " ++ show vs ++ " " ++ show rvs) False = undefined
    f b t [] [] = IsoAnn b t
    f b t ((v,t'):varTys') (_:es) = f (IsoApp (IsoAnn b t) (IsoAnn (IsoVar v) t')) (genType es ty) varTys' es
    f _ _ _ _ = error $ moduleName ++ "Impossible case: a list has different length to its reverse"

    -- genType vts t' | trace ("genType " ++ show vts ++ " " ++ show t') False = undefined
    genType vts t' = foldr g t' vts
    g (_,ITyBase lTy rTy) r' = ITyFun lTy rTy r'
    g (v',t') _ = error $ moduleName ++ "Impossible case: free iso variable with higher order type: " ++
      show v' ++ ", " ++ show t'

  Nothing -> return vt
convertIso _ (IsoVar v) = Left $ moduleName ++ show v ++ " is not type annotated!"
convertIso fvmap (IsoApp rator rand) = liftA2 IsoApp (convertIso fvmap rator) (convertIso fvmap rand)
convertIso fvmap (IsoLam var lTy rTy body) = IsoLam var lTy rTy <$> convertIso fvmap body
convertIso fvmap fix@(IsoAnn (IsoFix var _ _ _) ty) = case lookupFix fix fvmap of
  Just fvset -> return $ f (IsoVar var) (genType varTys ty) (reverse varTys) varTys where
    varTys = RF.toList fvset

    -- f b t vs rvs | trace ("f " ++ show b ++ " " ++ show t ++ " " ++ show vs ++ " " ++ show rvs) False = undefined
    f b t [] [] = IsoAnn b t
    f b t ((v,t'):varTys') (_:es) = f (IsoApp (IsoAnn b t) (IsoAnn (IsoVar v) t')) (genType es ty) varTys' es
    f _ _ _ _ = error $ moduleName ++ "Impossible case: a list has different length to its reverse"

    -- genType vts t' | trace ("genType " ++ show vts ++ " " ++ show t') False = undefined
    genType vts t' = foldr g t' vts
    g (_,ITyBase lTy rTy) r' = ITyFun lTy rTy r'
    g (v',t') _ = error $ moduleName ++ "Impossible case: free iso variable with higher order type: " ++
      show v' ++ ", " ++ show t'
  _ -> Left $ moduleName ++ "IsoFix " ++ var ++ " not found!"
convertIso _ f@(IsoFix {}) = Left $ moduleName ++ show f ++ " is not type annotated!"
convertIso fvmap (IsoAnn iso ty) = flip IsoAnn ty <$> convertIso fvmap iso

convertPairs :: FixMap -> [(Value, Exp)] -> Result [(Value, Exp)]
convertPairs fvmap pairs = foldrM f [] pairs where
  f (v,e) r = do
    e' <- convertExp fvmap e
    return $ (v,e'):r

convertExp :: FixMap -> Exp -> Result Exp
convertExp _ v@(ExpVal _) = return v
convertExp fvmap (ExpLet pat iso pat' body) = do
  iso' <- convertIso fvmap iso
  body' <- convertExp fvmap body
  return (ExpLet pat iso' pat' body')
convertExp fvmap (ExpScale s e) = ExpScale s <$> convertExp fvmap e
convertExp fvmap (ExpPlus es) = ExpPlus <$> mapM (convertExp fvmap) es

convertTerm :: FixMap -> Term -> Result Term
convertTerm _ TmUnit = return TmUnit
convertTerm _ n@(TmInt _) = return n
convertTerm _ TmEmpty = return TmEmpty
convertTerm fvmap (TmCons l r) = liftA2 TmCons (convertTerm fvmap l) (convertTerm fvmap r)
convertTerm _ v@(TmVar _) = return v
convertTerm fvmap (TmLInj t) = TmLInj <$> convertTerm fvmap t
convertTerm fvmap (TmRInj t) = TmRInj <$> convertTerm fvmap t
convertTerm fvmap (TmPair l r) = liftA2 TmPair (convertTerm fvmap l) (convertTerm fvmap r)
convertTerm fvmap (TmIsoApp iso t) = liftA2 TmIsoApp (convertIso fvmap iso) (convertTerm fvmap t)
convertTerm fvmap (TmLet pat rhs body) = liftA2 (TmLet pat) (convertTerm fvmap rhs) (convertTerm fvmap body)
convertTerm fvmap (TmAnn t ty) = flip TmAnn ty <$> convertTerm fvmap t
