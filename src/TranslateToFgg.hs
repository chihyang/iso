module TranslateToFgg (transToFggPg) where

import Data.Bifunctor (bimap)
import Data.Foldable
import Data.List (nub)
import Control.Monad.Except
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (except)
import Control.Monad (void)
import Syntax
import qualified Data.Map.Strict as Map
import Perpl.Util.FGG
import Perpl.Util.Helpers (enumerate)
import Perpl.Util.Indices (PatternedTensor)
import Perpl.Util.JSON
import Perpl.Util.RuleM
import Perpl.Util.Tensor (TensorLike)
import Debug.Trace (trace)

type ResultT = ExceptT String RuleM

moduleName :: String
moduleName = "Translate To FGG: "

err :: String -> Result a
err msg = reportErr moduleName msg

errT :: String -> ResultT a
errT msg = throwError msg

type Info = Map.Map String Iso

makeInfo :: Definitions -> Info
makeInfo = Map.fromList

lookupIso :: String -> Info -> Result Iso
lookupIso var table =
  case Map.lookup var table of
    Just iso -> return iso
    Nothing -> err ("Undefined ISO: " ++ var)

transToFggPg :: Bool -> (Definitions, Program) -> Result JSON
transToFggPg suppress pgs = do
  fgg <- compileToFggPg pgs :: Result (FGG PatternedTensor)
  return $ fgg_to_json suppress fgg

compileToFggPg :: TensorLike tensor => (Definitions, Program) -> Result (FGG tensor)
compileToFggPg (defs, pg) =
  do let info = makeInfo defs
     nodeLabels <- prog2NodeLabel pg
     edgeLabel <- prog2NtEdgeLabel pg
     let (v, rs) = runRuleM (runExceptT $ prog2Rules info pg)
     case v of
       Left msg -> err msg
       Right _ -> return (rulesToFGG domain edgeLabel nodeLabels rs)

prog2NodeLabel :: Program -> Result [NodeLabel]
prog2NodeLabel (PgTm (TmAnn _ t)) = return $ map snd (newOutTmNodes [t])
prog2NodeLabel (PgIs (IsoAnn _ (ITyBase ty1 ty2))) = return $ map snd (newOutTmNodes [ty1, ty2])
prog2NodeLabel pg@(PgIs (IsoAnn {})) = err $ "The given iso is not supported to translate to FGG: " ++ show pg
prog2NodeLabel pg = err $ "The given program is not type annotated: " ++ show pg

prog2NtEdgeLabel :: Program -> Result EdgeLabel
prog2NtEdgeLabel (PgTm (TmAnn tm _)) = return (ElTmNonterminal (unwrapTm tm))
prog2NtEdgeLabel (PgIs (IsoAnn iso _)) = return (ElIsoNonterminal (unwrapIso iso))
prog2NtEdgeLabel pg = err $ "The given program is not type annotated: " ++ show pg

prog2Rules :: Info -> Program -> ResultT ()
prog2Rules info (PgTm (TmAnn tm ty)) = void (term2Fgg info tm ty)
prog2Rules info (PgIs (IsoAnn iso ty)) = void (iso2Fgg info iso ty)
prog2Rules _ pg = errT $ "The given program is not type annotated: " ++ show pg

term2Fgg :: Info -> Term -> BaseType -> ResultT [Node]
-- term2Fgg _ tm ty | trace ("Convert tm: " ++ show tm ++ " : " ++ show ty) False = undefined
term2Fgg _ TmUnit BTyUnit =
  let ns = newOutTmNodes [BTyUnit] in
    mkTermRule TmUnit ns [Edge ns (ElTerminal (FaMulProd []))] ns []
term2Fgg _ tm@(TmVar v) ty =
  let varNs = newVarTmNames [(v, ty)]
      tyNs = newOutTmNodes [ty]
      ns = varNs ++ tyNs
  in
    mkTermRule tm ns [Edge ns (ElTerminal (FaIdentity ty))] ns varNs
term2Fgg info tm@(TmPair tm1 tm2) ty@(BTyProd ty1 ty2) =
  do varsNs1 <- term2Fgg info tm1 ty1
     varsNs2 <- term2Fgg info tm2 ty2
     let varsNs = varsNs1 ++ varsNs2
         [internalNs1, internalNs2] = newInternalTmNodes [ty1, ty2]
         tyNs = newOutTmNodes [ty]
         e1 = termEdge (varsNs1 ++ [internalNs1]) tm1
         e2 = termEdge (varsNs2 ++ [internalNs2]) tm2
         e3 = Edge ([internalNs1, internalNs2] ++ tyNs) (ElTerminal (FaMulProd [ty1, ty2]))
     mkTermRule tm (varsNs ++ [internalNs1, internalNs2] ++ tyNs) [e1, e2, e3] (varsNs ++ tyNs) varsNs
term2Fgg info tm@(TmLInj tm1) ty@(BTySum ty1 ty2) =
  do
    varsNs <- term2Fgg info tm1 ty1
    let internalNs = newInternalTmNodes [ty1]
        tyNs = newOutTmNodes [ty]
        e1 = termEdge (varsNs ++ internalNs) tm1
        e2 = Edge (internalNs ++ tyNs)  (ElTerminal (FaAddProd [ty1, ty2] 0))
    mkTermRule tm (varsNs ++ internalNs ++ tyNs) [e1, e2] (varsNs ++ tyNs) varsNs
term2Fgg info tm@(TmRInj tm2) ty@(BTySum ty1 ty2) =
  do
    varsNs <- term2Fgg info tm2 ty2
    let internalNs = newInternalTmNodes [ty2]
        tyNs = newOutTmNodes [ty]
        e1 = termEdge (varsNs ++ internalNs) tm2
        e2 = Edge (internalNs ++ tyNs)  (ElTerminal (FaAddProd [ty1, ty2] 1))
    mkTermRule tm (varsNs ++ internalNs ++ tyNs) [e1, e2] (varsNs ++ tyNs) varsNs
term2Fgg info tapp@(TmIsoApp (IsoAnn iso ti@(ITyBase ty1 ty2)) tm) ty2' | ty2 == ty2' =
  do
    isoNs <- iso2Fgg info iso ti
    varsNs <- term2Fgg info tm ty1
    let tyNs1 = newInternalTmNodes [ty1]
        tyNs2 = newOutTmNodes [ty2]
        e1 = termEdge (varsNs ++ tyNs1) tm
        e2 = isoEdge (isoNs ++ tyNs1 ++ tyNs2) iso
    mkTermRule tapp (varsNs ++ isoNs ++ tyNs1 ++ tyNs2) [e1, e2] (varsNs ++ tyNs2) varsNs
term2Fgg info tlet@(TmLet pat (TmAnn rhs ty1) body) ty =
  do
    varsNs1 <- term2Fgg info rhs ty1
    varsNs2 <- pattern2fgg info pat ty1
    varsNs3 <- term2Fgg info body ty -- we assume that varsNs2 is a subset of varsNs3
    let varsNs = filter (`notElem` varsNs2) (varsNs1 ++ varsNs3)
        tyNs1 = newInternalTmNodes [ty1]
        tyNs = newOutTmNodes [ty]
        e1 = termEdge (varsNs1 ++ tyNs1) rhs
        e2 = termEdge (varsNs2 ++ tyNs1) (pat2Tm pat)
        e3 = termEdge (varsNs3 ++ tyNs) body
    mkTermRule tlet (varsNs1 ++ varsNs3 ++ tyNs1 ++ tyNs) [e1, e2, e3] (varsNs ++ tyNs) varsNs
term2Fgg info t@(TmScale s tm) ty =
  do
    varsNs <- term2Fgg info tm ty
    let tyNs = newOutTmNodes [ty]
        ns = varsNs ++ tyNs
        e1 = Edge [] (ElTerminal (FaScalar s))
        e2 = termEdge ns tm
    mkTermRule t ns [e1, e2] ns varsNs
term2Fgg info t@(TmPlus tms) ty = do
  (varsNs, hgfs) <- mkHGFs (tm2Hgf info) tms ty
  bindTmCases varsNs t hgfs
term2Fgg info (TmAnn tm ty1) ty2 | ty1 == ty2 = term2Fgg info tm ty1
term2Fgg _ tm _ = error $ "Unsupported term for translating to FGG: " ++ show tm

iso2Fgg :: Info -> Iso -> IsoType -> ResultT [Node]
iso2Fgg info iso@(IsoValue ves) (ITyBase vTy eTy) = do
  (varsNs, hgfs) <- mkHGFs (cls2Hgf info) ves (vTy, eTy)
  bindIsoCases varsNs iso hgfs
iso2Fgg info (IsoVar var) ti@(ITyBase vTy eTy) = do
  iso <- except (lookupIso var info)
  _ <- iso2Fgg info iso ti
  let ns = newOutTmNodes [vTy, eTy]
      e1 = isoEdge ns iso
  mkIsoRule (IsoVar var) ns [e1] ns []
iso2Fgg info (IsoVar var) ti =
  errT $ "Translating second order iso var to FGG is in progress: " ++ var
iso2Fgg info iso@(IsoLam var lTy rTy body) ty =
  errT $ "Translating second order iso to FGG is in progress: " ++ show iso
iso2Fgg info iso@(IsoApp (IsoAnn lhs tiso@(ITyFun lhsTy rhsTy _)) rhs) ty = do
  lhsVars <- iso2Fgg info lhs tiso
  rhsVars <- iso2Fgg info rhs (ITyBase lhsTy rhsTy)
  errT $ "Translating application of second-order iso to FGG is in progress: " ++ show iso
iso2Fgg info (IsoAnn iso ty) ty' | ty == ty' = iso2Fgg info iso ty
iso2Fgg _ iso _ = errT $ "Unsupported iso for translating to FGG: " ++ show iso

cls2Hgf :: Info -> (Value, Exp) -> (BaseType, BaseType) -> ResultT ([Node], [HGF])
cls2Hgf info (v, e) (vTy, eTy) =
  do
    vTm <- val2Tm v
    eTm <- exp2Tm e
    varsNs1 <- term2Fgg info vTm vTy
    varsNs2 <- term2Fgg info eTm eTy
    let varsNs = varsNs1 ++ varsNs2
        [tyNs1, tyNs2] = newOutTmNodes [vTy, eTy]
        ns = varsNs ++ [tyNs1, tyNs2]
        e1 = termEdge (varsNs1 ++ [tyNs1]) vTm
        e2 = termEdge (varsNs2 ++ [tyNs2]) eTm
    mkHGF ns [e1, e2] [tyNs1, tyNs2] []

pattern2fgg :: Info -> Pattern -> BaseType -> ResultT [Node]
pattern2fgg info pat ty = term2Fgg info (pat2Tm pat) ty

mkHGFs :: (a -> b -> ResultT ([Node], [HGF])) -> [a] -> b -> ResultT ([Node], [HGF])
mkHGFs f as b = foldlM acc ([], []) as where
  acc (ns, hgfs) a = do
    (ns', hgfs') <- f a b
    return (nub $ ns ++ ns', nub $ hgfs ++ hgfs')

tm2Hgf :: Info -> Term -> BaseType -> ResultT ([Node], [HGF])
tm2Hgf info tm ty = do
  varsNs <- term2Fgg info tm ty
  let tyNs = newOutTmNodes [ty]
      ns = varsNs ++ tyNs
      e1 = termEdge ns tm
  mkHGF ns [e1] ns varsNs

val2Tm :: Value -> ResultT Term
val2Tm ValUnit = return TmUnit
val2Tm (ValVar v) = return $ TmVar v
val2Tm (ValPair v1 v2) =
  do t1 <- val2Tm v1
     TmPair t1 <$> val2Tm v2
val2Tm (ValLInj v) = TmLInj <$> val2Tm v
val2Tm (ValRInj v) = TmRInj <$> val2Tm v
val2Tm (ValAnn v ty) = do
  tm <- val2Tm v
  return $ TmAnn tm ty
val2Tm v = errT $ "Unsupported base value for converting to FGG: " ++ show v

exp2Tm :: Exp -> ResultT Term
exp2Tm (ExpVal v) = val2Tm v
exp2Tm (ExpLet pat iso@(IsoAnn _ (ITyBase vTy eTy)) pat' body) = do
  let tPat' = pat2Tm pat'
  tBody <- exp2Tm body
  return $ TmLet pat (TmAnn (TmIsoApp iso (TmAnn tPat' vTy)) eTy) tBody
exp2Tm e@(ExpLet {}) =
  errT $ "The given expression " ++ show e ++ " is not type annotated when translating to FGG!"
exp2Tm (ExpScale s e) = do
  t <- exp2Tm e
  return $ TmScale s t
exp2Tm (ExpPlus es) = TmPlus <$> mapM exp2Tm es

pat2Tm :: Pattern -> Term
pat2Tm (PtSingleVar var) = TmVar var
pat2Tm (PtMultiVar []) = TmUnit
pat2Tm (PtMultiVar [var]) = TmVar var
pat2Tm (PtMultiVar (var:vars)) = TmPair (TmVar var) (pat2Tm (PtMultiVar vars))

termEdge :: [Node] -> Term -> Edge
termEdge nodes tm = Edge nodes (ElTmNonterminal (unwrapTm tm))

isoEdge :: [Node] -> Iso -> Edge
isoEdge nodes iso = Edge nodes (ElIsoNonterminal (unwrapIso iso))

{- domain ty

Convert a type to a domain. -}
domainBaseType :: BaseType -> Result [ProgramBaseValue]
domainBaseType BTyUnit = return [PBValUnit]
domainBaseType (BTySum lTy rTy) = do
  lVals <- domainBaseType lTy
  rVals <- domainBaseType rTy
  return $ map PBValLeft lVals ++ map PBValRight rVals
domainBaseType (BTyProd lTy rTy) = do
  lVals <- domainBaseType lTy
  rVals <- domainBaseType rTy
  return $ [PBValPair l r | l <- lVals, r <- rVals]
domainBaseType ty = err $ "Unsupported Base type for converting to a FGG domain: " ++ show ty

domainIsoType :: IsoType -> Result [ProgramBaseValue]
domainIsoType (ITyBase vTy eTy) = do
  vVals <- domainBaseType vTy
  eVals <- domainBaseType eTy
  -- We use product type to enumerate all possible base values
  return $ [PBValPair l r | l <- vVals, r <- eVals]
domainIsoType ty@(ITyFun lhsTy rhsTy bodyTy) =
  err $ "Getting domain of higher-order iso type is in progress: " ++ show ty

mkDomain :: [ProgramBaseValue] -> Domain
mkDomain vals = Domain (length vals) (map (DValue . show) vals)

domain :: NodeLabel -> Domain
domain (TmNodeLabel ty) = case domainBaseType ty of
  Left msg -> error msg
  Right vals -> mkDomain vals
domain (IsoNodeLabel ty) = case domainIsoType ty of
  Left msg -> error msg
  Right vals -> mkDomain vals

{- mkRule lhs ns es xs

Creates a rule.

- lhs: the left-hand side
- ns:  the right-hand side node ids and labels
- es:  the right-hand side edges
- xs:  the external node ids and labels
- vxs: the external node ids and labels that come from free variables in the
       left-hand side -}
mkTermRule :: Term -> [Node] -> [Edge] -> [Node] -> [Node] -> ResultT [Node]
-- mkTermRule tm ns edges extns varexts |
--   trace ("tm: " ++ show tm ++ ", nodes: " ++ show ns ++ ", edges: " ++
--          show edges ++ ", exts: " ++ show extns ++ ", var external nodes: " ++ show varexts) False = undefined
mkTermRule tm ns edges extns varexts = mkRule (ElTmNonterminal (unwrapTm tm)) ns edges extns varexts

mkIsoRule :: Iso -> [Node] -> [Edge] -> [Node] -> [Node] -> ResultT [Node]
mkIsoRule iso = mkRule (ElIsoNonterminal (unwrapIso iso))

mkRule :: EdgeLabel -> [Node] -> [Edge] -> [Node] -> [Node] -> ResultT [Node]
mkRule lhs ns es xs vxs =
  do
    let xs' = nub xs
    lift $ addRuleBlock lhs [HGF (nub ns) es xs'] >> return vxs

{- bindTmCases xs rms

   Runs all of rms and keeps only the external nodes in xs. -}
bindTmCases :: [Node] -> Term -> [HGF] -> ResultT [Node]
bindTmCases vxs tm rms =
  do
    let vxs' = nub vxs
    lift $ addRuleBlock (ElTmNonterminal (unwrapTm tm)) rms >> return vxs'

bindIsoCases :: [Node] -> Iso -> [HGF] -> ResultT [Node]
bindIsoCases vxs iso rms =
  do
    let vxs' = nub vxs
    lift $ addRuleBlock (ElIsoNonterminal (unwrapIso iso)) rms >> return vxs'

{- mkHGF ns es xs

Creates a rule.

- ns:  the right-hand side node ids and labels
- es:  the right-hand side edges
- xs:  the external node ids and labels
- vxs: the external node ids and labels that come from free variables in the
       left-hand side -}
mkHGF :: [Node] -> [Edge] -> [Node] -> [Node] -> ResultT ([Node], [HGF])
mkHGF ns es xs vxs =
  do
    let xs' = nub xs
    return (vxs, [HGF (nub ns) es xs'])

unwrapTm :: Term -> Term
unwrapTm TmUnit = TmUnit
unwrapTm (TmInt n) = TmInt n
unwrapTm TmEmpty = TmEmpty
unwrapTm (TmCons l r) = TmCons (unwrapTm l) (unwrapTm r)
unwrapTm (TmVar var) = TmVar var
unwrapTm (TmLInj tm) = TmLInj (unwrapTm tm)
unwrapTm (TmRInj tm) = TmRInj (unwrapTm tm)
unwrapTm (TmPair l r) = TmPair (unwrapTm l) (unwrapTm r)
unwrapTm (TmIsoApp iso tm) = TmIsoApp (unwrapIso iso) (unwrapTm tm)
unwrapTm (TmLet pat rhs body) = TmLet pat (unwrapTm rhs) (unwrapTm body)
unwrapTm (TmSuc tm) = TmSuc (unwrapTm tm)
unwrapTm (TmScale s tm) = TmScale s (unwrapTm tm)
unwrapTm (TmPlus tms) = TmPlus $ map unwrapTm tms
unwrapTm (TmAnn tm _) = unwrapTm tm

unwrapIso :: Iso -> Iso
unwrapIso (IsoValue ves) = IsoValue (map (bimap unwrapValue unwrapExp) ves)
unwrapIso (IsoVar var) = IsoVar var
unwrapIso (IsoLam var lhs rhs body) = IsoLam var lhs rhs (unwrapIso body)
unwrapIso (IsoApp rator rand) = IsoApp (unwrapIso rator) (unwrapIso rand)
unwrapIso (IsoFix var lhs rhs iso) = IsoFix var lhs rhs (unwrapIso iso)
unwrapIso (IsoAnn iso _) = unwrapIso iso

unwrapValue :: Value -> Value
unwrapValue ValUnit = ValUnit
unwrapValue (ValInt n) = ValInt n
unwrapValue (ValSuc v) = ValSuc (unwrapValue v)
unwrapValue ValEmpty = ValEmpty
unwrapValue (ValCons l r) = ValCons (unwrapValue l) (unwrapValue r)
unwrapValue (ValVar var) = ValVar var
unwrapValue (ValLInj v) = ValLInj (unwrapValue v)
unwrapValue (ValRInj v) = ValRInj (unwrapValue v)
unwrapValue (ValPair l r) = ValPair (unwrapValue l) (unwrapValue r)
unwrapValue (ValAnn v _) = unwrapValue v

unwrapExp :: Exp -> Exp
unwrapExp (ExpVal v) = ExpVal (unwrapValue v)
unwrapExp (ExpLet pat iso pat' body) = ExpLet pat (unwrapIso iso) pat' (unwrapExp body)
unwrapExp (ExpScale s e) = ExpScale s (unwrapExp e)
unwrapExp (ExpPlus es) = ExpPlus (map unwrapExp es)

{- Functions to make nodes. -}
newInternalNodes :: (a -> NodeLabel) -> [a] -> [Node]
newInternalNodes f as = [(NnInternal j, f atp) | (j, atp) <- enumerate as]

newVarNames :: (a -> NodeLabel) -> [(String, a)] -> [Node]
newVarNames f vtys = [ (NnVar v, f ty) | (v, ty) <- vtys]

newOutNodes :: (a -> NodeLabel) -> [a] -> [Node]
newOutNodes f tys = [(NnOut j, f ty) | (j, ty) <- enumerate tys]

newInternalTmNodes :: [BaseType] -> [Node]
newInternalTmNodes as = newInternalNodes TmNodeLabel as

newVarTmNames :: [(String, BaseType)] -> [Node]
newVarTmNames vtys = newVarNames TmNodeLabel vtys

newOutTmNodes :: [BaseType] -> [Node]
newOutTmNodes tys = newOutNodes TmNodeLabel tys

newInternalIsoNodes :: [IsoType] -> [Node]
newInternalIsoNodes as = newInternalNodes IsoNodeLabel as

newVarIsoNames :: [(String, IsoType)] -> [Node]
newVarIsoNames vtys = newVarNames IsoNodeLabel vtys

newOutIsoNodes :: [IsoType] -> [Node]
newOutIsoNodes tys = newOutNodes IsoNodeLabel tys
