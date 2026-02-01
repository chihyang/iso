{- Code for generating FGG rules, and the RuleM monad. -}

module Perpl.Util.RuleM (RuleM, addRuleBlock, runRuleM, getWeights, rulesToFGG) where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Writer.Lazy
import Data.List (intercalate)
import Perpl.Util.FGG
import Perpl.Util.Helpers
import Perpl.Util.Tensor
import Syntax
import Debug.Trace (trace)

type RuleM = Writer (Map EdgeLabel [HGF])

{- addRuleBlock lhs rhss

   A "rule block" is a set of rules, all with the same lhs and the
   same external nodes, that comprise all the rules with that lhs.

   If there is already a rule block with this lhs, the new rule block
   is discarded. (Theoretically the new rule block is identical to the
   old one, but we do not check this.) -}

addRuleBlock :: EdgeLabel -> [HGF] -> RuleM ()
addRuleBlock lhs rhss = tell (Map.singleton lhs rhss)

runRuleM :: RuleM a -> (a, [Rule])
runRuleM rm =
  let (v, rs) = runWriter rm in
    (v, [Rule lhs rhs | (lhs, rhss) <- Map.toList rs, rhs <- rhss])

{--- Functions for computing Weights for terminal-labeled Edges ---}

{- getIdWeights n

   -  n: number of possible values

   Returns: the nxn identity matrix -}

getIdWeights :: TensorLike tensor => Int -> Weights tensor
getIdWeights n = tensorId [n]

{- getSumWeights sizes

   Computes the weights for the direct sum of a list of domains.

   - sizes: the list of domain sizes

   Returns: If tp = tp1 + ... + tpn, the tensor w[x, in(i) x] = 1. -}

getSumWeights :: TensorLike tensor => [Int] -> Int -> Weights tensor
getSumWeights = tensorSum

{- getProdWeights sizes

   Computes the weights for the tensor product of a list of domains.

   - sizes: the list of domain sizes

   If tp = (tp1, ..., tpn), returns the tensor w[x1, ..., xn, (x1, ..., xn)] = 1. -}

getProdWeights :: TensorLike tensor => [Int] -> Weights tensor
getProdWeights = tensorId

{- getEqWeights size n

   Returns the weights for (tm1 == tm2 == ... == tmn)

   - size: the size of the domains of the terms
   - n: the number of terms

   Returns: size x   ....   x s x 2 tensor
            |<- n copies ->|
 -}

getEqWeights :: TensorLike tensor => Int -> Int -> Weights tensor
getEqWeights size ntms = fromTensor $
  foldr
    (\ _ ws b mi -> Vector [ws (b && maybe True (== j) mi) (Just j) | j <- [0..size-1]])
    (\ b _ -> Vector (if b then [Scalar 0, Scalar 1] else [Scalar 1, Scalar 0]))
    [0..ntms-1]
    True
    Nothing

getWeights :: TensorLike tensor => (NodeLabel -> Int) -> Factor -> Weights tensor
getWeights size = h where
  h (FaScalar w) = fromTensor (Scalar w)
  h (FaIdentity tp) = getIdWeights (f tp)
  h (FaEqual tp n) = getEqWeights (f tp) n
  h (FaArrow tp1 tp2) = getProdWeights [f tp1, f tp2]
  h (FaAddProd tps k) = getSumWeights (f <$> tps) k
  h (FaMulProd tps) = getProdWeights (f <$> tps)

  f = size . TmNodeLabel

{- rulesToFGG dom start rs nts facs

   Construct an FGG from:

   - dom: function that gives the possible Values belonging to d
   - start: start nonterminal
   - start_type: start nonterminal
   - rs: list of rules
-}

rulesToFGG :: TensorLike tensor => (NodeLabel -> Domain) -> EdgeLabel -> [NodeLabel] -> [Rule] -> FGG tensor
rulesToFGG dom start start_type rs =
  FGG ds fs nts start (map checkRule rs)
  where
    -- Get all NodeLabels from start symbol and rule right-hand sides
    nls = concat (start_type : map (\ (Rule lhs (HGF ns es xs)) -> snds ns) rs)
    ds  = foldr (\ d m -> Map.insert d (dom d) m) Map.empty nls

    -- Get all EdgeLabels from both left-hand sides and right-hand
    -- sides. (The right-hand sides would be sufficient, but we want
    -- to check the left-hand sides for errors.)
    lhs_els :: [(EdgeLabel, [NodeLabel])]
    lhs_els = [(lhs, snds xs) | (Rule lhs (HGF _ es xs)) <- rs]

    rhs_es = concat [es | (Rule lhs (HGF _ es _)) <- rs]

    rhs_els :: [(EdgeLabel, [NodeLabel])]
    rhs_els = checkEdgeLabels [(el, snds atts) | (Edge atts el) <- rhs_es]

    checkNonterm :: EdgeLabel -> [NodeLabel] -> [NodeLabel] -> [NodeLabel]
    -- checkNonterm x d1 d2 | trace ("checkNonterm x d1 d2: " ++ show x ++ " " ++ show d1 ++ " " ++ show d2) False = undefined
    checkNonterm x d1 d2 = if d1 == d2 then d1 else error
      ("Conflicting types for nonterminal " ++ show x ++ ": " ++
        show d1 ++ " versus " ++ show d2)
    checkTerm x (d1, w1) (d2, _) = if d1 == d2 then (d1, w1) else error
      ("Conflicting types for terminal " ++ show x ++ ": " ++
        show d1 ++ " versus " ++ show d2)

    checkEdgeLabels els =
      let
        count = foldr (\ (el, _) -> Map.insertWith (<>) (show el) (Set.singleton el)) Map.empty els
        dups = Map.filter (\ s -> length s > 1) count
      in
        if not (null dups) then
          error ("Name collisions for edge labels: " ++ unwords (Map.keys dups))
        else
          els

    checkWeights el nls w =
      let shape = map domSize nls in
      if compatible (tensorShape w) shape then
        w
      else
        error ("Weight tensor for terminal " ++ show el ++ " has wrong shape (" ++ show (tensorShape w) ++ ", expected " ++ show shape ++ ")")

    checkRule r@(Rule lhs (HGF ns es xs)) =
      let count = Map.fromListWith (+) [(nn, 1) | (nn, nl) <- ns]
          dups = [nn | (nn, c) <- Map.toList count, c > 1] in
        if not (null dups) then
          error ("Node(s) " ++ intercalate ", " (show <$> dups) ++ " appear more than once in rule " ++ show r)
        else
          r

    -- lhs_els : [NodeLabel]
    -- rhs_els : [NodeLabel]
    (fs, nts) = foldr f (Map.empty, Map.fromList [(start, start_type)]) (lhs_els ++ rhs_els)

    f :: TensorLike tensor => (EdgeLabel, [NodeLabel]) ->
      (Map.Map EdgeLabel ([NodeLabel], Weights tensor), Map.Map EdgeLabel [NodeLabel]) ->
      (Map.Map EdgeLabel ([NodeLabel], Weights tensor), Map.Map EdgeLabel [NodeLabel])
    {-
    f (el@(ElTmNonterminal _), nls) (fs, nts) | trace ("foldr with f: EdgeLabel: " ++ show el ++
                                                       ", NodeLabels: " ++ show nls ++ ", Nonterminals: " ++
                                                       show nts ++ " " ++ show (Map.lookup el nts) ++ " " ++
                                                       show (compare el (fst $ head $ Map.toList nts))) False = undefined
    -}
    f (el, nls) (fs, nts) =
      case el of
        ElTerminal fac ->
          let w = checkWeights el nls (getWeights domSize fac) in
            (Map.insertWith (checkTerm el) el (nls, w) fs, nts)
        ElIsoNonterminal _ -> (fs, Map.insertWith (checkNonterm el) el nls nts)
        ElTmNonterminal _ -> (fs, Map.insertWith (checkNonterm el) el nls nts)

    -- myMapInsert f k v m | trace ("Insert " ++ show k ++ ", " ++ show v ++ " into " ++ show m ++ ", key in the map: " ++ (show $ Map.lookup k m)) False = undefined
    myMapInsert f k v m = Map.insertWith f k v m

    domSize d = sz where Domain sz _ = dom d

-- Compare two tensor shapes, but allow the first one
-- (generated by tensorShape) to end prematurely after 0
compatible :: [Int] -> [Int] -> Bool
compatible []     []     = True
compatible [0]    (0:_)  = True
compatible (x:xs) (y:ys) = x == y && compatible xs ys
compatible _      _      = False
