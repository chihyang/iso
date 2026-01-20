{- A minimalist implementation of factor graph grammars (FGGs), which
   are the main target of the compiler. For more information about
   FGGs, see: David Chiang and Darcey Riley. Factor graph grammars. In
   Proc. NeurIPS, 6648–6658. 2020. -}

module Perpl.Util.FGG (Node, NodeName(..), NodeLabel,
                  Domain(..), Value(..),
                  Edge(..), EdgeLabel(..),
                  Factor(..), Weights, Weight,
                  HGF(..), Rule(..), FGG(..), showFGG) where
import Syntax (Scale, andOrd, compareScale)
import qualified Data.Map as Map
import Perpl.Struct.Lib
import Perpl.Util.Helpers
import Perpl.Util.Tensor
import Perpl.Util.JSON
import Data.List (intercalate)
import Data.Complex as C

-- Domain contains the size and a list of all values.
data Domain = Domain Int [Value]
newtype Value = Value String
  deriving Show
type Weight = Scale
type Weights a = a Weight

{- Every node in an FGG has a NodeName, which is unique within its
   Rule. Nodes are either internal or external, and we use different
   NodeNames for the two kinds of nodes. -}

data NodeName =
    NnOut           -- external node holding the value of an expression
  | NnVar TmVar     -- external node holding the value of a free variable
  | NnInternal Int  -- internal node
  deriving (Eq, Ord)
instance Show NodeName where
  show NnOut = "*out*"
  show (NnVar v) = show v
  show (NnInternal i) = "*" ++ show i ++ "*"

{- Every node in an FGG has a NodeLabel, which determines a set, called
   a Domain, of possible Values that the node can have. For our
   purposes, a NodeLabel is always a Type, and the corresponding
   Domain is the set of String representations of all the inhabitants
   of that Type. -}

type NodeLabel = Type

{- Every Edge (really, a hyperedge) in an FGG has an EdgeLabel, which is
   either terminal or nonterminal.

   - Both terminals and nonterminals determine a list of NodeLabels of
     the attachment nodes. In the FGG literature, this list is called
     a "type," which we always write in scare quotes here.

   - Terminals determine a function, called a Factor, from the
     attachment nodes' Values to a Weight; here, this function is
     represented as a Tensor.

   - Edges labeled with nonterminals can be rewritten using
     Rules. Here, nonterminal labels always correspond to Terms. -}

data EdgeLabel =
    ElNonterminal Term
  | ElTerminal Factor
  deriving (Eq, Ord)
instance Show EdgeLabel where
  show (ElNonterminal tm) = show tm
  show (ElTerminal fac) = show fac

data Factor =
    FaScalar Weight                     -- just a scalar weight
  | FaIdentity Type                     -- identity matrix for tp
  | FaEqual Type Int                    -- k-way equality for tp
  | FaArrow Type Type                   -- tensor mapping (tp1, tp2) to tp1, tp2
  | FaAddProd [Type] Int                -- matrix projecting tp1+...+tpn to tpk
  | FaMulProd [Type]                    -- tensor mapping (tp1,...,tpn) to tp1,...,tpn
  | FaCtor [Ctor] Int                   -- k'th constructor in cs
  deriving (Eq)
instance Ord Factor where
  compare (FaScalar w) (FaScalar w') = compareScale w w'
  compare (FaScalar _) _ = LT
  compare (FaIdentity {}) (FaScalar _) = GT
  compare (FaIdentity t) (FaIdentity t') = compare t t'
  compare (FaIdentity _) _ = LT
  compare (FaEqual {}) (FaScalar {}) = GT
  compare (FaEqual {}) (FaIdentity {}) = GT
  compare (FaEqual t n) (FaEqual t' n') = andOrd (compare t t') (compare n n')
  compare (FaEqual {}) _ = LT
  compare (FaArrow {}) (FaScalar {}) = GT
  compare (FaArrow {}) (FaIdentity {}) = GT
  compare (FaArrow {}) (FaEqual {}) = GT
  compare (FaArrow t1 t2) (FaArrow t1' t2') = andOrd (compare t1 t1') (compare t2 t2')
  compare (FaArrow {}) _ = LT
  compare (FaAddProd {}) (FaScalar {}) = GT
  compare (FaAddProd {}) (FaIdentity {}) = GT
  compare (FaAddProd {}) (FaEqual {}) = GT
  compare (FaAddProd {}) (FaArrow {}) = GT
  compare (FaAddProd tys n) (FaAddProd tys' n') = andOrd (compare tys tys') (compare n n')
  compare (FaAddProd {}) _ = LT
  compare (FaMulProd {}) (FaScalar {}) = GT
  compare (FaMulProd {}) (FaIdentity {}) = GT
  compare (FaMulProd {}) (FaEqual {}) = GT
  compare (FaMulProd {}) (FaArrow {}) = GT
  compare (FaMulProd {}) (FaAddProd {}) = GT
  compare (FaMulProd tys) (FaMulProd tys') = compare tys tys'
  compare (FaMulProd {}) _ = LT
  compare (FaCtor ctors n) (FaCtor ctors' n') = andOrd (compare ctors ctors') (compare n n')
  compare (FaCtor {}) _ = GT
instance Show Factor where
  show (FaScalar w) = show w
  show (FaIdentity tp) = "Identity[" ++ show tp ++ "]"
  show (FaEqual tp n) = "Equal[" ++ show tp ++ "^" ++ show n ++ "]"
  show (FaArrow tp1 tp2) = "Arrow[" ++ show tp1 ++ "," ++ show tp2 ++ "]"
  show (FaAddProd tps k) = "AddProd[" ++ intercalate "," (show <$> tps) ++ ";" ++ show k ++ "]"
  show (FaMulProd tps) = "MulProd[" ++ intercalate "," (show <$> tps) ++ "]"
  show (FaCtor cs k) = "Ctor[" ++ show (cs !! k) ++ "]"

type Node = (NodeName, NodeLabel)
data Edge = Edge { edge_atts :: [Node], edge_label :: EdgeLabel }
  deriving (Eq, Show)
-- Hypergraph fragment (= hypergraph with external nodes)
data HGF = HGF { hgf_nodes :: [Node], hgf_edges :: [Edge], hgf_exts :: [Node] }
  deriving (Eq, Show)
data Rule = Rule EdgeLabel HGF
  deriving (Eq, Show)
data FGG a = FGG {
  domains :: Map NodeLabel Domain,                       -- node label to set of values
  factors :: Map EdgeLabel ([NodeLabel], Weights a),-- edge label to att node labels, weights
  nonterminals :: Map EdgeLabel [NodeLabel],             -- nt name to attachment node labels
  start :: EdgeLabel,                                    -- start nt
  rules :: [Rule]                                        -- rules
}

weight_to_json :: Weight -> JSON
weight_to_json (r :+ 0) = JSdouble r
weight_to_json (r :+ i) = JSarray [JSdouble r, JSdouble i]

{- fgg_to_json fgg

   Convert an FGG into a JSON. -}

fgg_to_json :: TensorLike a => Bool -> FGG a -> JSON
fgg_to_json si (FGG ds fs nts s rs) =
  let mapToList = \ ds f -> JSobject $ map f (Map.toList ds) in
  JSobject
    [("grammar", JSobject
      [("terminals", mapToList fs $
         \ (el, (d, mws)) -> (show el, JSobject [("type", JSarray [JSstring (show nl) | nl <- d])])),
       ("nonterminals", mapToList nts $
         \ (el, d) -> (show el, JSobject [
           ("type", JSarray [JSstring (show nl) | nl <- d])
         ])),
       ("start", JSstring (show s)),
       ("rules", JSarray $ flip map rs $
          \ (Rule lhs (HGF ns es xs)) ->
            let m = Map.fromList (zip (fsts ns) [0..]) in
            JSobject [
             ("lhs", JSstring (show lhs)),
             ("rhs", JSobject [
                 ("nodes", JSarray [JSobject [("label", JSstring (show d)), ("id", JSstring (show n))] | (n, d) <- ns]),
                 ("edges", JSarray $ flip map es $
                   \ (Edge atts el) -> JSobject [
                     ("attachments", JSarray [JSint (m Map.! n) | (n, d) <- atts]),
                     ("label", JSstring (show el))
                   ]),
                 ("externals", JSarray [JSint (m Map.! n) | (n, d) <- xs])
               ])
         ])
      ]),
    ("interpretation", JSobject [
       ("domains", mapToList ds $
         \ (nl, Domain sz dom) ->
           if si
           then (show nl, JSobject [
                          ("class", JSstring "range"),
                          ("size", JSint sz)
                          ])
           else (show nl, JSobject [
                             ("class", JSstring "finite"),
                             ("values", JSarray $ [JSstring v | Value v <- dom])
                             ])),
       ("factors",
          mapToList fs $
           \ (el, (d, ws)) -> (show el, JSobject [
             ("function", JSstring "finite"),
               ("type", JSarray [JSstring (show nl) | nl <- d]),
               ("weights", weights_to_json weight_to_json ws)
             ]))
        ])
    ]


showFGG :: TensorLike a => Bool -> FGG a -> String
showFGG suppress_interp = pprint_json . fgg_to_json suppress_interp
