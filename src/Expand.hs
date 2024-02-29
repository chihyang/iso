module Expand where
import Data

-- expand a finite type to a list of values of that type
expandFiniteType :: BaseType -> [ProgramBaseValue]
expandFiniteType BTyUnit = [PBValUnit]
expandFiniteType BTyInt = error "Infinite type Nat hasn't been supported by this time!"
expandFiniteType (BTyVar _) = error "Var should have been expanded by this time!"
expandFiniteType (BTySum left right) = (map PBValLeft lhs) ++ (map PBValRight rhs) where
  lhs = expandFiniteType left
  rhs = expandFiniteType right
expandFiniteType (BTyProd hd tl) = [PBValPair h t | h <- hdV, t <- tlV] where
  hdV = expandFiniteType hd
  tlV = expandFiniteType tl
expandFiniteType (BTyMu _ _) = error "Recursive type is not supported yet!"
