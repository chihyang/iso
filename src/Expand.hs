module Expand (expandType) where

import Syntax

-- expand a finite type to a list of values of that type
expandType :: BaseType -> [ProgramBaseValue]
expandType BTyUnit = [PBValUnit]
expandType BTyInt = error "Infinite type Nat hasn't been supported by this time!"
expandType (BTyVar _) = error "Var should have been expanded by this time!"
expandType (BTySum left right) = (map PBValLeft lhs) ++ (map PBValRight rhs) where
  lhs = expandType left
  rhs = expandType right
expandType (BTyProd hd tl) = [PBValPair h t | h <- hdV, t <- tlV] where
  hdV = expandType hd
  tlV = expandType tl
expandType (BTyMu _ _) = error "Recursive type is not supported yet!"
