module Expand (expandType) where

import Syntax
import Debug.Trace (trace)

moduleName :: String
moduleName = "Convert: "

-- expand a finite type to a list of values of that type
expandType :: BaseType -> Result [ProgramBaseValue]
-- expandType ty | trace ("expandType " ++ show ty) False = undefined
expandType BTyUnit = return [PBValUnit]
expandType BTyInt = Left $ moduleName ++ "Infinite type is not supported yet, given: " ++ show BTyInt
expandType (BTyList ty) = Left $ moduleName ++ "Infinite type is not supported yet, given: " ++ show (BTyList ty)
expandType (BTyVar var) = Left $ moduleName ++ "Cannot expand a type variable " ++ show var
expandType (BTySum left right) = do
  lhs <- expandType left
  rhs <- expandType right
  return $ (map PBValLeft lhs) ++ (map PBValRight rhs)
expandType (BTyProd hd tl) = do
  hdV <- expandType hd
  tlV <- expandType tl
  return [PBValPair h t | h <- hdV, t <- tlV]
expandType (BTyMu var body) =
  Left $ moduleName ++ "Recursive type is not supported yet, given: " ++ show (BTyMu var body)
