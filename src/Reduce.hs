module Reduce (foldDefsPg, foldDefs) where

import Syntax
import qualified Data.List as L
import Debug.Trace (trace)

moduleName :: String
moduleName = "Reduce: "

foldDefsPg :: (Declarations, Program) -> Result (Definitions, Program)
foldDefsPg (decls, pg) = do
  defs <- foldDefs decls
  return (defs, pg)

{---------- Fold declarations ----------}
foldDefs :: Declarations -> Result [(String, Iso)]
foldDefs decls = foldDeclsAcc (L.sort decls) []

-- Given a sorted list of declarations, return a list of possibly type
-- annotated isos.
foldDeclsAcc :: Declarations -> [(String, Iso)] -> Result [(String, Iso)]
foldDeclsAcc [] acc = return acc
foldDeclsAcc ((var, Left ty):decls) acc =
  case decls of
    ((var', Left _):_)
      | var' == var ->
        Left $ moduleName ++ var ++ " has multiple type declarations!"
    ((var', Right iso):decls')
      | var' == var && lookup var' decls' == Nothing ->
        foldDeclsAcc decls' ((var, (IsoAnn iso ty)):acc)
    ((var', Right _):_)
      | var' == var ->
        Left $ moduleName ++ var ++ " has multiple definitions!"
    ((var', _):_)
      | var' /= var ->
        Left $ moduleName ++ var ++ " has no definition!"
    _ -> Left $ moduleName ++ var ++ " has no definition!"
foldDeclsAcc ((var, Right _):_) _ =
  Left $ moduleName ++ var ++ " has no type declaration!"
