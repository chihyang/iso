module Convert (matrixize, matrixizePairs) where

import Data.Matrix
import qualified Data.Set as Set

moduleName :: String
moduleName = "Matrixize: "

listToIndices :: [a] -> [Int]
listToIndices l = listToIndicesAcc l 0

listToIndicesAcc :: [a] -> Int -> [Int]
listToIndicesAcc [] _ = []
listToIndicesAcc (_ : tl) acc = acc : listToIndicesAcc tl (acc + 1)

indexMap :: (Ord a) => [a] -> [(a , Int)]
indexMap l = zip l' idx where
  l' = Set.toAscList $ Set.fromList l
  idx = listToIndices l'

checkedLookup :: (Eq a) => [(a , b)] -> a -> b
checkedLookup l k = case (lookup k l) of
  Just v -> v
  Nothing -> error "In a checked lookup, we should always find a key!"

collectIndices :: (Ord a , Ord b) =>
  [(a , Int)] -> [(b , Int)] -> [(a , b)] -> [a] -> Set.Set (Int , Int)
collectIndices lhsMap rhsMap pairs lhs =
  foldl (\r v -> Set.insert v r) Set.empty idPairs where
    idPairs = mapFilter (\l -> case lookup l pairs of
                           Just b -> Just (checkedLookup rhsMap b, checkedLookup lhsMap l)
                           Nothing -> Nothing)
              lhs
    mapFilter _ [] = []
    mapFilter f (v:vs) =
      case f v of
        Just b -> b : (mapFilter f vs)
        _ -> mapFilter f vs

collectIndex :: (Ord a) => [(a , Int)] -> a -> Int
collectIndex valMap val =
  case lookup val valMap of
    Just b -> b
    Nothing -> -1

matrixizePairs :: (Ord a , Ord b) => [(a , b)] -> [a] -> [b] -> Matrix Int
matrixizePairs pairs lhs rhs = matrix (length rhsMap) (length lhsMap) fill where
  lhsMap = indexMap lhs
  rhsMap = indexMap rhs
  idx = collectIndices lhsMap rhsMap pairs lhs
  fill (x , y) = if Set.member (x - 1, y - 1) idx then 1 else 0

matrixize :: (Ord a) => [a] -> a -> Matrix Int
matrixize vals val = matrix (length valMap) 1 fill where
  valMap = indexMap vals
  idx = collectIndex valMap val
  fill (x , _) = if (x - 1) == idx then 1 else 0
