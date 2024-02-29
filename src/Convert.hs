module Convert (matrixize) where

import Data.Matrix
import qualified Data.Set as Set

listToIndices :: [a] -> [Int]
listToIndices l = listToIndicesAcc l 0

listToIndicesAcc :: [a] -> Int -> [Int]
listToIndicesAcc [] _ = []
listToIndicesAcc (_ : tl) acc = acc : listToIndicesAcc tl (acc + 1)

indexMap :: (Ord a) => [a] -> [(a , Int)]
indexMap l = zip l' idx where
  l' = Set.toAscList $ Set.fromList l
  idx = listToIndices l'

proofedLookup :: (Eq a) => [(a , b)] -> a -> b
proofedLookup l k = case (lookup k l) of
  Just v -> v
  Nothing -> error "In a proofed lookup, we should always find a key!"

collectIndices :: (Ord a , Ord b) =>
  [(a , Int)] -> [(b , Int)] -> [(a , b)] -> Set.Set (Int , Int)
collectIndices lhsMap rhsMap pairs =
  foldl (\r v -> Set.insert v r) Set.empty idPairs where
    idPairs = map (\p -> (proofedLookup rhsMap $ snd p ,
                          proofedLookup lhsMap $ fst p))
              pairs

matrixize :: (Ord a , Ord b) => [(a , b)] -> Matrix Int
matrixize pairs = matrix (length rhsMap) (length lhsMap) fill where
  lhsMap = indexMap $ map fst pairs
  rhsMap = indexMap $ map snd pairs
  idx = collectIndices lhsMap rhsMap pairs
  fill (x , y) = if Set.member (x - 1, y - 1) idx then 1 else 0
