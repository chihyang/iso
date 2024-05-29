module Convert (matrixize, matrixizeScale, matrixizeEntangled) where

import Syntax
import Data.Matrix
import qualified Data.List as L
import qualified Data.Set as Set
import Debug.Trace as T (trace)

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

collectIndex :: (Ord a) => [(a , Int)] -> a -> Int
collectIndex valMap val =
  case lookup val valMap of
    Just b -> b
    Nothing -> -1

matrixizeScale :: (Ord a) => [[(Scale , a)]] -> [a] -> Matrix Scale
-- matrixizeScale scaled keys | T.trace ("matrixizeScale " ++ show scaled ++ ", " ++ show keys) False = undefined
matrixizeScale scaled keys = matrix (length keys) (length scaled) fill where
  fill (x , y) = do
    let vals = scaled!!(y-1)
    let key = keys!!(x-1)
    case L.find (\v -> key == snd v) vals of
      Just (s, _) -> s
      Nothing -> (0 :+ 0)

matrixize :: (Ord a) => [a] -> a -> Matrix Scale
matrixize vals val = matrix (length valMap) 1 fill where
  valMap = indexMap vals
  idx = collectIndex valMap val
  fill (x , _) = if (x - 1) == idx then 1 else 0

matrixizeEntangled :: (Ord a) => [(Scale, a)] -> [a] -> Matrix Scale
matrixizeEntangled scaled keys = matrix (length keys) 1 fill where
  fill (x , _) = do
    let key = keys!!(x-1)
    case L.find (\v -> key == snd v) scaled of
      Just (s, _) -> s
      Nothing -> (0 :+ 0)
