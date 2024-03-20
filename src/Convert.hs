module Convert (matrixize, matrixizeIso) where

import Data.Matrix
import qualified Data.Set as Set
import qualified Data.List as List
import Syntax as S

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
  [(a , Int)] -> [(b , Int)] -> [(a , b)] -> Set.Set (Int , Int)
collectIndices lhsMap rhsMap pairs =
  foldl (\r v -> Set.insert v r) Set.empty idPairs where
    idPairs = map (\p -> (checkedLookup rhsMap $ snd p ,
                          checkedLookup lhsMap $ fst p))
              pairs

matrixize :: (Ord a , Ord b) => [(a , b)] -> Matrix Int
matrixize pairs = matrix (length rhsMap) (length lhsMap) fill where
  lhsMap = indexMap $ map fst pairs
  rhsMap = indexMap $ map snd pairs
  idx = collectIndices lhsMap rhsMap pairs
  fill (x , y) = if Set.member (x - 1, y - 1) idx then 1 else 0

matrixizeIso :: ProgramValue -> S.Result (Matrix Int)
matrixizeIso (PI (PIValBase pairs _)) = return $ matrixize $ List.sort pairs
matrixizeIso (PB val) = Left $ moduleName ++ "Cannot convert a base value to matrix: " ++ show val
matrixizeIso (PI val) = Left $ moduleName ++ "Cannot convert an iso lambda to matrix: " ++ show val
