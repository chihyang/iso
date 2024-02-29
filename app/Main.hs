module Main (main) where

import Convert
import Data
import Interp

main :: IO ()
main = do {
  let e1 = IsoValue [ValUnit] [ExpVal (ValPair ValUnit ValUnit)]
  ; print e1
  ; let m1 = matrixize [("a" , 0 :: Int) , ("b" , 2 :: Int), ("c" , 3 :: Int)]
  ; print m1
  }
