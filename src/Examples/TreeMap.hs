module Examples.TreeMap where

import Lang
import Parser


-- map `f` to a binary leaf tree
str1 = "\\ f -> fix phi .\n\
        \ {(l,r) <-> let x = phi l in\n\
        \   let y = phi r in\n\
        \     (x,y);\n\
        \  a  <-> let b = f a in b }"

res1 = test pTerm str1

-- `not`
str2 = "{ 1 <-> 0; 0 <-> 1}"
res2 = test pTerm str2

str3 :: String
str3 = "((0,(1,0)),1)"
res3 = test pTerm str3


prog = do
  map <- load str1
  not <- load str2
  tree1 <- load str3
  let t1 = TmApp map not
      t2 = TmApp t1 tree1
   in eval t2 initEnv
