-- Using flatparse library

{-# language StrictData #-}
{-# language TemplateHaskell #-}

module FlatParser where


import qualified Data.ByteString as B

import FlatParse.Basic hiding (Parser, runParser, string, char, cut)
import FlatParse.Common.Assorted (strToUtf8, utf8ToStr)
import FlatParse.Examples.BasicLambda.Lexer
import FlatParse.Examples.BasicLambda.Parser


import Data

ident'' = utf8ToStr <$> ident'

paren p = $(symbol "(") *> p <* $(symbol' ")")

pBTyUnit = BTyUnit <$ $(keyword "Unit")
pBTyInt = BTyUnit <$ $(keyword "Nat")
pBTyVar = BTyVar <$> ident''
pBTySum = paren $ do
  l <- pBaseType
  $(keyword "+")
  r <- pBaseType
  return $ BTySum l r
pBTyProd = paren $ do
  l <- pBaseType
  $(keyword "x")
  r <- pBaseType
  return $ BTyProd l r
pBTyMu = do
  $(keyword "mu")
  var <- ident''
  $(keyword ".")
  body <- pBaseType
  return $ BTyMu var body

pBaseType = pBTyUnit <|> pBTyInt <|> pBTySum <|> pBTyProd <|> pBTyMu <|> pBTyVar

{-
-- Examples
-}

str0 = "Unit"
res0 = parse pBTyUnit str0

str1 = "(Nat + Nat)"
res1 = parse pBTySum str1

str2 = "mu x. Nat"
res2 = parse pBaseType str2

str3 = "(mu var0  . Unit x Nat)"
res3 = parse pBaseType str3

parse p str = runParser p (strToUtf8 str)
