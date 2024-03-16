-- Using flatparse library

{-# language StrictData #-}
{-# language TemplateHaskell #-}

module FlatParser where

--import qualified Language.Haskell.TH as TH

import qualified Data.ByteString as B

import FlatParse.Basic hiding (Parser, runParser, string, char, cut)
import FlatParse.Common.Assorted (strToUtf8, utf8ToStr)
import FlatParse.Examples.BasicLambda.Lexer hiding (isKeyword)
import FlatParse.Examples.BasicLambda.Parser hiding (ident, ident')


import Data

-- TODO: use TH to expand kw's
-- keywordsList = ["Unit", "Int", "mu", "unit", "left", "right", "let", "in"]
-- kw = map (\str -> [| $(str) -> pure () |] keywordsList
-- isKeyword = foldl1 <|> . map macro

isKeyword :: Span -> Parser ()
isKeyword span = inSpan span $ do
  $(switch [| case _ of
      "Unit"  -> pure ()
      "Int"   -> pure ()
      "mu"    -> pure ()
      "fix"    -> pure ()
      "unit"  -> pure ()
      "left"  -> pure ()
      "right" -> pure ()
      "let"   -> pure ()
      "in"    -> pure ()
      "if"    -> pure ()
      "then"  -> pure ()
      "else"  -> pure ()
      "true"  -> pure ()
      "false" -> pure ()  |])
  eof

ident :: Parser Name
ident = token $ byteStringOf $
  withSpan (identStartChar *> skipMany identChar) (\_ span -> fails (isKeyword span))

ident' :: Parser Name
ident' = ident `cut'` (Msg "identifier")

ident'' = utf8ToStr <$> ident

-- use TH to write this so it's feasible to do `C <$> parens p` with nary constructors?
parens p = $(symbol "(") *> p <* $(symbol' ")") 
brackets p = $(symbol "[") *> p <* $(symbol' "]")
braces p = $(symbol "{") *> p <* $(symbol' "}")

{-
-- BaseType
-}
pBTyUnit = BTyUnit <$ $(keyword "Unit")
pBTyInt = BTyInt <$ $(keyword "Int")
pBTyVar = BTyVar <$> ident''
pBTySum = parens $ do
  l <- pBaseType
  $(symbol "+")
  r <- pBaseType
  return $ BTySum l r
pBTyProd = parens $ do
  l <- pBaseType
  $(symbol "x")
  r <- pBaseType
  return $ BTyProd l r
pBTyMu = do
  $(keyword "mu")
  var <- ident''
  $(symbol' ".")
  body <- pBaseType
  return $ BTyMu var body

pBaseType = pBTyUnit <|> pBTyInt <|> pBTySum <|> pBTyProd <|> pBTyMu <|> pBTyVar

{-
-- IsoType
-}
pITyBase = do
  l <- pBaseType
  $(symbol "<->")
  r <- pBaseType
  return $ ITyBase l r

pITyFun = p1 <* $(symbol' "->") <*> pIsoType
  where
    p1 = parens $ do
      l <- pBaseType
      $(symbol "<->")
      r <- pBaseType
      return $ ITyFun l r
    
pIsoType = pITyFun <|> pITyBase

{-
-- Value
-}
pValUnit = ValUnit <$ $(keyword "unit")
pValInt  = ValInt <$> int
pValVar  = ValVar <$> ident''
pValLInj = ValLInj <$> ($(keyword "left") *> pValue)
pValRInj = ValRInj <$> ($(keyword "right") *> pValue)
--pValPair = ValPair <$> parens (pValue <* $(symbol ",") <*> pValue)
pValPair = parens (ValPair <$> pValue <* $(symbol ",") <*> pValue)
pValAnn  = parens (ValAnn <$> pValue <* $(symbol "::") <*> pBaseType)

pValue = pValUnit <|> pValInt <|> pValLInj <|> pValRInj <|> pValPair <|> pValAnn <|> pValVar

{-
-- Exp
-}
pExpVal = ExpVal <$> pValue

pExpLet = do
  $(keyword "let")
  pat <- pPattern
  $(symbol' "=")
  iso <- pIso
  pat' <- pPattern
  $(keyword' "in")
  body <- pExp
  return $ ExpLet pat iso pat' body

pExp = pExpLet <|> pExpVal

{-
-- Pattern
-}
pPtSingleVar = PtSingleVar <$> ident''

-- Assume input syntax has at least 1 variable, otherwise fail
pListOfVars  = brackets $ do
  x1 <- ident''
  xs <- many ($(symbol' ",") *> ident'')
  return $ x1 : xs

pPtMultiVar  = PtMultiVar <$> pListOfVars

pPattern = pPtMultiVar <|> pPtSingleVar

{-
-- Iso
-}
pIsoClause = do
  lhs <- pValue
  $(symbol' "<->")
  rhs <- pExp
  return (lhs, rhs)

-- !! `some` would not work here even for positive cases
pIsoValue = braces $ IsoValue <$> ((:) <$> pIsoClause <*>
  many ($(symbol ";") *> pIsoClause))

pIsoVar = IsoVar <$> ident''

pIsoLam = do
  $(symbol "\\")
  var <- ident''
  $(symbol' "::")
  $(symbol' "(")
  l <- pBaseType
  $(symbol "<->")
  r <- pBaseType
  $(symbol' ")")
  $(symbol' "->")
  body <- pIso
  return $ IsoLam var l r body

pIsoApp = parens (IsoApp <$> pIso <*> pIso)

pIsoFix = do
  $(keyword "fix")
  var <- ident''
  $(symbol' ".")
  iso <- pIso
  return $ IsoFix var iso

pIsoAnn = parens $ IsoAnn <$> pIso <* $(symbol' "::") <*> pIsoType

pIso = pIsoValue <|> pIsoLam <|> pIsoApp <|> pIsoFix <|> pIsoAnn <|> pIsoVar

{-
-- Program
-}
pPgTm = PgTm <$> pTerm
pPgIs = PgIs <$> pIso
pProg = pPgTm <|> pPgIs

{-
-- Term
-}
pTmUnit = TmUnit <$ $(keyword "unit")
pTmInt  = TmInt <$> int
pTmVar  = TmVar <$> ident''
pTmLInj = TmLInj <$> ($(keyword "left") *> pTerm)
pTmRInj = TmRInj <$> ($(keyword "right") *> pTerm)
pTmPair = parens (TmPair <$> pTerm <* $(symbol ",") <*> pTerm)
pTmAnn  = parens (TmAnn <$> pTerm <* $(symbol "::") <*> pBaseType)
-- ^ above are alomost identical with pValue
pTmIsoApp = parens $ TmIsoApp <$> pIso <*> pTerm
pTmLet    = do
  $(keyword "let")
  pat <- pPattern
  $(symbol' "=")
  rhs <- pTerm
  $(keyword' "in")
  body <- pTerm
  return $ TmLet pat rhs body

pTerm = pTmUnit <|> pTmInt <|> pTmLInj <|> pTmRInj <|> pTmPair <|> pTmAnn
  <|> pTmIsoApp <|> pTmLet <|> pTmVar


{-
-- Examples
-}
parse p str = runParser p (strToUtf8 str)

test p str = putStrLn msg
  where
    msg = case parse p str of
      OK a res -> "OK\n" ++ show a ++ "\n" ++ show res
      Fail     -> "Failed"
      Err e    -> prettyError (strToUtf8 str) e 

-- Testing base types
str0 = "Unit"
res0 = test pBTyUnit str0

str1 = "(Int + Int)"
res1 = test pBTySum str1

str2 = "mu x. Int"
res2 = test pBaseType str2

str3 = "(mu var0  . Unit x Int)"
res3 = test pBaseType str3

-- Testing iso types
str4 = "Int <-> Int"
res4 = test pIsoType str4

str5 = "mu v . (v + Int) <-> Int"
res5 = test pIsoType str5

str5' = "mu v . v + Int <-> Int" -- this should fail
res5' = test pIsoType str5'

-- Testing values
str6 = "unit"
res6 = test pValue str6

str7 = "left 123"
res7 = test pValue str7

str8 = "(left 123, right v)"
res8 = test pValue str8

str9 = "(Nothing :: mu X. (X + Unit))"
res9 = test pValue str9

-- Testing expressions and patterns
str10 = "let x = f x in let y = g x in x"
res10 = test pExp str10

-- Isos
str11 = "{ 1 <-> 2 }"
res11 = test pIsoValue str11

str12 = "\\f :: (Nat <-> Nat) -> { 1 <-> 2 ; x <-> let y = f x in y }"
res12 = test pIso str12

-- Terms
str13 = "((\\f :: ((Unit + Nat) <-> Nat) -> { left unit <-> 0 ; x <-> let y = f x in y } \n\
          \{ right z <-> z }) 1)"
res13 = test pTmIsoApp str13

res14 = test pProg str13

