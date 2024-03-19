-- Using flatparse library

{-# language StrictData #-}
{-# language TemplateHaskell #-}

module FlatParser (
  parse,
  pProg,
  Result(..)
  ) where

--import qualified Language.Haskell.TH as TH

import qualified Data.ByteString as B

import FlatParse.Basic hiding (Parser, runParser, string, char, cut)
import FlatParse.Common.Assorted (strToUtf8, utf8ToStr)
import FlatParse.Examples.BasicLambda.Lexer hiding (isKeyword)
import FlatParse.Examples.BasicLambda.Parser (Name, int)


import Syntax

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

pTerm =
  pTmUnit <|>
  pTmInt <|>
  pTmLInj <|>
  pTmRInj <|>
  pTmPair <|>
  pTmAnn <|>
  pTmIsoApp <|>
  pTmLet <|>
  pTmVar

{-
-- Program
-}
pPgTm = PgTm <$> pTerm
pPgIs = PgIs <$> pIso
pProg = pPgTm <|> pPgIs

parse :: String -> Result Error Program
parse str = runParser pProg (strToUtf8 str)
