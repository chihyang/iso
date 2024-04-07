-- Using flatparse library

{-# language StrictData #-}
{-# language TemplateHaskell #-}

module FlatParser (
  flatParse,
  parse,
  parseDefsPg,
  pProg,
  pDefsPg,
  F.Result(..)
  ) where

--import qualified Language.Haskell.TH as TH

import qualified Data.ByteString as B
import qualified Data.Complex as C

import FlatParse.Basic as F hiding (Parser, runParser, string, cut)
import FlatParse.Common.Parser (PureMode)
import FlatParse.Examples.BasicLambda.Lexer hiding (isKeyword)
import FlatParse.Examples.BasicLambda.Parser (Name, int, digit)
import Syntax

type FParser a = F.ParserT PureMode Error a
-- TODO: use TH to expand kw's
-- keywordsList = ["Unit", "Int", "mu", "unit", "left", "right", "let", "in"]
-- kw = map (\str -> [| $(str) -> pure () |] keywordsList
-- isKeyword = foldl1 <|> . map macro

isKeyword :: Span -> Parser ()
isKeyword spn = inSpan spn $ do
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
  withSpan (identStartChar *> skipMany identChar) (\_ spn -> fails (isKeyword spn))

ident'' :: Parser String
ident'' = utf8ToStr <$> ident

-- use TH to write this so it's feasible to do `C <$> parens p` with nary constructors?
parens p = $(symbol "(") *> p <* $(symbol' ")")
brackets p = $(symbol "[") *> p <* $(symbol' "]")
braces p = $(symbol "{") *> p <* $(symbol' "}")
angle p = $(symbol "<") *> p <* $(symbol' ">")

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
pValPair = angle (ValPair <$> pValue <* $(symbol ",") <*> pValue)
pValAnn  = parens (ValAnn <$> pValue <* $(symbol "::") <*> pBaseType)

pValue = pValUnit <|> pValInt <|> pValLInj <|> pValRInj <|> pValPair <|> pValAnn <|> pValVar

{-
-- Exp
-}
pExpVal :: FParser Exp
pExpVal = ExpVal <$> pValue

pExpLet :: FParser Exp
pExpLet = do
  $(keyword "let")
  pat <- pPattern
  $(symbol' "=")
  iso <- pIso
  pat' <- pPattern
  $(keyword' "in")
  body <- pExp
  return $ ExpLet pat iso pat' body

double :: Parser Double
double = token $ do
  whole <- some digit
  $(char '.')
  frac <- some digit
  let wholeVal = foldl (\acc e -> acc * 10.0 + fromIntegral e) 0.0 whole
  let fracVal = foldr (\e acc -> acc / 10.0 + fromIntegral e / 10) 0.0 frac
  return $ (wholeVal + fracVal)

pNumber :: Parser Double
pNumber = double <|> (fromIntegral <$> int)

pNegNumber :: Parser Double
pNegNumber = do
  $(symbol "(")
  $(symbol "-")
  n <- pNumber
  $(symbol ")")
  return ((-1) * n)

pAllNumber :: Parser Double
pAllNumber = pNegNumber <|> pNumber

pComplex :: FParser Scale
pComplex = do
  $(symbol "(")
  real <- pAllNumber
  $(symbol' ":+")
  imag <- pAllNumber
  $(symbol ")")
  return $ real C.:+ imag

pScale :: FParser Scale
pScale = pComplex <|> ((\r -> r :+ 0) <$> pNumber)

pExpScale :: FParser Exp
pExpScale = do
  scale <- pScale
  $(symbol "*")
  e <- pExp
  return $ ExpScale scale e

pExpAdd :: FParser Exp
pExpAdd = $(symbol "+") *> pExp

pExpSub :: FParser Exp
pExpSub = do
  $(symbol "-")
  v <- pExp
  return $ ExpScale ((-1.0) :+ 0) v

pExpAdditive :: FParser Exp
pExpAdditive = pExpAdd <|> pExpSub

pExpPlus :: FParser Exp
pExpPlus = do
  $(symbol "[")
  l <- pExp
  r <- pExpAdditive
  $(symbol "]")
  return $ ExpPlus [l,r]

pExp :: FParser Exp
pExp = pExpLet <|> pExpPlus <|> pExpScale <|> pExpVal

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
pIsoValue = braces $ IsoValue <$> ((:) <$> pIsoClause <*> many ($(symbol ";") *> pIsoClause))

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

pIsoApp = brackets (IsoApp <$> pIso <*> pIso)

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
pTmPair = angle (TmPair <$> pTerm <* $(symbol ",") <*> pTerm)
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
-- Definitions
-}
pDefType :: FParser (String, Either IsoType Iso)
pDefType = do
  var <- ident''
  $(symbol "::")
  ty <- pIsoType
  return (var, Left ty)

pDefIso :: FParser (String, Either IsoType Iso)
pDefIso = do
  var <- ident''
  $(symbol "=")
  iso <- pIso
  return (var, Right iso)

pDef = pDefType <|> pDefIso

{-
-- Program
-}
pPgTm :: FParser Program
pPgTm = PgTm <$> pTerm

pPgIs :: FParser Program
pPgIs = PgIs <$> pIso

pProg :: FParser Program
pProg = pPgIs <|> pPgTm

pDefsPg :: FParser (Declarations, Program)
pDefsPg = do
  decs <- many pDef
  pg <- pProg
  return (decs, pg)

flatParse :: String -> F.Result Error Program
flatParse str = runParser pProg (strToUtf8 str)

parse :: String -> Syntax.Result Program
parse str =
  case runParser pProg (strToUtf8 str) of
    OK ast rest ->
      if rest == B.empty
      then return ast
      else Left $ "Incomplete input:\n" ++ str
    Fail -> Left "Invalid input!"
    Err msg -> Left $ show msg

parseDefsPg :: String -> Syntax.Result (Declarations, Program)
parseDefsPg str =
  case runParser pDefsPg (strToUtf8 str) of
    OK ast rest ->
      if rest == B.empty
      then return ast
      else Left $ "Incomplete input:\n" ++ str
    Fail -> Left "Invalid input!"
    Err msg -> Left $ show msg
