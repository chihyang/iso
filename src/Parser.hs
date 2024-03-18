-- Using flatparse library

{-# language TemplateHaskell #-}

module Parser(pType, pIso, pTerm,
              isTmValue, isTmExp, isTmPattern, isTmIso,
              parse, test, load) where

--import qualified Language.Haskell.TH as TH
import Lang

import qualified Data.ByteString as B

import FlatParse.Basic hiding (Parser, runParser, string, char, cut)
--import FlatParse.Common.Assorted (strToUtf8, utf8ToStr)
import FlatParse.Examples.BasicLambda.Lexer hiding ( isKeyword)
import FlatParse.Examples.BasicLambda.Parser hiding (Name, ident, ident')

-- TODO: look at `chainl` provided by flatparser
sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 pa pb = (:) <$> pa <*> (many $ pb *> pa)

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy pa pb = sepBy1 pa pb <|> pure []
  
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

ident :: Parser String
ident = utf8ToStr <$> ident_

ident_ :: Parser B.ByteString
ident_ = token $ byteStringOf $
  withSpan (identStartChar *> skipMany identChar) (\_ span -> fails (isKeyword span))

ident' :: Parser Name
ident' = ident `cut'` (Msg "identifier")

-- use TH to write this so it's feasible to do `C <$> parens p` with nary constructors?
parens p = $(symbol "(") *> p <* $(symbol' ")") 
brackets p = $(symbol "[") *> p <* $(symbol' "]")
braces p = $(symbol "{") *> p <* $(symbol' "}")

pType = pBaseType <|> pIsoType

{-
-- BaseType
-}
pTyUnit :: Parser Type
pTyUnit = TyUnit <$ $(keyword "Unit")

pTyInt = TyInt <$ $(keyword "Int")
pTyVar = TyVar <$> ident
pTySum = parens $ do
  l <- pBaseType
  $(symbol "+")
  r <- pBaseType
  return $ TySum l r
pTyProd = parens $ do
  l <- pBaseType
  $(symbol "x")
  r <- pBaseType
  return $ TyProd l r
pTyMu = do
  $(keyword "mu")
  var <- ident
  $(symbol' ".")
  body <- pBaseType
  return $ TyMu var body

pBaseType = pTyUnit <|> pTyInt <|> pTySum <|> pTyProd <|> pTyMu <|> pTyVar
pBaseType' = pBaseType `cut'` (Msg "expecting BaseType") 

{-
-- IsoType
-}
pTyIsoZ = do
  l <- pType
  $(symbol "<->")
  r <- pType
  return $ TyIsoZ l r

pTyIsoS = p1 <* $(symbol' "->") <*> pIsoType
  where
    p1 = parens $ do
      l <- pType
      $(symbol "<->")
      r <- pType
      return $ TyIsoS l r
    
pIsoType = pTyIsoZ <|> pTyIsoS

pIsoType' = pIsoType `cut'` (Msg "expecting IsoType")

{-
-- Term
-}
pUnit = TmUnit <$ $(keyword "unit")
pInt  = TmInt <$> int
pInl = TmInl <$> ($(keyword "left") *> pTerm)
pInr = TmInr <$> ($(keyword "right") *> pTerm)
pCons = parens (TmCons <$> pTerm <* $(symbol ",") <*> pTerm)
pFold = parens ($(keyword "fold") *> (TmFold <$> pTerm))
pVar  = TmVar <$> ident
pApp  = parens (TmApp <$> pTermIso <*> pTerm)
pTermIso = TmIso <$> pIso
pAnn  = parens (TmAnn <$> pTerm <* $(symbol "::") <*> pType)
pTermLet = do
  $(keyword "let")
  lhs <- pTerm
  $(symbol' "=")
  rhs <- pTerm
  $(keyword' "in")
  body <- pTerm
  return $ TmLet lhs rhs body

pTerm = pUnit <|> pInt <|> pInl <|> pInr <|> pCons <|> pFold
  <|> pApp <|> pAnn <|> pTermLet <|> pVar <|> pTermIso

pTerm' = pTerm `cut'` (Msg "Term")

{-
-- Value
-}
pValUnit = pUnit
pValInt = pInt
pValInl = TmInl <$> ($(keyword "left") *> pValue)
pValInr = TmInr <$> ($(keyword "right") *> pValue)
pValCons = parens (TmCons <$> pValue <* $(symbol ",") <*> pValue)
pValFold = parens (TmFold <$> pValue)
pValVar  = pVar

pValue = pValUnit <|> pValInt <|> pValInl <|> pValInr <|> pValCons <|> pValFold <|> pValVar

pValue' =  pValue `cut'` (Msg "Value")

{-
-- Exp
-}
pExpVal = pValue

pExpLet = do
  $(keyword "let")
  pat <- pPattern
  $(symbol' "=")
  iso <- pTermIso
  pat' <- pPattern
  $(keyword' "in")
  body <- pExp
  return $ TmLet pat (TmApp iso pat') body

pExp = pExpLet <|> pExpVal

pExp' = pExp `cut'` (Msg "Exp")

{-
-- Pattern
-}
pPtSingleVar = pVar

pListOfVars  = brackets $ sepBy1 ident $(symbol' ",") 

pPtMultiVar  = TmVarList <$> pListOfVars

pPattern = pPtMultiVar <|> pPtSingleVar

pPattern' = pPattern `cut'` (Msg "Pattern")

{-
-- Iso
-}
pIsoClause = do
  lhs <- pValue'
  $(symbol' "<->")
  rhs <- pExp'
  return (lhs, rhs)

pIsoClauses = braces $ IsoClauses <$> (sepBy1 pIsoClause $(symbol ";"))

pIsoFix = do
  $(keyword "fix")
  var <- ident
  $(symbol' ".")
  iso <- pIso
  return $ IsoFix var iso

pIsoLam = do
  $(symbol "\\")
  var <- ident'
  $(symbol' "->")
  body <- pIso'
  return $ IsoLam var body

pIsoApp = parens (IsoApp <$> pIso <*> pIso)

pIsoVar = IsoVar <$> ident

pIso :: Parser Iso
pIso = pIsoClauses <|> pIsoLam <|> pIsoApp <|> pIsoFix <|> pIsoVar

pIso' = pIso `cut'` (Msg "Iso")

{-
-- Syntactic Checkers
-}
isTmValue :: Term -> Bool
isTmValue TmUnit           = True
isTmValue (TmInt n)        = True
isTmValue (TmInl a)        = isTmValue a
isTmValue (TmInr b)        = isTmValue b
isTmValue (TmCons a b)     = isTmValue a && isTmValue b
isTmValue (TmFold t)       = isTmValue t
isTmValue (TmVar _)        = True
isTmValue _                = False

isTmPattern :: Term -> Bool
isTmPattern (TmCons a b)     = isTmPattern a && isTmPattern b
isTmPattern (TmVar _)        = True
isTmPattern _                = False

isTmExp :: Term -> Bool
isTmExp (TmLet lhs (TmApp (TmIso f) x) body) =
  isTmPattern lhs && isTmPattern x && isTmExp body
isTmExp t = isTmValue t

isTmIso :: Term -> Bool
isTmIso (TmIso _) = True
isTmIso _         = False

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

load str =
  case parse pTerm str of
    OK t res -> if res == mempty then Just t
                 else error $ "load: remaining string unparsed " ++ show res
    _        -> Nothing

-- Testing base types
str0 = "Unit"
res0 = test pTyUnit str0

str1 = "(Int + Int)"
res1 = test pTySum str1

str2 = "mu x. Int"
res2 = test pType str2

str3 = "(mu var0  . Unit x Int)"
res3 = test pType str3

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
res9 = test pTerm str9

-- Testing expressions and patterns
str10 = "let x = f x in let y = g x in x"
res10 = test pExp str10

-- Isos
str11 = "{ 1 <-> 2 }"
res11 = test pIsoClauses str11

str12 = "\\f  -> { 1 <-> 2 ; x <-> let y = f x in y }"
res12 = test pIso str12

-- Terms
str13 = "(f 1)"
res13 = test pTerm str13

str14 = "((\\f -> { left unit <-> 0 ; x <-> let y = f x in y } \n\
         \ { right z <-> z }) 1)"
res14 = test pTerm str14
