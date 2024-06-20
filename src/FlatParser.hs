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
import Syntax as Syntax

moduleName :: String
moduleName = "Parser: "

-- General type for disambiguity
data GType =
  GUnit
  | GInt
  | GList GType
  | GVar String
  | GSum GType GType
  | GProd GType GType
  | GMu String GType
  | GDArr GType GType
  | GArr GType GType
  deriving (Eq, Ord)
instance Show GType where
  show GUnit = "Unit"
  show GInt = "Int"
  show (GList t) = "[" ++ show t ++ "]"
  show (GVar var) = var
  show (GSum lt rt) = "(" ++ show lt ++ " + " ++ show rt ++ ")"
  show (GProd lt rt) = "(" ++ show lt ++ " x " ++ show rt ++ ")"
  show (GMu var bodyT) = "Mu " ++ var ++ ". " ++ show bodyT
  show (GDArr lt rt) = "(" ++ show lt ++ " <-> " ++ show rt ++ ")"
  show (GArr vT bodyT) = show vT ++ " -> " ++ show bodyT

-- Parser is a type defined in the Lexer example
-- type Parser a = F.ParserT PureMode Error a
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
      "μ"    -> pure ()
      "fix"    -> pure ()
      "unit"  -> pure ()
      "left"  -> pure ()
      "right" -> pure ()
      "let"   -> pure ()
      "in"    -> pure () |])
  eof

ident :: Parser Name
ident = token $ byteStringOf $
  withSpan (identStartChar *> skipMany identChar) (\_ spn -> fails (isKeyword spn))

ident'' :: Parser String
ident'' = utf8ToStr <$> ident

dArrow :: ParserT PureMode Error ()
dArrow = $(symbol "<->") <|> $(symbol "↔")

arrow :: ParserT PureMode Error ()
arrow = $(symbol "->") <|> $(symbol "→")

prod :: ParserT PureMode Error ()
prod = $(symbol "x") <|> $(symbol "×")

dColon :: ParserT PureMode Error ()
dColon = $(symbol "::") <|> $(symbol "∷")

dColon' :: ParserT PureMode Error ()
dColon' = $(symbol' "::") <|> $(symbol' "∷")

mu :: ParserT PureMode Error ()
mu = $(keyword "mu") <|> $(keyword "μ")

-- use TH to write this so it's feasible to do `C <$> parens p` with nary
-- constructors?
parens :: ParserT PureMode Error a -> ParserT PureMode Error a
parens p = $(symbol "(") *> p <* $(symbol' ")")

brackets :: ParserT PureMode Error a -> ParserT PureMode Error a
brackets p = $(symbol "[") *> p <* $(symbol' "]")

braces :: ParserT PureMode Error a -> ParserT PureMode Error a
braces p = $(symbol "{") *> p <* $(symbol' "}")

angle :: ParserT PureMode Error a -> ParserT PureMode Error a
angle p = $(symbol "<") *> p <* $(symbol' ">")

{-
-- BaseType
-}
pBTyUnit :: ParserT PureMode Error BaseType
pBTyUnit = BTyUnit <$ $(keyword "Unit")

pBTyInt :: ParserT PureMode Error BaseType
pBTyInt = BTyInt <$ $(keyword "Int")

pBTyList :: ParserT PureMode Error BaseType
pBTyList = BTyList <$> (brackets pBaseType)

pBTyVar :: ParserT PureMode Error BaseType
pBTyVar = BTyVar <$> ident''

pBTyMu :: ParserT PureMode Error BaseType
pBTyMu = do
  mu
  var <- ident''
  $(symbol' ".")
  body <- pBaseType
  return $ BTyMu var body

pBTyParen :: ParserT PureMode Error BaseType
pBTyParen = parens pBaseType

pBaseProdStart :: ParserT PureMode Error BaseType
pBaseProdStart =
  pBTyUnit <|>
  pBTyInt <|>
  pBTyMu <|>
  pBTyVar <|>
  pBTyList <|>
  pBTyParen

pBaseStart :: ParserT PureMode Error BaseType
pBaseStart = do
  l <- pBaseProdStart
  ty <- optional (prod *> pBaseType)
  case ty of
    Just r -> return $ BTyProd l r
    Nothing -> return l

pBaseType :: ParserT PureMode Error BaseType
pBaseType = do
  l <- pBaseStart
  ty <- optional ($(symbol "+") *> pBaseType)
  case ty of
    Just r -> return $ BTySum l r
    Nothing -> return l

pMixTyUnit :: ParserT PureMode Error GType
pMixTyUnit = GUnit <$ $(keyword "Unit")

pMixTyInt :: ParserT PureMode Error GType
pMixTyInt = GInt <$ $(keyword "Int")

pMixTyList :: ParserT PureMode Error GType
pMixTyList = GList <$> (brackets pMixType)

pMixTyVar :: ParserT PureMode Error GType
pMixTyVar = GVar <$> ident''

pMixTyMu :: ParserT PureMode Error GType
pMixTyMu = do
  mu
  var <- ident''
  $(symbol' ".")
  body <- pMixType
  return $ GMu var body

pMixTyParen :: ParserT PureMode Error GType
pMixTyParen = parens pMixType

pMixProdStart :: ParserT PureMode Error GType
pMixProdStart =
  pMixTyUnit <|>
  pMixTyInt <|>
  pMixTyMu <|>
  pMixTyVar <|>
  pMixTyList <|>
  pMixTyParen

pMixDArrStart :: ParserT PureMode Error GType
pMixDArrStart = do
  l <- pMixProdStart
  ty <- optional (dArrow *> pMixType)
  case ty of
    Just r -> return $ GDArr l r
    Nothing -> return l

pMixArrStart :: ParserT PureMode Error GType
pMixArrStart = do
  l <- pMixDArrStart
  ty <- optional (arrow *> pMixType)
  case ty of
    Just r -> return $ GArr l r
    Nothing -> return l

pMixStart :: ParserT PureMode Error GType
pMixStart = do
  l <- pMixArrStart
  ty <- optional (prod *> pMixType)
  case ty of
    Just r -> return $ GProd l r
    Nothing -> return l

pMixType :: ParserT PureMode Error GType
pMixType = do
  l <- pMixStart
  ty <- optional ($(symbol "+") *> pMixType)
  case ty of
    Just r -> return $ GSum l r
    Nothing -> return l

g2Base :: GType -> Syntax.Result BaseType
g2Base GUnit = return BTyUnit
g2Base GInt = return BTyInt
g2Base (GList gty) = do
  bty <- g2Base gty
  return $ BTyList bty
g2Base (GVar var) = return (BTyVar var)
g2Base (GSum ty1 ty2) = do
  bty1 <- g2Base ty1
  bty2 <- g2Base ty2
  return $ BTySum bty1 bty2
g2Base (GProd ty1 ty2) = do
  bty1 <- g2Base ty1
  bty2 <- g2Base ty2
  return $ BTyProd bty1 bty2
g2Base (GMu var ty) = do
  bty <- g2Base ty
  return $ BTyMu var bty
g2Base (GDArr ty1 ty2) = Left $ moduleName ++ "Expect a base type, given an iso type: " ++ show (GDArr ty1 ty2)
g2Base (GArr ty1 ty2) = Left $ moduleName ++ "Expect a base type, given an iso type: " ++ show (GArr ty1 ty2)

g2Iso :: GType -> Syntax.Result IsoType
g2Iso (GDArr ty1 ty2) = do
  bty1 <- g2Base ty1
  bty2 <- g2Base ty2
  return $ (ITyBase bty1 bty2)
g2Iso (GArr ty1 ty2) = do
  ity1 <- g2Iso ty1
  case ity1 of
    (ITyBase bty1 bty2) -> do
      ity2 <- g2Iso ty2
      return $ ITyFun bty1 bty2 ity2
    ty -> Left $ moduleName ++ "Invalid argument type, expect a `<->` type, given: " ++ show ty
g2Iso ty = Left $ moduleName ++ "Invalid iso type, expect a `<->` or an `->` type, given: " ++ show ty

{-
-- Value
-}
pValUnit :: ParserT PureMode Error Value
pValUnit = ValUnit <$ $(keyword "unit")

pValInt :: ParserT PureMode Error Value
pValInt  = ValInt <$> int

pValEmpty :: ParserT PureMode Error Value
pValEmpty = ValEmpty <$ $(symbol "[") <* $(symbol "]")

pValVar :: ParserT PureMode Error Value
pValVar  = ValVar <$> ident''

pValLInj :: ParserT PureMode Error Value
pValLInj = ValLInj <$> ($(keyword "left") *> pValStart)

pValRInj :: ParserT PureMode Error Value
pValRInj = ValRInj <$> ($(keyword "right") *> pValStart)

pValPair :: ParserT PureMode Error Value
pValPair = angle (ValPair <$> pValue <* $(symbol ",") <*> pValue)

pValParen :: ParserT PureMode Error Value
pValParen = parens pValue

pValStart :: ParserT PureMode Error Value
pValStart = pListValColon

pListValColon :: ParserT PureMode Error Value
pListValColon = do
  tm <- pListVal
  tms <- many ($(symbol ":") *> pValStart)
  return $ makeColonVal (tm:tms)

makeColonVal :: [Value] -> Value
makeColonVal [] = error "Impossible case!"
makeColonVal [tm] = tm
makeColonVal (tm:tms) = ValCons tm (makeColonVal tms)

pListValComma :: ParserT PureMode Error Value
pListValComma = do
  $(symbol "[")
  tm <- pValue
  tms <- many ($(symbol ",") *> pValue)
  $(symbol "]")
  return $ makeCommaVal (tm:tms)

makeCommaVal :: [Value] -> Value
makeCommaVal [] = ValEmpty
makeCommaVal (tm:tms) = ValCons tm (makeCommaVal tms)

pListVal :: ParserT PureMode Error Value
pListVal =
  pValUnit <|>
  pValEmpty <|>
  pValInt <|>
  pValLInj <|>
  pValRInj <|>
  pValPair <|>
  pValVar <|>
  pListValComma <|>
  pValParen

pValue :: ParserT PureMode Error Value
pValue = do
  first <- pValStart
  rest <- optional (dColon *> pBaseType)
  case rest of
    Just ty -> return $ ValAnn first ty
    Nothing -> return first

{-
-- Exp
-}
pExpVal :: Parser Exp
pExpVal = ExpVal <$> pValue

pExpLet :: Parser Exp
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

pComplex :: Parser Scale
pComplex = do
  $(symbol "(")
  real <- pAllNumber
  $(symbol' ":+")
  imag <- pAllNumber
  $(symbol ")")
  return $ real C.:+ imag

pScale :: Parser Scale
pScale = pComplex <|> ((\r -> r :+ 0) <$> pNumber)

pExpScale :: Parser Exp
pExpScale = do
  scale <- pScale
  $(symbol "*")
  e <- pExp
  return $ ExpScale scale e

pExpAdd :: Parser Exp
pExpAdd = $(symbol "+") *> pExp

pExpSub :: Parser Exp
pExpSub = do
  $(symbol "-")
  v <- pExp
  return $ ExpScale ((-1.0) :+ 0) v

pExpAdditive :: Parser Exp
pExpAdditive = pExpAdd <|> pExpSub

pExpPlus :: Parser Exp
pExpPlus = do
  $(symbol "[")
  l <- pExp
  r <- pExpAdditive
  $(symbol "]")
  return $ ExpPlus [l,r]

pExp :: Parser Exp
pExp = pExpLet <|> pExpPlus <|> pExpScale <|> pExpVal

{-
-- Pattern
-}
pPtSingleVar :: ParserT PureMode Error Pattern
pPtSingleVar = PtSingleVar <$> ident''

-- Assume input syntax has at least 1 variable, otherwise fail
pListOfVars :: ParserT PureMode Error [String]
pListOfVars  = brackets $ do
  x1 <- ident''
  xs <- many ($(symbol' ",") *> ident'')
  return $ x1 : xs

pPtMultiVar :: ParserT PureMode Error Pattern
pPtMultiVar  = PtMultiVar <$> pListOfVars

pPattern :: ParserT PureMode Error Pattern
pPattern = pPtMultiVar <|> pPtSingleVar

{-
-- Iso
-}
pIsoClause :: ParserT PureMode Error (Value, Exp)
pIsoClause = do
  lhs <- pValue
  dArrow
  rhs <- pExp
  return (lhs, rhs)

-- !! `some` would not work here even for positive cases
pIsoValue :: ParserT PureMode Error Iso
pIsoValue = braces $ IsoValue <$> ((:) <$> pIsoClause <*> many ($(symbol ";") *> pIsoClause))

pIsoVar :: ParserT PureMode Error Iso
pIsoVar = IsoVar <$> ident''

pIsoLam :: ParserT PureMode Error Iso
pIsoLam = do
  $(symbol "\\")
  var <- ident''
  dColon'
  $(symbol' "(")
  l <- pBaseType
  dArrow
  r <- pBaseType
  $(symbol' ")")
  arrow
  body <- pIso
  return $ IsoLam var l r body

pIsoApp :: ParserT PureMode Error Iso
pIsoApp = brackets (IsoApp <$> pIso <*> pIso)

pIsoFix :: ParserT PureMode Error Iso
pIsoFix = do
  $(keyword "fix")
  var <- ident''
  dColon'
  $(symbol' "(")
  l <- pBaseType
  dArrow
  r <- pBaseType
  $(symbol' ")")
  arrow
  iso <- pIso
  return $ IsoFix var l r iso

pIso :: ParserT PureMode Error Iso
pIso = pIsoValue <|> pIsoLam <|> pIsoApp <|> pIsoFix <|> pIsoVar

{-
-- Term
-}
pTmUnit :: ParserT PureMode Error Term
pTmUnit = TmUnit <$ $(keyword "unit")

pTmInt :: ParserT PureMode Error Term
pTmInt  = TmInt <$> int

pTmEmpty :: ParserT PureMode Error Term
pTmEmpty = TmEmpty <$ $(symbol "[") <* $(symbol "]")

pTmVar :: ParserT PureMode Error Term
pTmVar  = TmVar <$> ident''

pTmLInj :: ParserT PureMode Error Term
pTmLInj = TmLInj <$> ($(keyword "left") *> pTmStart)

pTmRInj :: ParserT PureMode Error Term
pTmRInj = TmRInj <$> ($(keyword "right") *> pTmStart)

pTmPair :: ParserT PureMode Error Term
pTmPair = angle (TmPair <$> pTerm <* $(symbol ",") <*> pTerm)

-- ^ above are alomost identical with pValue
pTmIsoApp :: ParserT PureMode Error Term
pTmIsoApp = TmIsoApp <$> pIso <*> pTerm

pTmLet :: ParserT PureMode Error Term
pTmLet    = do
  $(keyword "let")
  pat <- pPattern
  $(symbol' "=")
  rhs <- pTerm
  $(keyword' "in")
  body <- pTerm
  return $ TmLet pat rhs body

pTmParen :: ParserT PureMode Error Term
pTmParen = parens pTerm

-- left recursive case
pTmStart :: ParserT PureMode Error Term
pTmStart = pListTmColon

pListTmColon :: ParserT PureMode Error Term
pListTmColon = do
  tm <- pListTm
  tms <- many ($(symbol ":") *> pTmStart)
  return $ makeColonList (tm:tms)

makeColonList :: [Term] -> Term
makeColonList [] = error "Impossible case!"
makeColonList [tm] = tm
makeColonList (tm:tms) = TmCons tm (makeColonList tms)

pListTmComma :: ParserT PureMode Error Term
pListTmComma = do
  $(symbol "[")
  tm <- pTerm
  tms <- many ($(symbol ",") *> pTerm)
  $(symbol "]")
  return $ makeCommaList (tm:tms)

makeCommaList :: [Term] -> Term
makeCommaList [] = TmEmpty
makeCommaList (tm:tms) = TmCons tm (makeCommaList tms)

pListTm :: ParserT PureMode Error Term
pListTm =
  pTmUnit <|>
  pTmEmpty <|>
  pTmInt <|>
  pTmLInj <|>
  pTmRInj <|>
  pTmPair <|>
  pTmIsoApp <|>
  pTmLet <|>
  pTmVar <|>
  pListTmComma <|>
  pTmParen

pTerm :: ParserT PureMode Error Term
pTerm = do
  first <- pTmStart
  rest <- optional (dColon *> pBaseType)
  case rest of
    Just ty -> return $ TmAnn first ty
    Nothing -> return first

{-
-- Definitions
-}
pDefType :: ParserT PureMode Error (Either IsoType Iso)
pDefType = do
  dColon
  ty <- pMixType
  case g2Iso ty of
    Right ity -> return $ Left ity
    Left msg -> do
      pos <- getPos
      err $ Imprecise pos [Msg msg]

pDefIso :: ParserT PureMode Error (Either IsoType Iso)
pDefIso = do
  $(symbol "=")
  iso <- pIso
  return $ Right iso

pDef :: ParserT PureMode Error (String, Declaration)
pDef = do
  var <- ident''
  val <- (pDefType <|> pDefIso)
  return $ (var, val)

{-
-- Program
-}
pPgTm :: Parser Program
pPgTm = PgTm <$> pTerm

pPgIs :: Parser Program
pPgIs = PgIs <$> pIso

pProg :: Parser Program
pProg = pPgIs <|> pPgTm

pDefsPg :: Parser (Declarations, Program)
pDefsPg = ws *> (do
  decs <- many pDef
  pg <- pProg
  return (decs, pg)) <* eof

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
