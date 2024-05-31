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
pBTyList = BTyList <$> (brackets pBaseType)
pBTyVar = BTyVar <$> ident''
pBTyMu = do
  $(keyword "mu")
  var <- ident''
  $(symbol' ".")
  body <- pBaseType
  return $ BTyMu var body
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
  ty <- optional ($(symbol "x") *> pBaseType)
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

pMixTyUnit = GUnit <$ $(keyword "Unit")
pMixTyInt = GInt <$ $(keyword "Int")
pMixTyList = GList <$> (brackets pMixType)
pMixTyVar = GVar <$> ident''
pMixTyMu = do
  $(keyword "mu")
  var <- ident''
  $(symbol' ".")
  body <- pMixType
  return $ GMu var body
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
  ty <- optional ($(symbol "<->") *> pMixType)
  case ty of
    Just r -> return $ GDArr l r
    Nothing -> return l

pMixArrStart :: ParserT PureMode Error GType
pMixArrStart = do
  l <- pMixDArrStart
  ty <- optional ($(symbol "->") *> pMixType)
  case ty of
    Just r -> return $ GArr l r
    Nothing -> return l

pMixStart :: ParserT PureMode Error GType
pMixStart = do
  l <- pMixArrStart
  ty <- optional ($(symbol "x") *> pMixType)
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
pValUnit = ValUnit <$ $(keyword "unit")
pValInt  = ValInt <$> int
pValEmpty = ValEmpty <$ $(symbol "[") <* $(symbol "]")
pValVar  = ValVar <$> ident''
pValLInj = ValLInj <$> ($(keyword "left") *> pValStart)
pValRInj = ValRInj <$> ($(keyword "right") *> pValStart)
pValPair = angle (ValPair <$> pValue <* $(symbol ",") <*> pValue)
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
  rest <- optional ($(symbol "::") *> pBaseType)
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
  $(symbol' "::")
  $(symbol' "(")
  l <- pBaseType
  $(symbol "<->")
  r <- pBaseType
  $(symbol' ")")
  $(symbol' "->")
  iso <- pIso
  return $ IsoFix var l r iso

pIso = pIsoValue <|> pIsoLam <|> pIsoApp <|> pIsoFix <|> pIsoVar

{-
-- Term
-}
pTmUnit = TmUnit <$ $(keyword "unit")
pTmInt  = TmInt <$> int
pTmEmpty = TmEmpty <$ $(symbol "[") <* $(symbol "]")
pTmVar  = TmVar <$> ident''
pTmLInj = TmLInj <$> ($(keyword "left") *> pTmStart)
pTmRInj = TmRInj <$> ($(keyword "right") *> pTmStart)
pTmPair = angle (TmPair <$> pTerm <* $(symbol ",") <*> pTerm)
-- ^ above are alomost identical with pValue
pTmIsoApp = TmIsoApp <$> pIso <*> pTerm
pTmLet    = do
  $(keyword "let")
  pat <- pPattern
  $(symbol' "=")
  rhs <- pTerm
  $(keyword' "in")
  body <- pTerm
  return $ TmLet pat rhs body
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
  rest <- optional ($(symbol "::") *> pBaseType)
  case rest of
    Just ty -> return $ TmAnn first ty
    Nothing -> return first

{-
-- Definitions
-}
pDefType :: ParserT PureMode Error (Either IsoType Iso)
pDefType = do
  $(symbol "::")
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
