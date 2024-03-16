{-# LANGUAGE NoMonomorphismRestriction #-}
--{-# LANGUAGE GADTs #-}

module Parser where

import Data -- the AST
import Prelude hiding ((^), (||))
import Control.Applicative

data PrinterParser a = PrinterParser (a -> String)
                                     (String -> Maybe (a, String))

class FormatSpec repr where
  lit  :: String -> repr a a
  int  :: repr a (Int -> a)
  char :: repr a (Char -> a)
  fpp  :: PrinterParser b -> repr a (b -> a)
  (^)  :: repr b c -> repr a b -> repr a c

class Choice repr where
  triv  :: any -> repr a (any->a)
  (||)  :: repr a (x->a) -> repr a (y->a) -> repr a (Either x y -> a)

-- Printer
newtype FPr a b = FPr ((String -> a) -> b)

sprintf :: FPr String b -> b
sprintf (FPr format) = format id

instance FormatSpec FPr where
  lit str = FPr $ \k -> k str
  int     = FPr $ \k x -> k (show x)
  char    = FPr $ \k x -> k [x]
  fpp (PrinterParser pr _) = FPr $ \k x -> k (pr x)
  (FPr l) ^ (FPr r) = FPr $ \k -> l (\sl -> r (\sr -> k (sl ++ sr)))

instance Choice FPr where
  triv a = FPr $ \k _ -> k "" -- just discard

  (FPr l) || (FPr r) = 
    FPr $ \k e -> case e of
      Left x -> (flip l) x (\sl -> k sl)
      Right y -> (flip r) y (\sl -> k sl)


-- Parser
newtype FSc a b = FSc (String -> b -> Maybe (a, String))

sscanf :: FSc a b -> String -> b -> Maybe (a, String)
sscanf (FSc format) str k = format str k

removePrefix :: String -> String -> Maybe String
removePrefix long [] = Just long
removePrefix []   _  = Nothing
removePrefix (x:xs) (y:ys)
 | x == y    = removePrefix xs ys
 | otherwise = Nothing
 
instance FormatSpec FSc where
  lit str = FSc $ \inp k ->
    case removePrefix inp str of
      Just suffix -> Just (k, suffix)
      Nothing -> Nothing

  char = FSc $ \inp k ->
    case inp of
      (x : xs) -> Just (k x, xs)
      _        -> Nothing

  fpp (PrinterParser _ par) = FSc $ \inp k ->
    case par inp of
      Just (b, inp') -> Just (k b, inp')
      Nothing        -> Nothing

  int = fpp showread

  (FSc pl) ^ (FSc pr) = FSc $ \inp k ->
    case pl inp k of
      Just (k', inp') -> pr inp' k'
      _               -> Nothing

instance Choice FSc where
  triv a = FSc $ \inp k -> Just (k a, inp) -- feed `a` without touching input string

  (FSc l) || (FSc r) = FSc $ \inp k ->
    let kl = k . Left
        kr = k . Right
     in case l inp kl of
          Nothing -> r inp kr
          just -> just

-- Some helpers:
fmt :: (FormatSpec repr, Show b, Read b) => b -> repr a (b -> a)
fmt _ = fpp showread

-- casting `read` result from list to maybe
showread :: (Show a, Read a) => PrinterParser a
showread =
  PrinterParser show $
    \str -> case reads str of
      [(a, str')] -> Just (a, str')
      _ -> Nothing

paren spec = lit "(" ^ spec ^ lit ")"

-- translating Yafei's `show` instance:
baseTypeSpec BTyUnit = lit "Unit"
baseTypeSpec BTyInt = lit "Nat"
baseTypeSpec (BTyVar var) = lit var
baseTypeSpec (BTySum lt rt) = paren $ baseTypeSpec lt ^ lit " + " ^ baseTypeSpec rt
baseTypeSpec (BTyProd lt rt) = paren $ baseTypeSpec lt ^ lit " x " ^ baseTypeSpec rt
baseTypeSpec (BTyMu var bodyT) = lit "mu " ^ lit var ^ lit ". " ^ baseTypeSpec bodyT -- slightly changed position of '.'

baseTypeParser str =
  sscanf unitP str BTyUnit <|>
  sscanf intP  str BTyInt  <|>
  sscanf varP  str BTyVar  <|>
  sscanf sumP  str BTySum  <|>
  sscanf prodP str BTyProd <|>
  sscanf muP   str BTyMu   <|>
  Nothing
 where  
  unitP = baseTypeSpec BTyUnit
  intP  = baseTypeSpec BTyInt
  -- varP  = fmt ""  -- this would not work, needs a way to read a token. Q: how to read a string of indefinite length?
  varP  = fpp varPP
  sumP  = paren $ fpp baseTypePP ^ lit " + " ^ fpp baseTypePP
  prodP = paren $ fpp baseTypePP ^ lit " x " ^ fpp baseTypePP
  muP   = lit "mu " ^ varP ^ lit ". " ^ fpp baseTypePP

-- modifed variable name format to "var" ++ some int so parsing is convenient
varPP = PrinterParser show
                      (\inp -> sscanf (lit "Var" ^ int) inp (\x -> "Var" ++ show x))

baseTypePP =
  PrinterParser show
                baseTypeParser

baseTypeFmt = fpp baseTypePP
{-
-- tests
--}

x = 0
y = '0'
fmt00 = lit "ch" ^ (int || char)
print00x = sprintf fmt00 (Left x)
print00y = sprintf fmt00 (Right y)
str001 = "ch0123"
str002 = "chc"
parse001 = sscanf fmt00 str001 id
parse002 = sscanf fmt00 str002 id

str0 = "Unit"
fmt0 = baseTypeSpec BTyUnit
parse0 = sscanf fmt0 str0 "done"

str1 = "(mu Var0. Unit x Nat)"
fmt1 = baseTypeSpec (BTyProd (BTyMu "Var0" BTyUnit) (BTyInt))
parse10 = sscanf fmt1 str1 "done"
parse11 = sscanf baseTypeFmt str1 id
