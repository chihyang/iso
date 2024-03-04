{-# LANGUAGE NoMonomorphismRestriction #-}

module Parser where

import Data -- the AST
import Prelude hiding ((^))


data PrinterParser a = PrinterParser (a -> String)
                                     (String -> Maybe (a, String))

class FormatSpec repr where
  lit  :: String -> repr a a
  int  :: repr a (Int -> a)
  char :: repr a (Char -> a)
  fpp  :: PrinterParser b -> repr a (b -> a)
  (^)  :: repr b c -> repr a b -> repr a c
  (|)  :: repr a c -> repr a b -> repr a (Either c b -> a)

-- Printer
newtype FPr a b = FPr ((String -> a) -> b)

sprintf :: FPr String b -> b
sprintf (FPr format) = format id

instance FormatSpec FPr where
    lit str = FPr $ \k -> k str
    int     = FPr $ \k x -> k (show x)
    char    = FPr $ \k x -> k [x]
    fpp (PrinterParser pr _) = FPr $ \k x -> k (pr x)
    (FPr a) ^ (FPr b) = FPr $ \k -> a (\sa -> b (\sb -> k (sa ++ sb)))
    (FPr a) | (FPr b) = FPr $ \k -> a


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


baseTypePP BTyUnit = lit "Unit"
baseTypePP BTyInt = lit "Nat"
baseTypePP (BTyVar var) = lit var
baseTypePP (BTySum lt rt) = paren $ baseTypePP lt ^ lit " + " ^ baseTypePP rt
baseTypePP (BTyProd lt rt) = paren $ baseTypePP lt ^ lit " x " ^ baseTypePP rt
baseTypePP (BTyMu var bodyT) = lit "mu " ^ lit var ^ lit ". " ^ baseTypePP bodyT

baseTypeWrapper bt str =
  case sscanf bt str "" of
    Just ("", "") -> Just bt
    _             -> Nothing

{-
-- tests
--}
str0 = "Unit"
fmt0 = baseTypePP BTyUnit
parse0 = sscanf fmt0 str0 ""

str1 = "(mu a. Unit x Nat)"
fmt1 = baseTypePP (BTyProd (BTyMu "a" BTyUnit) (BTyInt))
parse1 = sscanf fmt1 str1 ""
