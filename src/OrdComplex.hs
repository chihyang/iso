{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
module OrdComplex (module OrdComplex) where

import Data.Complex as C
import Data.Semiring (Semiring)

newtype OrdComplex a = OrdComplex (C.Complex a)
  deriving newtype (Show, Num, Fractional, Floating, Semiring)
  deriving stock (Eq)
instance (Ord a) => Ord (OrdComplex a) where
  compare (OrdComplex (r1 C.:+ i1)) (OrdComplex (r2 C.:+ i2)) =
    compare (r1, i1) (r2, i2)

pattern (:+) :: a -> a -> OrdComplex a
pattern r :+ i <- OrdComplex (r C.:+ i) where
  r :+ i = OrdComplex (r C.:+ i)

infix 6 :+

realPart :: OrdComplex a -> a
realPart (OrdComplex c) = C.realPart c

imagPart :: OrdComplex a -> a
imagPart (OrdComplex c) = C.imagPart c

-- Basic Functions
conjugate :: (Num a) => OrdComplex a -> OrdComplex a
conjugate (OrdComplex c) = OrdComplex (C.conjugate c)

-- Functions requiring RealFloat
magnitude :: (RealFloat a) => OrdComplex a -> a
magnitude (OrdComplex c) = C.magnitude c

phase :: (RealFloat a) => OrdComplex a -> a
phase (OrdComplex c) = C.phase c

polar :: (RealFloat a) => OrdComplex a -> (a, a)
polar (OrdComplex c) = C.polar c

cis :: (RealFloat a) => a -> OrdComplex a
cis theta = OrdComplex (C.cis theta)
