-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE BangPatterns #-}

-- | This module provides type classes for rings. It also provides
-- several specific instances of rings, such as the ring ℤ₂ of
-- integers modulo 2, the ring ℚ of rational numbers, the ring ℤ[½] of
-- dyadic fractions, the ring ℤ[/i/] of Gaussian integers, the ring
-- ℤ[√2] of quadratic integers with radix 2, and the ring ℤ[ω] of
-- cyclotomic integers of degree 8.

module Libraries.Synthesis.Ring where

import Data.Bits
import Data.Complex
import Data.Ratio

-- ----------------------------------------------------------------------
-- * Rings

-- | A type class to denote rings. We make 'Ring' a synonym of
-- Haskell's 'Num' type class, so that we can use the usual notation
-- '+', '-', '*' for the ring operations.  This is not a perfect fit,
-- because Haskell's 'Num' class also contains two non-ring operations
-- 'abs' and 'signum'.  By convention, for rings where these notions
-- don't make sense (or are inconvenient to define), we set 'abs' /x/
-- = /x/ and 'signum' /x/ = 1.

class (Num a) => Ring a
instance (Num a) => Ring a

-- ----------------------------------------------------------------------
-- * Rings with particular elements

-- $ We define several classes of rings with special elements.

-- ----------------------------------------------------------------------
-- ** Rings with ½

-- | A type class for rings that contain ½.
class (Ring a) => HalfRing a where
  -- | The value ½.
  half :: a

instance HalfRing Double where
  half = 0.5

instance HalfRing Float where
  half = 0.5

instance HalfRing Rational where
  half = 1%2

instance (HalfRing a, RealFloat a) => HalfRing (Complex a) where
  half = half :+ 0

-- ----------------------------------------------------------------------
-- ** Rings with √2

-- | A type class for rings that contain √2.
class (Ring a) => RootTwoRing a where
  -- | The square root of 2.
  roottwo :: a
  
instance RootTwoRing Double where
  roottwo = sqrt 2

instance RootTwoRing Float where
  roottwo = sqrt 2

instance (RootTwoRing a, RealFloat a) => RootTwoRing (Complex a) where
  roottwo = roottwo :+ 0

-- ----------------------------------------------------------------------
-- ** Rings with 1\/√2

-- | A type class for rings that contain 1\/√2.
class (HalfRing a, RootTwoRing a) => RootHalfRing a where
  -- | The square root of ½.
  roothalf :: a
  
instance RootHalfRing Double where
  roothalf = sqrt 0.5

instance RootHalfRing Float where
  roothalf = sqrt 0.5

instance (RootHalfRing a, RealFloat a) => RootHalfRing (Complex a) where
  roothalf = roothalf :+ 0


-- ----------------------------------------------------------------------
-- ** Rings with /i/

-- | A type class for rings that contain a square root of -1.
class (Ring a) => ComplexRing a where
  -- | The complex unit.
  i :: a
       
instance (Ring a, RealFloat a) => ComplexRing (Complex a) where
  i = 0 :+ 1

-- ----------------------------------------------------------------------
-- ** Rings with ω

-- | A type class for rings that contain a square root of /i/, or
-- equivalently, a fourth root of −1.
class (Ring a) => OmegaRing a where
  -- | The square root of /i/.
  omega :: a
  
instance (ComplexRing a, RootHalfRing a) => OmegaRing a where
  omega = roothalf * (1 + i)

-- ----------------------------------------------------------------------
-- * Rings with particular automorphisms

-- ----------------------------------------------------------------------
-- ** Rings with complex conjugation

-- | A type class for rings with complex conjugation, i.e., an
-- automorphism mapping /i/ to −/i/. 
-- 
-- When instances of this type class are vectors or matrices, the
-- conjugation also exchanges the roles of rows and columns (in other
-- words, it is the adjoint).
-- 
-- For rings that are not complex, the conjugation can be defined to
-- be the identity function.
class Adjoint a where
  -- | Compute the adjoint (complex conjugate transpose).
  adj :: a -> a

instance Adjoint Integer where
  adj x = x
  
instance Adjoint Int where
  adj x = x
  
instance Adjoint Double where
  adj x = x
  
instance Adjoint Float where
  adj x = x
  
instance Adjoint Rational where  
  adj x = x
  
instance (Adjoint a, Ring a) => Adjoint (Complex a) where
  adj (a :+ b) = adj a :+ (-adj b)

-- ----------------------------------------------------------------------
-- ** Rings with √2-conjugation

-- | A type class for rings with a √2-conjugation, i.e., an
-- automorphism mapping √2 to −√2. 
-- 
-- When instances of this type class are vectors or matrices, the
-- √2-conjugation does /not/ exchange the roles of rows and columns.
-- 
-- For rings that have no √2, the conjugation can be defined to be the
-- identity function.
class Adjoint2 a where
  -- | Compute the adjoint, mapping /a/ + /b/√2 to /a/ −/b/√2.
  adj2 :: a -> a

instance Adjoint2 Integer where
  adj2 x = x

instance Adjoint2 Int where
  adj2 x = x
  
instance Adjoint2 Double where
  adj2 x = x
  
instance Adjoint2 Float where
  adj2 x = x
  
instance Adjoint2 Rational where  
  adj2 x = x
  
-- ----------------------------------------------------------------------
-- * Normed rings

-- | A (number-theoretic) /norm/ on a ring /R/ is a function /N/ : /R/
-- → ℤ such that /N/(/rs/) = /N/(/r/)/N/(/s/), for all /r/, /s/ ∈ /R/.
-- The norm also satisfies /N/(/r/) = 0 iff /r/ = 0, and /N/(/r/) = ±1
-- iff /r/ is a unit of the ring.
class (Ring r) => NormedRing r where
  norm :: r -> Integer
  
instance NormedRing Integer where
  norm x = x
  
-- ----------------------------------------------------------------------
-- * Floor and ceiling
  
-- | The 'floor' and 'ceiling' functions provided by the standard
-- Haskell libraries are predicated on many unnecessary assumptions.
-- This type class provides an alternative.
-- 
-- Minimal complete definition: 'floor_of' or 'ceiling_of'.
class (Ring r) => Floor r where
  -- | Compute the floor of /x/, i.e., the greatest integer /n/ such
  -- that /n/ ≤ /x/.
  floor_of :: r -> Integer
  floor_of x = -(ceiling_of (-x))
  -- | Compute the ceiling of /x/, i.e., the least integer /n/ such
  -- that /x/ ≤ /n/.
  ceiling_of :: r -> Integer
  ceiling_of x = -(floor_of (-x))

instance Floor Integer where
  floor_of = id
  ceiling_of = id

instance Floor Rational where
  floor_of = floor
  ceiling_of = ceiling

instance Floor Float where
  floor_of = floor
  ceiling_of = ceiling

instance Floor Double where
  floor_of = floor
  ceiling_of = ceiling

-- ----------------------------------------------------------------------
-- * Particular rings

-- ----------------------------------------------------------------------
-- ** The ring ℤ₂ of integers modulo 2

-- | The ring ℤ₂ of integers modulo 2. 
data Z2 = Even | Odd
        deriving (Eq)
                     
instance Show Z2 where
  show Even = "0"
  show Odd = "1"

instance Num Z2 where
  Even + x = x
  x + Even = x
  Odd + Odd = Even
  Even * x = Even
  x * Even = Even
  Odd * Odd = Odd
  negate x = x
  fromInteger n = if even n then Even else Odd
  abs x = x
  signum x = 1

instance Adjoint Z2 where
  adj x = x

instance Adjoint2 Z2 where
  adj2 x = x

-- ----------------------------------------------------------------------
-- ** The ring [bold D] of dyadic rationals

-- | A dyadic rational is a rational number whose denominator is a
-- power of 2. We denote the dyadic rationals by [bold D] = ℤ[½].
-- 
-- We internally represent a dyadic rational /a/\/2[sup /n/] as a pair
-- (/a/,/n/). Note that this representation is not unique. When it is
-- necessary to choose a canonical representative, we choose the least
-- possible /n/≥0.
data Dyadic = Dyadic !Integer !Integer

-- | Given a dyadic rational /r/, return (/a/,/n/) such that /r/ =
-- /a/\/2[sup /n/], where /n/≥0 is chosen as small as possible.
decompose_dyadic :: Dyadic -> (Integer, Integer)
decompose_dyadic (Dyadic a n) 
  | a == 0 = (0, 0)
  | n >= k = (b, n-k)
  | otherwise = (shiftL b (fromInteger (k-n)), 0)
  where
    (b,k) = lobit a

-- | Given a dyadic rational /r/ and an integer /k/≥0, such that /a/ =
-- /r/2[sup /k/] is an integer, return /a/. If /a/ is not an integer,
-- the behavior is undefined.
integer_of_dyadic :: Dyadic -> Integer -> Integer
integer_of_dyadic (Dyadic a n) k =
  shift a (fromInteger (k-n))

instance Real Dyadic where
  toRational (Dyadic a n) 
    | n >= 0    = a % 2^n
    | otherwise = a * 2^(-n) % 1

instance Show Dyadic where
  showsPrec d a = showsPrec_rational d (toRational a)

instance Eq Dyadic where
  Dyadic a n == Dyadic b m = a * 2^(k-n) == b * 2^(k-m) where
    k = max n m

instance Ord Dyadic where
  compare (Dyadic a n) (Dyadic b m) = compare (a * 2^(k-n)) (b * 2^(k-m)) where
    k = max n m

instance Num Dyadic where
  Dyadic a n + Dyadic b m 
    | n < m     = Dyadic c m
    | otherwise = Dyadic d n
    where
      c = shiftL a (fromInteger (m-n)) + b
      d = a + shiftL b (fromInteger (n-m))
  Dyadic a n * Dyadic b m = Dyadic (a*b) (n+m)
  negate (Dyadic a n) = Dyadic (-a) n
  abs x = if x >= 0 then x else -x
  signum x = case compare 0 x of { LT -> 1; EQ -> 0; GT -> -1 }
  fromInteger n = Dyadic n 0

instance HalfRing Dyadic where
  half = Dyadic 1 1

instance Adjoint Dyadic where
  adj x = x

instance Adjoint2 Dyadic where
  adj2 x = x

-- | The unique ring homomorphism from ℤ[½] to any ring containing
-- ½. This exists because ℤ[½] is the free such ring.

-- Implementation note: we can't just use fromInteger a * half^n,
-- because this can give potentially bad round-off errors in case
-- half^n underflows in the target type. Moreover, this does not work
-- if n is negative.
fromDyadic :: (HalfRing a) => Dyadic -> a
fromDyadic x = aux (fromInteger a) n where
  (a,n) = decompose_dyadic x
  aux !a !n
    | n>0       = aux (half*a) (n-1)
    | n==0      = a
    | otherwise = aux (2*a) (n+1)

-- ----------------------------------------------------------------------
-- ** The ring ℚ of rational numbers

-- | We define our own variant of the rational numbers, which is an
-- identical copy of the type 'Rational' from the standard Haskell
-- library, except that it has a more sensible 'Show' instance.
newtype Rationals = ToRationals { unRationals :: Rational }
                  deriving (Num, Eq, Ord, Fractional, Real, RealFrac, HalfRing, Adjoint, Adjoint2, ToEComplex, Floor)

-- | An auxiliary function for printing rational numbers, using
-- correct precedences, and omitting denominators of 1.
showsPrec_rational :: (Show a, Integral a) => Int -> Ratio a -> ShowS
showsPrec_rational d a
  | denom == 1 = showsPrec d numer
  | numer < 0  = showParen (d > 5) $ showString "-" . showsPrec_rational 6 (-a)
  | otherwise  = showParen (d > 6) $
                 showsPrec 7 numer . showString "/" . showsPrec 7 denom
    where
      numer = numerator a
      denom = denominator a

instance Show Rationals where
  showsPrec d (ToRationals a) = showsPrec_rational d a

-- | Conversion from 'Rationals' to any 'Fractional' type.
fromRationals :: (Fractional a) => Rationals -> a
fromRationals = fromRational . unRationals

-- ----------------------------------------------------------------------
-- ** The ring /R/[√2]
  
-- | The ring /R/[√2], where /R/ is any ring. The value 'RootTwo' /a/
-- /b/ represents /a/ + /b/ √2.
data RootTwo a = RootTwo !a !a
                deriving (Eq)

instance (Eq a, Num a) => Num (RootTwo a) where
  RootTwo a b + RootTwo a' b' = RootTwo a'' b'' where
    a'' = a + a'
    b'' = b + b'
  RootTwo a b * RootTwo a' b' = RootTwo a'' b'' where
    a'' = a * a' + 2 * b * b'
    b'' = a * b' + a' * b
  negate (RootTwo a b) = RootTwo a' b' where
    a' = -a
    b' = -b
  fromInteger n = RootTwo n' 0 where
    n' = fromInteger n
  abs f = f * signum f
  signum f@(RootTwo a b)
    | sa == 0 && sb == 0 = 0
    | sa /= -1 && sb /= -1 = 1
    | sa /= 1 && sb /= 1 = -1
    | sa /= -1 && sb /= 1 && signum (a*a - 2*b*b) /= -1 = 1
    | sa /= 1 && sb /= -1 && signum (a*a - 2*b*b) /= 1  = 1
    | otherwise = -1
    where
      sa = signum a
      sb = signum b

instance (Eq a, Ring a) => Ord (RootTwo a) where
  x <= y  =  signum (y-x) /= (-1)
  
instance (Show a, Eq a, Ring a) => Show (RootTwo a) where
  showsPrec d (RootTwo a 0) = showsPrec d a
  showsPrec d (RootTwo 0 1) = showString "√2"
  showsPrec d (RootTwo 0 (-1)) = showParen (d > 5) $ showString "-√2"
  showsPrec d (RootTwo 0 b) = showParen (d > 10) $ 
    showsPrec 11 b . showString " √2"
  showsPrec d (RootTwo a b) | signum b == 1 = showParen (d > 6) $
    showsPrec 7 a . showString " + " . showsPrec 7 (RootTwo 0 b)
  showsPrec d (RootTwo a b) | otherwise = showParen (d > 6) $
    showsPrec 7 a . showString " - " . showsPrec 7 (RootTwo 0 (-b))

instance (Eq a, Adjoint2 a, Fractional a) => Fractional (RootTwo a) where
  recip y = RootTwo (a/k) (b/k) where
    RootTwo k _ = y * adj2 y
    RootTwo a b = adj2 y
  fromRational r = fromInteger a / fromInteger b where
    a = numerator r
    b = denominator r

instance (Eq a, Ring a) => RootTwoRing (RootTwo a) where
  roottwo = RootTwo 0 1

instance (Eq a, HalfRing a) => HalfRing (RootTwo a) where
  half = RootTwo half 0
  
instance (Eq a, HalfRing a) => RootHalfRing (RootTwo a) where
  roothalf = RootTwo 0 half
  
instance (Eq a, ComplexRing a) => ComplexRing (RootTwo a) where
  i = RootTwo i 0

instance (Adjoint a) => Adjoint (RootTwo a) where  
  adj (RootTwo a b) = RootTwo (adj a) (adj b)

instance (Adjoint2 a, Num a) => Adjoint2 (RootTwo a) where  
  adj2 (RootTwo a b) = RootTwo (adj2 a) (-adj2 b)

instance (Eq a, NormedRing a) => NormedRing (RootTwo a) where
  norm (RootTwo a b) = (norm a)^2 - 2 * (norm b)^2

-- ----------------------------------------------------------------------
-- ** The ring ℤ[√2]

-- | The ring ℤ[√2].
type DInteger = RootTwo Integer

-- | The unique ring homomorphism from ℤ[√2] to any ring containing
-- √2. This exists because ℤ[√2] is the free such ring.
fromDInteger :: (RootTwoRing a) => DInteger -> a
fromDInteger (RootTwo x y) = fromInteger x + roottwo * fromInteger y

-- ----------------------------------------------------------------------
-- ** The ring ℤ[1\/√2]

-- | The ring ℤ[1\/√2]. We think of the elements of ℤ[1\/√2] as
-- (certain) exact real numbers. The \"D\" stands for \"dyadic\".
type DReal = RootTwo Dyadic

-- | The unique ring homomorphism from ℤ[1\/√2] to any ring containing
-- 1\/√2. This exists because ℤ[1\/√2] is the free such ring.
fromDReal :: (RootHalfRing a) => DReal -> a
fromDReal (RootTwo x y) = fromDyadic x + roottwo * fromDyadic y

-- ----------------------------------------------------------------------
-- ** The field ℚ[√2]

-- | The field ℚ[√2]. We think of the elements of ℚ[√2] as (certain)
-- exact real numbers, so the \"E\" stands for \"exact\".
type EReal = RootTwo Rationals

instance Floor EReal where
  floor_of x@(RootTwo a b)
    | r'+1 <= x  = r+1
    | r' <= x    = r
    | otherwise = r-1 
   where 
    a' = floor a
    b' = intsqrt (floor (2 * b^2))
    r | b >= 0    = a' + b'
      | otherwise = a' - b'
    r' = fromInteger r

-- | The unique ring homomorphism from ℚ[√2] to any ring containing
-- the rational numbers and √2. This exists because ℚ[√2] is the free
-- such ring.
fromEReal :: (RootTwoRing a, Fractional a) => EReal -> a
fromEReal (RootTwo x y) = fromRationals x + roottwo * fromRationals y

-- ----------------------------------------------------------------------
-- ** The ring /R/[/i/]

-- | The ring /R/[/i/], where /R/ is any ring. The reason we do not
-- use the 'Complex' /a/ type from the standard Haskell libraries is
-- that it assumes too much, for example, it assumes /a/ is a member
-- of the 'RealFloat' class. Also, this allows us to define a more
-- sensible 'Show' instance.
data Cplx a = Cplx !a !a
            deriving (Eq)

instance (Eq a, Show a, Num a) => Show (Cplx a) where
  showsPrec d (Cplx a 0) = showsPrec d a
  showsPrec d (Cplx 0 1) = showString "i"
  showsPrec d (Cplx 0 (-1)) = showParen (d > 5) $ showString "-i"
  showsPrec d (Cplx 0 b) = showParen (d > 10) $ 
    showsPrec 11 b . showString " i"
  showsPrec d (Cplx a b) | signum b == 1 = showParen (d > 6) $
    showsPrec 7 a . showString " + " . showsPrec 7 (Cplx 0 b)
  showsPrec d (Cplx a b) | otherwise = showParen (d > 6) $
    showsPrec 7 a . showString " - " . showsPrec 7 (Cplx 0 (-b))

instance (Num a) => Num (Cplx a) where
  Cplx a b + Cplx a' b' = Cplx a'' b'' where
    a'' = a + a'
    b'' = b + b'
  Cplx a b * Cplx a' b' = Cplx a'' b'' where
    a'' = a * a' - b * b'
    b'' = a * b' + a' * b
  negate (Cplx a b) = Cplx a' b' where
    a' = -a
    b' = -b
  fromInteger n = Cplx n' 0 where
    n' = fromInteger n
  abs x = x
  signum x = 1

instance (Fractional a) => Fractional (Cplx a) where
  fromRational a = Cplx (fromRational a) 0
  recip (Cplx a b) = Cplx (a/d) (-b/d) where
    d = a^2 + b^2

instance (Ring a) => ComplexRing (Cplx a) where
  i = Cplx 0 1

instance (HalfRing a) => HalfRing (Cplx a) where
  half = Cplx half 0

instance (RootHalfRing a) => RootHalfRing (Cplx a) where
  roothalf = Cplx roothalf 0

instance (RootTwoRing a) => RootTwoRing (Cplx a) where
  roottwo = Cplx roottwo 0

instance (Adjoint a, Ring a) => Adjoint (Cplx a) where
  adj (Cplx a b) = (Cplx (adj a) (-(adj b)))

instance (Adjoint2 a, Ring a) => Adjoint2 (Cplx a) where
  adj2 (Cplx a b) = (Cplx (adj2 a) (adj2 b))

instance (NormedRing a) => NormedRing (Cplx a) where
  norm (Cplx a b) = (norm a)^2 + (norm b)^2

-- ----------------------------------------------------------------------
-- ** The ring ℤ[/i/] of Gaussian integers

-- | The ring ℤ[/i/] of Gaussian integers.
type ZComplex = Cplx Integer

-- | The unique ring homomorphism from ℤ[/i/] to any ring containing
-- /i/. This exists because ℤ[/i/] is the free such ring.
fromZComplex :: (ComplexRing a) => ZComplex -> a
fromZComplex (Cplx a b) = fromInteger a + i * fromInteger b

-- ----------------------------------------------------------------------
-- ** The ring ℤ[1\/√2, /i/]

-- | The ring ℤ[1\/√2, /i/]. We think of the elements as (certain)
-- exact complex numbers. The \"D\" stands for \"dyadic\".
type DComplex = Cplx DReal

-- | The unique ring homomorphism from ℤ[1\/√2, /i/] to any ring containing
-- 1\/√2 and /i/. This exists because ℤ[1\/√2, /i/] is the free such ring.
fromDComplex :: (RootHalfRing a, ComplexRing a) => DComplex -> a
fromDComplex (Cplx a b) = fromDReal a + i * fromDReal b

-- ----------------------------------------------------------------------
-- ** The ring ℚ[√2, /i/]

-- | The field ℚ[√2, /i/]. We think of the elements as (certain) exact
-- complex numbers, hence the \"E\" in the name.
type EComplex = Cplx EReal

-- | The unique ring homomorphism from ℚ[√2, /i/] to any ring
-- containing the rational numbers, √2, and /i/. This exists because
-- ℚ[√2, /i/] is the free such ring.
fromEComplex :: (RootTwoRing a, ComplexRing a, Fractional a) => EComplex -> a
fromEComplex (Cplx a b) = fromEReal a + i * fromEReal b

-- ----------------------------------------------------------------------
-- ** The ring ℂ of complex numbers

-- $ We provide two versions of the complex numbers using floating
-- point arithmetic.

-- | Double precision complex floating point numbers.
type CDouble = Cplx Double

-- | Single precision complex floating point numbers.
type CFloat = Cplx Float

-- ----------------------------------------------------------------------
-- ** The ring /R/[ω]

-- | The ring /R/[ω], where /R/ is any ring, and ω is an 8th root of
-- unity. The value 'Omega' /a/ /b/ /c/ /d/ represents 
-- /a/ω[sup 3]+/b/ω[sup 2]+/c/ω+/d/.
data Omega a = Omega !a !a !a !a
            deriving (Eq)

-- | An inverse to the embedding /R/ ↦ /R/[ω]: return the \"real
-- rational\" part.
omega_real :: Omega a -> a
omega_real (Omega a b c d) = d

instance (Show a, Ring a) => Show (Omega a) where
  show (Omega a b c d) = "Ω" ++ show (a,b,c,d)

instance (Num a) => Num (Omega a) where
  Omega a b c d + Omega a' b' c' d' = Omega a'' b'' c'' d'' where
    a'' = a + a'
    b'' = b + b'
    c'' = c + c'
    d'' = d + d'
  Omega a b c d * Omega a' b' c' d' = Omega a'' b'' c'' d'' where  
    a'' = a*d' + b*c' + c*b' + d*a'
    b'' = b*d' + c*c' + d*b' - a*a'
    c'' = c*d' + d*c' - a*b' - b*a'
    d'' = d*d' - a*c' - b*b' - c*a'
  negate (Omega a b c d) = Omega (-a) (-b) (-c) (-d) where
  fromInteger n = Omega 0 0 0 n' where
    n' = fromInteger n
  abs x = x
  signum x = 1

instance (HalfRing a) => HalfRing (Omega a) where
  half = Omega 0 0 0 half

instance (HalfRing a) => RootHalfRing (Omega a) where
  roothalf = Omega (-half) 0 half 0

instance (Ring a) => RootTwoRing (Omega a) where
  roottwo = Omega (-1) 0 1 0

instance (Ring a) => ComplexRing (Omega a) where
  i = Omega 0 1 0 0

instance (Adjoint a, Ring a) => Adjoint (Omega a) where
  adj (Omega a b c d) = Omega (-(adj c)) (-(adj b)) (-(adj a)) (adj d)

instance (Adjoint2 a, Ring a) => Adjoint2 (Omega a) where
  adj2 (Omega a b c d) = Omega (-adj2 a) (adj2 b) (-adj2 c) (adj2 d)

instance (NormedRing a) => NormedRing (Omega a) where
  norm (Omega x y z w) = (a^2+b^2+c^2+d^2)^2-2*(a*b+b*c+c*d-d*a)^2
    where
      a = norm x
      b = norm y
      c = norm z
      d = norm w

-- This is an undecidable instance, but is not overlapping. Note: we
-- do not declare OmegaRing (Omega a), because this usually follows
-- from (ComplexRing a, RootHalfRing a). But there are some
-- exceptions, such as OmegaRing (Omega Z2) and OmegaRing (Omega
-- Integer).
instance OmegaRing (Omega Z2) where
  omega = Omega 0 0 1 0

-- ----------------------------------------------------------------------
-- ** The ring ℤ[ω]

-- | The ring ℤ[ω] of /cyclotomic integers/ of degree 8. Such rings
-- were first studied by Kummer around 1840, and used in his proof of
-- special cases of Fermat's Last Theorem.  See also:
-- 
-- * <http://fermatslasttheorem.blogspot.com/2006/05/basic-properties-of-cyclotomic.html>
-- 
-- * <http://fermatslasttheorem.blogspot.com/2006/02/cyclotomic-integers.html>
-- 
-- * Harold M. Edwards, \"Fermat's Last Theorem: A Genetic
-- Introduction to Algebraic Number Theory\"
type ZOmega = Omega Integer

-- | The unique ring homomorphism from ℤ[ω] to any ring containing
-- ω. This exists because ℤ[ω] is the free such ring.
fromZOmega :: (OmegaRing a) => ZOmega -> a
fromZOmega (Omega a b c d) = fromInteger a * omega^3 + fromInteger b * omega^2 + fromInteger c * omega + fromInteger d

-- This is an undecidable instance, but is not overlapping.
instance OmegaRing ZOmega where
  omega = Omega 0 0 1 0

-- | Inverse of the embedding ℤ[√2] → ℤ[ω]. Note that ℤ[√2] = ℤ[ω] ∩
-- ℝ. This function takes an element of ℤ[ω] that is real, and
-- converts it to an element of ℤ[√2]. It throws an error if the input
-- is not real.
dinteger_of_zomega :: ZOmega -> DInteger
dinteger_of_zomega (Omega a b c d)
  | a == -c && b == 0  = RootTwo d c
  | otherwise = error "dinteger_of_zomega: non-real value"
  
-- ----------------------------------------------------------------------
-- ** The ring [bold D][ω]

-- | The ring [bold D][ω]. Here [bold D]=ℤ[½] is the ring of dyadic
-- fractions. In fact, [bold D][ω] is isomorphic to the ring ℤ[1\/√2,
-- i], but they have different 'Show' instances.
type DOmega = Omega Dyadic

-- | The unique ring homomorphism from [bold D][ω] to any ring containing
-- 1\/√2 and /i/. This exists because [bold D][ω] is the free such ring.
fromDOmega :: (RootHalfRing a, ComplexRing a) => DOmega -> a
fromDOmega (Omega a b c d) = fromDyadic a * omega^3 + fromDyadic b * omega^2 + fromDyadic c * omega + fromDyadic d

-- This is an overlapping instance. It is nicer to show an element of
-- D[ω] by pulling out a common denominator exponent. But in cases
-- where the typechecker cannot infer this, then it will just fall
-- back to the more general method.
instance Show DOmega where
  showsPrec = showsPrec_DenomExp
  
-- This is an overlapping instance. See previous comment.
instance Show DComplex where
  showsPrec = showsPrec_DenomExp

-- ----------------------------------------------------------------------
-- ** The field ℚ[ω]

-- | The field ℚ[ω] of /cyclotomic rationals/ of degree 8.
type QOmega = Omega Rationals

-- ----------------------------------------------------------------------
-- * Conversion to dyadic

-- | A type class relating \"rational\" types to their dyadic
-- counterparts.
class ToDyadic a b | a -> b where
  -- | Convert a \"rational\" value to a \"dyadic\" value, if the
  -- denominator is a power of 2. Otherwise, return 'Nothing'.
  maybe_dyadic :: a -> Maybe b

-- | Convert a \"rational\" value to a \"dyadic\" value, if the
-- denominator is a power of 2. Otherwise, throw an error.
to_dyadic :: (ToDyadic a b) => a -> b
to_dyadic a = case maybe_dyadic a of
  Just b -> b
  Nothing -> error "to_dyadic: denominator not a power of 2"

instance ToDyadic Dyadic Dyadic where
  maybe_dyadic = return

instance ToDyadic Rational Dyadic where
  maybe_dyadic x = do
    k <- log2 denom
    return (Dyadic numer k)
    where denom = denominator x
          numer = numerator x

instance ToDyadic Rationals Dyadic where
  maybe_dyadic = maybe_dyadic . unRationals

instance (ToDyadic a b) => ToDyadic (RootTwo a) (RootTwo b) where
  maybe_dyadic (RootTwo x y) = do
    x' <- maybe_dyadic x
    y' <- maybe_dyadic y
    return (RootTwo x' y')

instance (ToDyadic a b) => ToDyadic (Cplx a) (Cplx b) where
  maybe_dyadic (Cplx x y) = do
    x' <- maybe_dyadic x
    y' <- maybe_dyadic y
    return (Cplx x' y')

instance (ToDyadic a b) => ToDyadic (Omega a) (Omega b) where
  maybe_dyadic (Omega x y z w) = do
    x' <- maybe_dyadic x
    y' <- maybe_dyadic y
    z' <- maybe_dyadic z
    w' <- maybe_dyadic w
    return (Omega x' y' z' w')

-- ----------------------------------------------------------------------
-- * Real part
    
-- | A type class for rings that have a \"real\" component. A typical
-- instance is /a/ = 'DComplex' with /b/ = 'DReal'.
class RealPart a b | a -> b where
  -- | Take the real part.
  real :: a -> b

instance RealPart (Cplx a) a where
  real (Cplx a b) = a

instance (HalfRing a) => RealPart (Omega a) (RootTwo a) where
  real (Omega a b c d) = RootTwo d (half * (c - a))

-- ----------------------------------------------------------------------
-- * Rings of integers
  
-- | A type class for rings that have a distinguished subring \"of
-- integers\". A typical instance is /a/ = 'DReal', which has /b/ =
-- 'DInteger' as its ring of integers.
class WholePart a b | a -> b where  
  -- | The embedding of the ring of integers into the larger ring.
  from_whole :: b -> a
  -- | The inverse of 'from_whole'. Throws an error if the given
  -- element is not actually an integer in the ring.
  to_whole :: a -> b
  
instance WholePart Dyadic Integer where
  from_whole = fromInteger
  to_whole d 
    | n == 0 = a
    | otherwise = error "to_whole: non-integral value"
    where
      (a,n) = decompose_dyadic d

instance WholePart DReal DInteger where
  from_whole = fromDInteger
  to_whole (RootTwo x y) = RootTwo (to_whole x) (to_whole y)
  
instance WholePart DOmega ZOmega where
  from_whole = fromZOmega
  to_whole (Omega x y z w) = Omega (to_whole x) (to_whole y) (to_whole z) (to_whole w)
  
instance (WholePart a a', WholePart b b') => WholePart (a,b) (a',b') where
  from_whole (x,y) = (from_whole x, from_whole y)
  to_whole (x,y) = (to_whole x, to_whole y)
  
instance WholePart () () where  
  from_whole = const ()
  to_whole = const ()
  
instance (WholePart a b) => WholePart [a] [b] where  
  from_whole = map from_whole
  to_whole = map to_whole
  
instance (WholePart a b) => WholePart (Cplx a) (Cplx b) where  
  from_whole (Cplx a b) = Cplx (from_whole a) (from_whole b)
  to_whole (Cplx a b) = Cplx (to_whole a) (to_whole b)
  
-- ----------------------------------------------------------------------
-- * Common denominators
  
-- | A type class for things from which a common power of 1\/√2 (a
-- least denominator exponent) can be factored out. Typical instances
-- are 'DReal', 'DComplex', as well as tuples, lists, vectors, and
-- matrices thereof.
class DenomExp a where
  -- | Calculate the least denominator exponent /k/ of /a/. Returns
  -- the smallest /k/≥0 such that /a/ = /b/\/√2[sup /k/] for some
  -- integral /b/.
  denomexp :: a -> Integer
  
  -- | Factor out a /k/th power of 1\/√2 from /a/. In other words,
  -- calculate /a/√2[sup /k/].
  denomexp_factor :: a -> Integer -> a

-- | Calculate and factor out the least denominator exponent /k/ of
-- /a/. Return (/b/,/k/), where /a/ = /b/\/(√2)[sup /k/] and /k/≥0.
denomexp_decompose :: (WholePart a b, DenomExp a) => a -> (b, Integer)
denomexp_decompose a = (b, k) where
  k = denomexp a
  b = to_whole (denomexp_factor a k)

-- | Generic 'show'-like method that factors out a common denominator
-- exponent.
showsPrec_DenomExp :: (WholePart a b, Show b, DenomExp a) => Int -> a -> ShowS
showsPrec_DenomExp d a 
  | k == 0 = showsPrec d b
  | k == 1 = showParen (d > 7) $ 
             showString "1/√2 " . showsPrec 7 b
  | otherwise = showParen (d > 7) $
                showString ("1/√2^" ++ show k ++ " ") . showsPrec 7 b
  where (b, k) = denomexp_decompose a

instance DenomExp DReal where
  denomexp (RootTwo x y) = k'
    where
      (a,k) = decompose_dyadic x
      (b,l) = decompose_dyadic y
      k' = maximum [2*k, 2*l-1]
  denomexp_factor a k = a * roottwo^k

instance DenomExp DOmega where
  denomexp (Omega x y z w) = k'
      where
        (a,ak) = decompose_dyadic x
        (b,bk) = decompose_dyadic y
        (c,ck) = decompose_dyadic z
        (d,dk) = decompose_dyadic w
        k = maximum [ak, bk, ck, dk]
        a' = if k == ak then a else 0
        b' = if k == bk then b else 0
        c' = if k == ck then c else 0
        d' = if k == dk then d else 0
        k' | k>0 && even (a'-c') && even (b'-d') = 2*k-1
           | otherwise = 2*k
  denomexp_factor a k = a * roottwo^k
        
instance (DenomExp a, DenomExp b) => DenomExp (a,b) where
  denomexp (a,b) = denomexp a `max` denomexp b
  denomexp_factor (a,b) k = (denomexp_factor a k, denomexp_factor b k)

instance DenomExp () where
  denomexp _ = 0
  denomexp_factor _ k = ()

instance (DenomExp a) => DenomExp [a] where
  denomexp as = maximum (0 : [ denomexp a | a <- as ])
  denomexp_factor as k = [ denomexp_factor a k | a <- as ]

instance (DenomExp a) => DenomExp (Cplx a) where
  denomexp (Cplx a b) = denomexp a `max` denomexp b
  denomexp_factor (Cplx a b) k = Cplx (denomexp_factor a k) (denomexp_factor b k)

-- ----------------------------------------------------------------------
-- * Conversion to EComplex

-- $ 'EComplex' is the largest one of our \"exact\" arithmetic
-- types. We define a 'toEComplex' family of functions for converting
-- just about anything to an 'EComplex'.

-- | A type class for things that can be exactly converted to
-- 'EComplex'.
class ToEComplex a where
  -- | Conversion to 'EComplex'.
  toEComplex :: a -> EComplex

instance ToEComplex Integer where
  toEComplex = fromInteger

instance ToEComplex Rational where
  toEComplex a = Cplx (RootTwo (ToRationals a) 0) 0

instance (ToEComplex a) => ToEComplex (RootTwo a) where
  toEComplex (RootTwo a b) = toEComplex a + roottwo * toEComplex b
  
instance ToEComplex Dyadic where
  toEComplex (Dyadic a n)
    | n >= 0    = toEComplex a * half^n
    | otherwise = toEComplex a * 2^(-n)

instance (ToEComplex a) => ToEComplex (Cplx a) where
  toEComplex (Cplx a b) = toEComplex a + i * toEComplex b

instance (ToEComplex a) => ToEComplex (Omega a) where
  toEComplex (Omega a b c d) = omega^3 * a' + omega^2 * b' + omega * c' + d'
    where
      a' = toEComplex a
      b' = toEComplex b
      c' = toEComplex c
      d' = toEComplex d

-- ----------------------------------------------------------------------
-- * Parity
    
-- | A type class for things that have parity.
class Parity a where
  -- | Return the parity of something.
  parity :: a -> Z2

instance Integral a => Parity a where
  parity x = if even x then 0 else 1
  
instance Parity DInteger where
  parity (RootTwo a b) = parity a

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | If /n/≠0, return (/a/,/k/) such that /a/ is odd and /n/ =
-- /a/⋅2[sup /k/]. If /n/=0, return (/0/,/0/).
lobit :: Integer -> (Integer, Integer)
lobit 0 = (0,0)
lobit n = aux n 0 where
  aux n !k
    | n .&. 0xffffffff == 0  = aux (shiftR n 32) (k+32)
    | n .&. 0xff == 0        = aux (shiftR n 8) (k+8)
    | even n                 = aux (shiftR n 1) (k+1)
    | otherwise              = (n,k)
        
-- | If /n/ is of the form 2[sup /k/], return /k/. Otherwise, return
-- 'Nothing'.
log2 :: Integer -> Maybe Integer
log2 n
  | a == 1 = Just k
  | otherwise = Nothing
    where
      (a,k) = lobit n

-- | For /n/ ≥ 0, return the floor of the square root of /n/. This is
-- done using integer arithmetic, so there are no rounding errors.
intsqrt :: (Integral n) => n -> n
intsqrt n 
  | n <= 0 = 0
  | otherwise = iterate 1 
    where
      iterate m
        | m_sq <= n && m_sq + 2*m + 1 > n = m
        | otherwise = iterate ((m + n `div` m) `div` 2)
          where
            m_sq = m*m

