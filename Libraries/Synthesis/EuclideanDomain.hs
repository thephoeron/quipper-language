-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleInstances #-}

-- | This module provides a type class for Euclidean domains. A
-- Euclidean domain is a ring with a notion of division with
-- remainder, and therefore greatest common divisors.

module Libraries.Synthesis.EuclideanDomain where

import Libraries.Synthesis.Ring
import Data.Maybe

-- ----------------------------------------------------------------------
-- * Euclidean domains

-- ----------------------------------------------------------------------
-- ** Definition

-- | A type class for Euclidean domains. A Euclidean domain is a ring
-- with a Euclidean function and a division with remainder.
class (Eq a, Ring a) => EuclideanDomain a where
  -- | The Euclidean function for the Euclidean domain. This is a
  -- function /rank/ : /R/\\{0} → ℕ such that:
  -- 
  -- * for all nonzero /a/, /b/ ∈ /R/, /rank/(/a/) ≤ /rank/(/ab/);
  -- 
  -- * if /b/ ≠ 0 and (/q/,/r/) = /a/ `divmod` /b/, then either /r/ =
  -- 0 or /rank/(/r/) < /rank/(/b/).
  rank :: a -> Integer
  -- | Given /a/ and /b/≠0, return a quotient and remainder for
  -- division of /a/ by /b/. Specifically, return (/q/,/r/) such that
  -- /a/ = /qb/ + /r/, and such that /r/ = 0 or /rank/(/r/) < /rank/(/b/).
  divmod :: a -> a -> (a,a)

-- ----------------------------------------------------------------------
-- Particular Euclidean domains

instance EuclideanDomain Integer where
  rank x = x
  divmod x y = divMod x y

instance EuclideanDomain ZComplex where
  rank x = abs (norm x)
  divmod x y = (q, r) where
    (Cplx l m) = x * adj y
    k = norm y
    q1 = l `rounddiv` k
    q2 = m `rounddiv` k
    q = Cplx q1 q2
    r = x - y * q

instance EuclideanDomain DInteger where
  rank x = abs (norm x)
  divmod x y@(RootTwo c d) = (q, r) where
    (RootTwo l m) = x * adj2 y
    k = norm y
    q1 = l `rounddiv` k
    q2 = m `rounddiv` k
    q = RootTwo q1 q2
    r = x - y * q
  
instance EuclideanDomain ZOmega where
  rank x = abs (norm x)
  divmod x y = (q, r) where
    (Omega a' b' c' d') = x * adj y * adj2(y * adj y)
    k = norm y
    a = a' `rounddiv` k
    b = b' `rounddiv` k
    c = c' `rounddiv` k
    d = d' `rounddiv` k
    q = Omega a b c d
    r = x - y * q    

-- ----------------------------------------------------------------------
-- ** Functions

-- | Calculate the remainder for the division of /x/ by /y/.
euclid_mod :: (EuclideanDomain a) => a -> a -> a
euclid_mod x y = r where
  (q,r) = x `divmod` y

infixl 7 `euclid_mod`

-- | Calculate the quotient for the division of /x/ by /y/, ignoring
-- the remainder, if any. This is typically, but not always, used in
-- situations where the remainder is known to be 0 ahead of time.
euclid_div :: (EuclideanDomain a) => a -> a -> a
euclid_div x y = q where
  (q,r) = x `divmod` y

infixl 7 `euclid_div`

-- | Calculate the greatest common divisor in any Euclidean domain.
euclid_gcd :: (EuclideanDomain a) => a -> a -> a
euclid_gcd x y
  | y == 0 = x
  | otherwise = euclid_gcd y r where
    (_,r) = divmod x y

-- | Perform the extended Euclidean algorithm. On inputs /x/ and
-- /y/, this returns (/a/,/b/,/s/,/t/,/d/) such that:
-- 
-- * /d/ = gcd(/x/,/y/),
-- 
-- * /ax/ + /by/ = /d/,
-- 
-- * /sx/ + /ty/ = 0,
-- 
-- * /at/ - /bs/ = 1.
extended_euclid :: (EuclideanDomain a) => a -> a -> (a, a, a, a, a)
extended_euclid x y
  | y == 0 = (1, 0, 0, 1, x)
  | otherwise = (b',a'-b'*q,-t',t'*q-s',d) where
    (a',b',s',t',d) = extended_euclid y r
    (q,r) = divmod x y

-- | Find the inverse of a unit in a Euclidean domain. If the given
-- element is not a unit, return 'Nothing'.
euclid_inverse :: (EuclideanDomain a) => a -> Maybe a
euclid_inverse x
  | x == 0    = Nothing
  | r == 0    = Just q
  | otherwise = Nothing
  where
    (q,r) = divmod 1 x

-- | Determine whether an element of a Euclidean domain is a unit.
is_unit :: (EuclideanDomain a) => a -> Bool
is_unit = isJust . euclid_inverse

-- | Compute the inverse of /a/ in /R/\/(p), where /R/ is a Euclidean
-- domain. Note: this works whenever /a/ and /p/ are relatively
-- prime. If /a/ and /p/ are not relatively prime, return 'Nothing'.
inv_mod :: EuclideanDomain a => a -> a -> Maybe a
inv_mod p a = case euclid_inverse d of
  Just d' -> let (q,r) = (b*d') `divmod` p in Just r
  Nothing -> Nothing
  where
    (b,_,_,_,d) = extended_euclid a p

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | For /y/ ≠ 0, find the integer /q/ closest to /x/ \/ /y/. This
-- works regardless of whether /x/ and\/or /y/ are positive or
-- negative.  The distance /q/ − /x/ \/ /y/ is guaranteed to be in
-- (-1\/2, 1\/2].
rounddiv :: (Integral a) => a -> a -> a
rounddiv x y = 
  -- Note: the use of "quot" and "div" is crucial for the signs to
  -- work out correctly.
  (x + y `quot` 2) `div` y

infixl 7 `rounddiv`
