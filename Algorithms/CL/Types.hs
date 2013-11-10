-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE IncoherentInstances #-} 
{-# LANGUAGE DeriveDataTypeable  #-}

-- | This module defines the specialized datatypes of the Class Number algorithm, and basic utility functions on these types.
module Algorithms.CL.Types where

import Quipper
import Quipper.Internal
import Data.Typeable
import Data.Ratio

import QuipperLib.Arith hiding (q_mult_param)
import QuipperLib.FPReal
import Algorithms.CL.Auxiliary

-- ===========================================
-- * Type synonyms

-- $ First, we define some type synonyms for arithmetic types, selecting which will be used in the functions for the Class Number algorithm.
--
-- We use three different integer types.  For interfacing with quantum computation, we use 'CLInt' := 'IntM'.  For efficient classical (i.e. circuit-generation time) computation on potentially large integers, we use 'CLIntP' := 'Integer', Haskell’s arbitrary-precision integers.  (Δ, for instance, is taken to be a 'CLIntP').  For small classical integers (typically for register sizes), we use 'Int', Haskell’s bounded-precision integers.
--
-- For the first two of these, we define type synonyms, so that they can be swapped out to other types if desired (they are to a large extent modular).  For 'Int' we do not, since we make un-coerced use of built-in Haskell functions like 'length' which give it specifically.
--
-- Where not dictated by these conventions, integer types are generalized, i.e., @(Integral a) =>@ …
--
-- Rational and real numbers have not yet been similarly stratified.

-- | Integers that may be passed into or received out of quantum computations.
type CLInt      = IntM

-- | Integers that will be used for parameter computation only, potentially large.
type CLIntP     = Integer

-- | Rational numbers for the Class Number code.
type CLRational = Rational

-- | Real numbers for the Class Number code.
type CLReal     = FPReal

-- ===========================================
-- * Algebraic number fields

-- ===========================================
-- ** Discriminants

-- $ The functions of this subsection are needed only for circuit-generation-time classical computation, not for quantum circuit computation.

-- | Compute Δ, given /d/.
-- (See [Jozsa 2003], Prop. 6 et seq.  We use Δ, or in code 'bigD', where Jozsa uses /D/.)
bigD_of_d :: Integral a => a -> a
bigD_of_d d = case (d `mod` 4) of
  1 -> d
  _ -> 4*d

-- | Compute /d/, given Δ.
-- (Again, see [Jozsa 2003], Prop. 6 et seq.)
d_of_bigD :: Integral a => a -> a
d_of_bigD bigD = case (bigD `mod` 4) of
  0 -> bigD `div` 4
  _ -> bigD

-- | Check if /d/ is a valid input to Hallgren’s algorithm,
-- i.e. correctly defines a real quadratic number field.
is_valid_d :: (Integral a) => a -> Bool
is_valid_d d = d > 1 && is_square_free d

-- | Check if /Δ/ is a valid input to Hallgren’s algorithm,
-- i.e. is the discriminant of a real quadratic number field.
-- (Cf. <http://en.wikipedia.org/wiki/Fundamental_discriminant>)
is_valid_bigD :: (Integral a) => a -> Bool
is_valid_bigD bigD = bigD > 1 && case (bigD `mod` 4) of
  1 -> is_square_free bigD
  0 -> (d `mod` 4 == 2 || d `mod` 4 == 3) && is_square_free d
    where d = bigD `div` 4
  _ -> False

-- | The (infinite, lazy) list of all valid inputs /d/, 
-- i.e. of all square-free integers above 2.
all_small_ds :: (Integral int) => [int]
all_small_ds = filter (\n -> is_valid_d n)  [2..]

-- | The (infinite, lazy) list of all valid inputs Δ, 
-- i.e. of all discriminants of real quadratic number fields.
all_bigDs :: (Integral int) => [int]
all_bigDs = map bigD_of_d all_small_ds

-- ===========================================
-- ** Field elements

-- | A data type describing a number in the algebraic number field K = ℚ[√Δ]: @'AlgNum' /a/ /b/ Δ@ represents /a/ + /b/√Δ.
--
-- In general, the type of coefficients may be any type of (classical or quantum)
-- numbers, i.e. an instance of the 'Num' or 'QNum' class.
-- Given this, the algebraic numbers with a fixed Δ will in turn be an instance
-- of 'Num' or 'QNum'.
-- 
-- A value @/a/ :: /x/@ may also be used as an @'AlgNumGen' /x/@,
-- with no Δ specified, to represent simply /a/ + 0√Δ; this can be considered polymorphic
-- over all possible values of Δ. 
-- 
-- This is similar to the use of 'IntM's or 'FPReal's of indeterminate size, although
-- unlike for them, we do not restrict this to the classical case.  However, the
-- question of whether an 'AlgNumQ' has specified √Δ is (like e.g. the length of
-- a list) is a parameter property, known at circuit generation time, not a purely 
-- quantum property.
data AlgNumGen a = AlgNum a a CLIntP | AlgNum_indet a deriving (Show)

-- | The specific instance of 'AlgNumGen' used for classical (parameter) computation.
type AlgNum = AlgNumGen CLRational

-- | Extract the first co-ordinate of an 'AlgNumGen'
fst_AlgNum :: AlgNumGen a -> a
fst_AlgNum (AlgNum u _ _) = u
fst_AlgNum (AlgNum_indet u) = u

-- | Extract the second co-ordinate of an 'AlgNumGen'
snd_AlgNum :: (Num a) => AlgNumGen a -> a
snd_AlgNum (AlgNum _ v _) = v
snd_AlgNum (AlgNum_indet _) = 0

instance (Eq a, Num a) => Eq (AlgNumGen a) where
  (AlgNum a b bigD) == (AlgNum a' b' bigD') = 
    if bigD == bigD' then a == a' && b == b'
    else error "Operation = on AlgNum: operands must have same Δ."
  (AlgNum a b bigD) == (AlgNum_indet a') = (AlgNum a b bigD) == (AlgNum a' 0 bigD)
  (AlgNum_indet a) == (AlgNum a' b' bigD') = (AlgNum a 0 bigD') == (AlgNum a' b' bigD')
  (AlgNum_indet a) == (AlgNum_indet a') = a == a'

-- | Print a 'Number' in human-readable (though not Haskell-readable) format, as e.g. 
pretty_show_AlgNum :: Show a => AlgNumGen a -> String
pretty_show_AlgNum (AlgNum a b bigD) = (show a) ++ " + " ++ (show b) ++ " √" ++ show bigD
pretty_show_AlgNum (AlgNum_indet a) = show a

-- | Realize an algebraic number as a real number (of any 'Floating' type).
floating_of_AlgNum :: (Real a, Floating b) => AlgNumGen a -> b
floating_of_AlgNum (AlgNum a b bigD) = (realToFrac a) + (realToFrac b) * (sqrt $ fromIntegral bigD)
floating_of_AlgNum (AlgNum_indet a) = (realToFrac a)

-- | Coerce one algebraic number into the field of a second, if possible.  If not possible (i.e. if their Δ’s mismatch), throw an error.
number_promote :: Num a => AlgNumGen a -> AlgNumGen b -> ErrMsg -> AlgNumGen a
number_promote (AlgNum a b bigD) (AlgNum _ _ bigD') e =
  if bigD == bigD' then AlgNum a b bigD
  else error $ e "mismatched Δ."
number_promote (AlgNum_indet a) (AlgNum _ _ bigD') _ = AlgNum a 0 bigD'
number_promote n (AlgNum_indet _) _ = n

instance (Ord a, Num a) => Ord (AlgNumGen a) where
  compare (AlgNum a b bigD) (AlgNum a' b' bigD') = 
    if bigD == bigD' then
      case (compare a a', compare b b') of 
        (EQ,y) -> y
        (x,EQ) -> x
        (GT,GT) -> GT
        (LT,LT) -> LT
        (GT,LT) -> compare ((a-a')^2) ((b-b')^2 * fromInteger bigD)
        (LT,GT) -> compare ((b-b')^2 * fromInteger bigD) ((a-a')^2)
    else 
      error "compare // AlgNumGen: mismatched Δ."
  compare (AlgNum a b bigD) (AlgNum_indet a') = compare (AlgNum a b bigD) (AlgNum a' 0 bigD)
  compare (AlgNum_indet a) (AlgNum a' b' bigD') = compare (AlgNum a 0 bigD') (AlgNum a' b' bigD')
  compare (AlgNum_indet a) (AlgNum_indet a') = compare a a'

instance (Ord a, Num a) => Num (AlgNumGen a) where
  (AlgNum a b bigD) + (AlgNum a' b' bigD') = 
    if bigD == bigD' then AlgNum (a+a') (b+b') bigD
    else error "Operation + on AlgNum: operands must have same Δ."
  (AlgNum a b bigD) + (AlgNum_indet a') = (AlgNum a b bigD) + (AlgNum a' 0 bigD)
  (AlgNum_indet a) + (AlgNum a' b' bigD') = (AlgNum a 0 bigD') + (AlgNum a' b' bigD')
  (AlgNum_indet a) + (AlgNum_indet a') = (AlgNum_indet (a + a'))

  (AlgNum a b bigD) * (AlgNum a' b' bigD') = 
    if bigD == bigD' then AlgNum (a*a' + b*b'*(fromIntegral bigD)) (a*b' + a'*b) bigD
    else error "Operation * on AlgNum: operands must have same Δ."
  (AlgNum a b bigD) * (AlgNum_indet a') = (AlgNum a b bigD) * (AlgNum a' 0 bigD)
  (AlgNum_indet a) * (AlgNum a' b' bigD') = (AlgNum a 0 bigD') * (AlgNum a' b' bigD')
  (AlgNum_indet a) * (AlgNum_indet a') = (AlgNum_indet (a * a'))

  (AlgNum a b bigD) - (AlgNum a' b' bigD') = 
    if bigD == bigD' then AlgNum (a-a') (b-b') bigD
    else error "Operation - on AlgNum: operands must have same Δ."
  (AlgNum a b bigD) - (AlgNum_indet a') = (AlgNum a b bigD) - (AlgNum a' 0 bigD)
  (AlgNum_indet a) - (AlgNum a' b' bigD') = (AlgNum a 0 bigD') - (AlgNum a' b' bigD')
  (AlgNum_indet a) - (AlgNum_indet a') = (AlgNum_indet (a - a'))

  abs n = if (n >= 0) then n else -n 
  signum n = number_promote (if n > 0 then 1 else if n == 0 then 0 else (-1)) n 
               (const "CL.Types: internal error (signum // AlgNum)")
  fromInteger = AlgNum_indet . fromInteger

instance (Real a) => Real (AlgNumGen a) where
  toRational = toRational . floating_of_AlgNum

instance (Ord a, Fractional a) => Fractional (AlgNumGen a) where
  fromRational = AlgNum_indet . fromRational

  recip (AlgNum a b bigD) = 
    let c = (a^2) - (b^2 * (fromIntegral bigD))
    in assert (c /= 0) (if (a == 0 && b == 0) then "CL.Types: divide-by-zero error"
                        else if is_valid_bigD bigD then "CL.Types: internal error (AlgNum // recip)"
                        else error "CL.Types: " ++ show bigD ++ " not a valid discriminant")
       (AlgNum (a/c) (-b/c) bigD)
  recip (AlgNum_indet a) = AlgNum_indet $ recip a

instance (RealFrac a) => RealFrac (AlgNumGen a) where
  properFraction x = (x',x - fromIntegral x')
    where x' = truncate $ floating_of_AlgNum x

-- | The algebraic conjugate: sends /a/ + /b/ √Δ to /a/ - /b/ √Δ.
conjugate :: (Num a) => AlgNumGen a -> AlgNumGen a
conjugate (AlgNum a b bigD) = (AlgNum a (-b) bigD)
conjugate (AlgNum_indet a) = (AlgNum_indet a)

-- | Test whether an algebraic number is an algebraic integer.
--
-- (A number is an algebraic integer iff it can be written in the form /m/ + /n/(Δ + √Δ)\/2, where /m/, /n/ are integers.
-- See [Jozsa 2003], proof of Prop. 14.)
is_alg_int :: (Ord a, RealFrac a) => AlgNumGen a -> Bool
is_alg_int (AlgNum a b bigD) = is_int n && is_int m
  where
-- solve for m, n in the equation [a + b √D = m + n(Δ + √Δ)/2]
    n = 2 * b
    m = a - b * fromIntegral bigD
is_alg_int (AlgNum_indet a) = is_int a

-- | Test whether an algebraic number is a unit of the ring of algebraic integers.
is_unit :: (Ord a, RealFrac a) => AlgNumGen a -> Bool
is_unit n = if n == 0 then False else (is_alg_int n) && (is_alg_int (recip n))

-- | The number ω associated to the field /K/.
omega_of_bigD :: CLIntP -> AlgNum
omega_of_bigD bigD =
  if (bigD `mod` 4 == 1)
  then (AlgNum (1/2) (1/2) bigD)
  else (AlgNum 0 1 bigD)

-- ===========================================
-- * Ideals

-- | Data specifying an ideal in an algebraic number field.  An ideal is described by a tuple
-- (Δ,/m/,/l/,/a/,/b/), representing the ideal
-- 
-- /m/\//l/ (/aZ/ + (/b/+√Δ)\/2 /Z/),
-- 
-- where moreover we assume and ensure always that the ideal is in /standard form/ ([Jozsa 2003], p.11, Prop. 16).  Specifically,
-- 
-- * /a/,/k/,/l/ > 0;
--
-- * 4/a/ | /b/[sup 2] – Δ; 
--
-- * /b/ = τ(/a/,/b/);
--
-- * gcd(/k/,/l/) = 1
-- 
-- In particular, this gives us bounds on the size of /a/ and /b/, 
-- and hence tells us the sizes needed for these registers (see 'length_for_ab' below).
data IdealX x = Ideal CLIntP (XInt x) (XInt x) (XInt x) (XInt x) 
  deriving (Show, Eq, Typeable) 

-- | Classical parameter specifying an ideal.
type Ideal = IdealX Bool

-- | Quantum circuit-type counterpart of 'Ideal'.
type IdealQ = IdealX Qubit

-- | Classical circuit-type counterpart of 'Ideal'.
type IdealC = IdealX Bit

type instance QCType x y (IdealX z) = IdealX (QCType x y z)
type instance QTypeB Ideal = IdealQ

instance Show Ideal where
  show (Ideal bigD m l a b) = 
    "Ideal "
    ++ show bigD ++ " "
    ++ show m ++ " "
    ++ show l ++ " "
    ++ show a ++ " "
    ++ show b

instance QCLeaf x => QCData (IdealX x) where
    
  qcdata_mapM ~(Ideal _ msh lsh ash bsh) f g (Ideal bigD m l a b) = do
    m' <- qcdata_mapM msh f g m
    l' <- qcdata_mapM lsh f g l
    a' <- qcdata_mapM ash f g a
    b' <- qcdata_mapM bsh f g b
    return (Ideal bigD m' l' a' b')
  
  qcdata_zip ~(Ideal _ msh lsh ash bsh) q c q' c' (Ideal bigD m l a b) (Ideal bigD' m' l' a' b') e
    | bigD /= bigD'
      = error (e "Ideal exponent mismatch")
    | otherwise 
      = (Ideal bigD m'' l'' a'' b'')
      where
        m'' = qcdata_zip msh q c q' c' m m' errmsg
        l'' = qcdata_zip lsh q c q' c' l l' errmsg
        a'' = qcdata_zip ash q c q' c' a a' errmsg
        b'' = qcdata_zip bsh q c q' c' b b' errmsg
        errmsg x = e ("in Ideal: " ++ x)

  qcdata_promote (Ideal bigD m l a b) (Ideal bigD' m' l' a' b') e
    | bigD /= bigD'
      = error (e "Ideal exponent mismatch")
    | otherwise 
      = (Ideal bigD m'' l'' a'' b'')
    where
      m'' = qcdata_promote m m' errmsg
      l'' = qcdata_promote l l' errmsg
      a'' = qcdata_promote a a' errmsg
      b'' = qcdata_promote b b' errmsg
      errmsg x = e ("in Ideal: " ++ x)

-- Labeling of IdealQ is (m,l,a,b).
instance QCLeaf x => Labelable (IdealX x) String where
  label_rec (Ideal _ qm ql qa qb) s = do
    label_rec qm s `dotted_indexed` "m"
    label_rec ql s `dotted_indexed` "l"
    label_rec qa s `dotted_indexed` "a"
    label_rec qb s `dotted_indexed` "b"

-- We also provide an alternate labeling by a 4-tuple of strings, in
-- case this is ever useful (maybe for an ideal where the components
-- are called something other than /m/, /l/, /a/, and /b/).
instance Labelable IdealQ (String, String, String, String) where
  label_rec (Ideal _ qm ql qa qb) (sm, sl, sa, sb) = do
    label_rec qm sm
    label_rec ql sl
    label_rec qa sa
    label_rec qb sb

instance Eq Ideal where
  i1@(Ideal bigD m l a b) == i2@(Ideal bigD' m' l' a' b')
    = if (bigD /= bigD') 
      then error error_string
      else (m == m' && l' == l' && a == a' && b == b')
    where error_string = "Comparing two ideals of different Δ: " ++ (show i1) ++ "," ++ (show i2)

-- | Data specifying a reduced ideal, by a tuple (Δ,/a/,/b/); this 
-- corresponds to the ideal specified by (Δ,1,/a/,/a/,/b/), i.e.,
-- /Z/ + (/b/+√Δ)\/2/a/ /Z/.
data IdealRedX x = IdealRed CLIntP (XInt x) (XInt x) 
  deriving (Show, Typeable)

-- | Classical parameter specifying a reduced ideal.
type IdealRed = IdealRedX Bool

-- | Quantum circuit-type counterpart of 'IdealRed'.
type IdealRedQ = IdealRedX Qubit

-- | Classical circuit-type counterpart of 'IdealRed'.
type IdealRedC = IdealRedX Bit

instance Show IdealRed where
  show (IdealRed bigD a b) = 
    "IdealRed "
    ++ show bigD ++ " "
    ++ show a ++ " "
    ++ show b

instance Eq IdealRed where
  i1@(IdealRed bigD a b) == i2@(IdealRed bigD' a' b')
    = if (bigD /= bigD') 
      then error error_string
      else (a == a' && b == b')
    where error_string = "Comparing two reduced ideals of different Δ: "
                         ++ (show i1) ++ "," ++ (show i2)

type instance QCType x y (IdealRedX z) = IdealRedX (QCType x y z)
type instance QTypeB IdealRed = IdealRedQ

instance QCLeaf x => QCData (IdealRedX x) where

  qcdata_mapM ~(IdealRed _ ash bsh) f g (IdealRed bigD a b) = do
    a' <- qcdata_mapM ash f g a
    b' <- qcdata_mapM bsh f g b
    return (IdealRed bigD a' b')
  
  qcdata_zip ~(IdealRed _ ash bsh) q c q' c' (IdealRed bigD a b) (IdealRed bigD' a' b') e
    | bigD /= bigD'
      = error (e "IdealRed exponent mismatch")
    | otherwise 
      = (IdealRed bigD a'' b'')
      where
        a'' = qcdata_zip ash q c q' c' a a' errmsg
        b'' = qcdata_zip bsh q c q' c' b b' errmsg
        errmsg x = e ("in IdealRed: " ++ x)

  qcdata_promote (IdealRed bigD a b) (IdealRed bigD' a' b') e 
    | bigD /= bigD'
      = error (e "IdealRed exponent mismatch")
    | otherwise
      = (IdealRed bigD a'' b'')
      where
        a'' = qcdata_promote a a' errmsg
        b'' = qcdata_promote b b' errmsg
        errmsg x = e ("in IdealRed: " ++ x)

-- Labeling of IdealRedQ is (a,b).
instance QCLeaf x => Labelable (IdealRedX x) String where
  label_rec (IdealRed _ qa qb) s = do
    label_rec qa s `dotted_indexed` "a"
    label_rec qb s `dotted_indexed` "b"

-- We also provide an alternate labeling by a pair of strings, in case
-- this is ever useful (maybe for an ideal where the two components
-- are called something other than /a/ and /b/).
instance QCLeaf x => Labelable (IdealRedX x) (String, String) where
  label_rec (IdealRed _ qa qb) (sa, sb) = do
    label_rec qa sa
    label_rec qb sb

-- | An ideal /I/, together with a distance δ for it — that is, /some/ representative, mod /R/, for δ(/I/) as defined on /G/ p.4.  
-- Most functions described as acting on ideals need in fact to be seen as a pair of an ideal and a distance for it. 
type IdDist = (Ideal,FPReal) 

-- | Quantum analogue of 'IdDist'. 
type IdDistQ = (IdealQ,FPRealQ) 

-- | A reduced ideal /I/, together with a distance δ for it.
type IdRedDist = (IdealRed,FPReal)

-- | Quantum analogue of 'IdRedDist'. 
type IdRedDistQ = (IdealRedQ,FPRealQ)

-- ===========================================
-- ** Trivial access functions

-- | Extract the /d/ component from an 'IdealQ'.
d_of_Ideal :: IdealX a -> CLIntP 
d_of_Ideal (Ideal bigD _ _ _ _) = d_of_bigD bigD
 
-- | Extract the /d/ component from an 'IdealRedQ'.
d_of_IdealRed :: IdealRedX a -> CLIntP 
d_of_IdealRed (IdealRed bigD _ _) = d_of_bigD bigD 

-- | Extract Δ from an 'IdealQ'.
bigD_of_Ideal :: IdealX a -> CLIntP 
bigD_of_Ideal (Ideal bigD _ _ _ _) = bigD 

-- | Extract Δ from an 'IdealRedQ'.
bigD_of_IdealRed :: IdealRedX a -> CLIntP 
bigD_of_IdealRed (IdealRed bigD _ _) = bigD 

-- | Extract the delta part from an ideal/distance pair.
delta :: IdDist -> CLReal
delta (Ideal _ _ _ _ _, del) = del

-- ===========================================
-- ** Assertions, coercions

-- $ Elements of the types 'Ideal', 'IdealRed', etc are assumed to satisfy certain extra conditions.  
-- This section includes functions for checking that these conditions are satisfied, and for safely 
-- coercing between these types. 

-- | @'tau' Δ /b/ /a/@: the function τ(/b/,/a/).  Gives the representative for /b/ mod /2a/, in a range dependent on /a/ and √Δ.  
--
-- (This doesn't quite belong here, but is included as a prerequisite of the assertions).
tau :: (Integral int, Integral int') => int' -> int -> int -> int
tau bigD b a = mod_with_max b (2*a) max
  where 
    max = if a > root_bigD then a else root_bigD
    root_bigD = floor $ sqrt $ fromIntegral bigD

-- | Return 'True' if the given ideal is in standard form.  (Functions should /always/ keep ideals in standard form).
is_standard :: Ideal -> Bool
is_standard (Ideal bigD m l a b) =
  (a > 0) && (l > 0) && (m > 0)
  && ((bigD - (fromIntegral b)^2) `mod` (4 * (fromIntegral a)) == 0)
  && b == tau bigD b a

-- | Test whether an 'Ideal' is reduced.  (An ideal \</m/,/l/,/a/,/b/> is reduced iff /m/ = 1, /l/ = /a/, /b/ ≥ 0 and /b/ + √Δ > 2/a/ ([Jozsa 2003], Prop. 20)). 
is_reduced :: Ideal -> Bool
is_reduced (Ideal bigD m l a b) = (m == 1) && (l == a) && (b >= 0) && (b + root_bigD > 2 * a)
  where root_bigD = ceiling $ sqrt $ fromIntegral bigD 

-- | Test whether an 'IdealRed' is really reduced.  (An ideal \<1,/a/,/a/,/b/> is reduced iff /b/ ≥ 0 and /b/ + √Δ > 2/a/ ([Jozsa 2003], Prop. 20)). 
is_really_reduced :: IdealRed -> Bool
is_really_reduced (IdealRed bigD a b) = (b >= 0) && (b + root_bigD > 2 * a)
  where root_bigD = ceiling $ sqrt $ fromIntegral bigD 

-- | Coerce an 'IdealRed' to an 'Ideal'.
forget_reduced :: IdealRed -> Ideal
forget_reduced (IdealRed bigD a b) = (Ideal bigD 1 a a b)

-- | Coerce an 'Ideal' to an 'IdealRed', if it is reduced, or throw an error otherwise.  Cf. [Jozsa 2003], Prop. 20.
to_reduced :: Ideal -> IdealRed
to_reduced ii@(Ideal bigD m l a b) =
  if is_reduced ii then (IdealRed bigD a b)
                   else error $ "to_reduced: (" ++ (show ii) ++ ") is not reduced."

-- | Throw an error if an 'Ideal' is not reduced; otherwise, the identity function.
assert_reduced :: Ideal -> a -> a
assert_reduced ii =
  assert (is_reduced ii) ("assert_reduced: (" ++ (show ii) ++ ") is not reduced.")

-- | Throw an error if an 'IdealRed' is not really reduced; otherwise, the identity function.
assert_really_reduced :: IdealRed -> a -> a
assert_really_reduced ii =
  assert (is_really_reduced ii) ("assert_really_reduced: (" ++ (show ii) ++ ") is not reduced.")

-- | Quantum analogue of 'tau'.  @'q_tau' Δ /qb/ /qa/@: compute the representative for /qb/ mod 2/qa/, in a range dependent on /qa/ and √Δ.
q_tau :: CLIntP -> QDInt -> QDInt -> Circ (QDInt, QDInt, QDInt)
q_tau bigD = box ("tau, Δ = " ++ show bigD) $ \a b -> do
  let root_bigD = floor $ sqrt $ fromIntegral bigD
  t <- with_computed
    (do 
      (_, a_gt_rtD) <- q_gt_param a root_bigD
      max <- qinit $ qc_false a
      (max, _) <- controlled_not max a `controlled` a_gt_rtD
      max <- bool_controlled_not max (intm_promote root_bigD max "q_tau: internal error") `controlled` (a_gt_rtD .==. False)
      (_, twice_a) <- q_mult_param 2 a
      (_, _, _, t) <- q_mod_with_max b twice_a max
      return t)
    qc_copy
  return (a,b,t)

-- | Test whether a given 'IdealQ' is reduced.  \</m/,/l/,/a/,/b/> is reduced iff /m/ = 1, /l/ = /a/, /b/ ≥ 0 and /b/ + √Δ > 2/a/ ([Jozsa 2003], Prop. 20).  
q_is_reduced :: IdealQ -> Circ (IdealQ,Qubit) 
q_is_reduced = box "is_reduced" $ \qii ->
  let bigD = bigD_of_Ideal qii in
  with_computed_fun qii
    (\(Ideal bigD qm ql qa qb) -> do
      test1 <- qinit False
      test1 <- qnot test1 `controlled` qm .==. 1
      (ql,qa,test2) <- q_is_equal ql qa
      (qb,test3) <- q_ge_param qb 0
      (qa, q2a) <- q_mult_param 2 qa
      qx <- q_sub_param_in_place (ceiling $ sqrt $ fromIntegral bigD) q2a
      (qb, qx, test4) <- q_gt qb qx
      return ([test1,test2,test3,test4], (qm,ql,qa,qb,qx)))
    (\(tests, rest) -> do
      test_out <- qinit False
      test_out <- qnot test_out `controlled` tests
      return ((tests, rest), test_out))

-- | Test whether a given 'IdealQ' is really reduced (as it should always be, if code is written correctly).  An ideal \<1,/a/,/a/,/b/> is reduced iff /b/ ≥ 0 and /b/ + √Δ > 2/a/ ([Jozsa 2003], Prop. 20). 
q_is_really_reduced :: IdealRedQ -> Circ (IdealRedQ,Qubit) 
q_is_really_reduced = box "is_really_reduced" $ \qii ->
  let bigD = bigD_of_IdealRed qii in
  with_computed_fun qii
    (\(IdealRed bigD qa qb) -> do
      (qb,test1) <- q_ge_param qb 0
      (qa, q2a) <- q_mult_param 2 qa
      qx <- q_sub_param_in_place (ceiling $ sqrt $ fromIntegral bigD) q2a
      (qb, qx, test2) <- q_gt qb qx
      return ([test1,test2], (qa,qb,qx)))
    (\(tests, rest) -> do
      test_out <- qinit False
      test_out <- qnot test_out `controlled` tests
      return ((tests, rest), test_out))
 
-- | Coerce an 'IdealRedQ' to an 'IdealQ', initializing the extra components appropriately.
q_forget_reduced :: IdealRedQ -> Circ IdealQ
q_forget_reduced = box "forget_reduced" $ \(IdealRed bigD a b) -> do
   let a_bits = qulist_of_qdint_bh a
       n = length a_bits 
   m <- qinit (intm n 1)
   (a,l) <- qc_copy_fun a
   return (Ideal bigD m l a b)

-- | Coerce an 'IdealQ' to an 'IdealRedQ', assertively terminating the extra components 
-- (and hence throwing an error at quantum runtime if the input is not reduced).
q_assert_reduced :: IdealQ -> Circ IdealRedQ
q_assert_reduced = box "assert_reduced" $ \x@(Ideal bigD m l a b) -> do
  x_red <- reverse_generic q_forget_reduced (IdealRed bigD a b) x
  q_assert_really_reduced x_red

-- | Throw a (quantum-runtime) error if an 'IdealRedQ' is not really reduced; otherwise, do nothing.
--
-- Compare 'assert_reduced', 'q_is_really_reduced' in "Algorithms.CL.RegulatorQuantum", and [Jozsa 2003] Prop. 20.
q_assert_really_reduced :: IdealRedQ -> Circ IdealRedQ
q_assert_really_reduced = box "assert_really_reduced" $ \ii -> do 
  (ii,test) <- q_is_really_reduced ii
  qterm True test
  return ii

-- ======================================================================
-- ** Bounds on coefficient sizes

-- $ Given Δ, how much space should be allocated for the coefficients of ideals?  Most of these bounds are currently missing or uncertain, as documented below.  Note these bounds are intended to be sufficient for the calculations occurring in this algorithm, /not/ for representing arbitrary ideals.

-- | Given Δ, return the size of integers to be used for the coefficients /a/, /b/ of reduced ideals.
--
-- Note: can we bound this more carefully?  In reduced ideals, we always have 0 ≤ /a/,/b/ ≤ √Δ (see notes on 'is_standard', 'is_reduced'), and the outputs of ρ, ρ[sup –1] and dot-products of reduced ideals always keep |/a/| ≤ Δ.  However, intermediate calculations may involve larger values, so we allocate a little more space.  For now, this padding is a seat-of-the-pants estimate.  
length_for_ab :: CLIntP -> Int
length_for_ab bigD = 3 + (ceiling $ logBase 2 $ fromIntegral bigD)

-- | Given Δ, return the size of integers to be used for the coefficients /m/, /l/ of general ideals.
--
-- TODO: bound this!  Neither Hallgren nor [Jozsa 2003] discusses bounds on the values of /m/ and /l/ that will appear, and we do not yet have a bound.  For now we use the same length as for /a/ and /b/, for convenience; this should be considered a dummy bound, quite possibly not sufficient in general.
length_for_ml :: CLIntP -> Int
length_for_ml = length_for_ab

-- | Given Δ, return the precision /n/ = log[sub 2]/N/ to be used for
-- discretizing the quasi-periodic function /f/ to /f/[sub /N/].
--
-- (“Precision” here means the number of binary digits after the point).
-- 
-- Taken to ensure 1\//N/ < 3/(32 Δ log Δ).  (Cf. [Jozsa 2003], Prop. 36 (iii).)
n_of_bigD :: (Integral int) => CLIntP -> int
n_of_bigD bigD =
  ceiling $ logBase 2 $ 32 * (fromIntegral bigD) * (log $ fromIntegral bigD) / 3

-- | Given Δ, /n/, /l/ (as for 'fN', 'q_fN'), return the precision required
-- for intermediate distance calculations during the computation of /f/[sub /N/].
--
-- TODO: bound this more carefully.  [Jozsa 2003] asks for the final output to be precision /n/, but does not discuss intermediate precision, and we have not yet got a confident answer.  For now, just a back-of-the-envelope estimate, which should be sufficient and /O/(correct), but is almost certainly rather larger than necessary.
precision_for_fN :: CLIntP -> Int -> Int -> Int
precision_for_fN _ n l = 2 * (n + l)

-- | Set the 'IntM' coefficients of an 'Ideal' to the standard lengths, if they are not already fixed incompatibly.  The standard lengths are determined by 'length_for_ml', 'length_for_ab'.   (Compare 'intm_promote', etc.)
fix_sizes_Ideal :: Ideal -> Ideal
fix_sizes_Ideal (Ideal bigD m l a b) = (Ideal bigD (f m) (f l) (f a) (f b))
  where
    f x = intm_promote x (intm n 0) "set_sizes_Ideal: lengths already fixed incompatibly"
    n = max (length_for_ml bigD) (length_for_ab bigD)

-- | Set the 'IntM' coefficients of an 'IdealRed' to the standard lengths, if they are not already fixed incompatibly.  The standard lengths are determined by 'length_for_ml', 'length_for_ab'.   (Compare 'intm_promote', etc.)
fix_sizes_IdealRed :: IdealRed -> IdealRed
fix_sizes_IdealRed (IdealRed bigD a b) = (IdealRed bigD (f a) (f b))
  where
    f x = intm_promote x (intm n 0) "set_sizes_Ideal: lengths already fixed incompatibly"
    n = max (length_for_ml bigD) (length_for_ab bigD)
