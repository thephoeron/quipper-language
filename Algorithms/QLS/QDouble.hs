-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable  #-}

-- | This modules implements a library for fixed-points real numbers.
module Algorithms.QLS.QDouble where

import qualified Data.Ratio as Ratio

import Data.Typeable

import Quipper
import Quipper.Internal

import QuipperLib.Arith
import QuipperLib.Simulation

import Algorithms.QLS.Utils
import Algorithms.QLS.QSignedInt

import Libraries.Auxiliary (getId, mmap)

-- * Signed fixed point type

-- | Data type for fixed point arithmetic. 
-- 
-- 'XDouble' /k/ /n/ represents the number /n/⋅2[sup -/k/], where /n/
-- is a signed integer and /k/ is an integer parameter.
-- 
-- We refer to /k/ as the /exponent/ of the fixed point number.  When
-- we speak of the /length/, we mean the total number of digits
-- (excluding the sign), i.e., the length, in binary digits, of the
-- underlying /n/.
data XDouble x = XDouble Int (SignedInt x)
  deriving (Show, Typeable)

-- | The parameter type of fixed-point numbers.
type FDouble = XDouble Bool

-- | The quantum type of fixed-point numbers.
type QDouble = XDouble Qubit

-- | The classical type of fixed-point numbers.
type CDouble = XDouble Bit

-- ----------------------------------------------------------------------
-- * Auxiliary definitions

-- | Compute the power of an integer by a non-negative integer.
integer_power :: Int -> Int -> Integer
integer_power x y = (fromIntegral x) ^ y

-- | Compute the power of an integer by another, possibly negative one. 
double_power :: Int -> Int -> Double
double_power x y
  | y >= 0 = (fromIntegral x) ^ y
  | otherwise = 1 / ((fromIntegral x) ^ (-y))

-- | Divide one integer by another, and round the result to the closest
-- integer. If the result is half way between two integers, round to
-- the even one (this is the same behavior as Haskell's 'round'
-- function). This function has unlimited precision.
div_round :: Integer -> Integer -> Integer
div_round x y = round (x Ratio.% y)
    
-- ----------------------------------------------------------------------
-- * Operation for length and exponent

-- ----------------------------------------------------------------------
-- ** Generic functions for XDouble

-- | Return the exponent /k/ of an 'XDouble'.
xdouble_exponent :: XDouble x -> Int
xdouble_exponent (XDouble k _) = k

-- | Return the length /m/ of an 'XDouble'.
xdouble_length :: XDouble x -> Int
xdouble_length (XDouble _ n) = sint_length n

-- | Return the \"extent\" of an 'XDouble'. The extent of a fixed-point
-- number /x/ is, by definition, the pair (/hi/,/lo/) of integers such
-- that the most significant bit of /x/ has positional index /hi/-1
-- (in other words, the value of this bit is 2[sup /hi/-1]), and the
-- least significant bit of /x/ has positional index /lo/ (in other
-- words, the value of this bit is 2[sup /lo/]. Typically, but not
-- necessarily, /hi/ ≥ 0 and /lo/ ≤ 0. In this case, one can also
-- think of /hi/ as \"the number of digits before the radix point\"
-- and −/lo/ as \"the number of digits after the radix point\". 
-- 
-- The exponent /k/, length /m/, and extent (/hi/,/lo/) are related by
-- /k/=-/lo/ and /m/=/hi/−/lo/.
-- 
-- Examples: 
-- 
-- * a number represented in the form /xxxx.yyy/ has extent (4,-3),
-- exponent 3, and length 7.
-- 
-- * a number represented in the form /xxxx000./ has extent (7,3),
-- exponent -3, and length 4.
-- 
-- * a number represented in the form /.000xxxx/ has extent (-3,-7),
-- exponent 7, and length 4.
-- 
-- If we regard extents as intervals, ordered by inclusion, then it is
-- always possible to losslessly cast a fixed-point number from a
-- smaller to a larger extent.
xdouble_extent :: XDouble x -> (Int, Int)
xdouble_extent x = (m-k, -k) where
  m = xdouble_length x
  k = xdouble_exponent x

-- | Add /n/ zeros to the high bits of the 'XDouble'. This sends
-- /xxx.yyy/ to 000/xxx.yyy/. This increases the length without changing
-- the exponent or value.
xdouble_pad_left :: (Monad m) => m x -> Int -> XDouble x -> m (XDouble x)
xdouble_pad_left zero n (XDouble k (SInt digits s)) = do
              pad <- sequence $ replicate n zero
              let digits' = pad ++ digits
              return $ XDouble k (SInt (digits') s)

-- | Add /n/ zeros to the low bits of the 'XDouble'. This sends
-- /xxx.yyy/ to /xxx.yyy000/. This increases the length and the
-- exponent without changing the value.
xdouble_pad_right :: (Monad m) => m x -> Int -> XDouble x -> m (XDouble x)
xdouble_pad_right zero n (XDouble k (SInt digits s)) = do
              pad <- sequence $ replicate n zero
              let digits' = digits ++ pad
              return $ XDouble (k+n) (SInt (digits') s)

-- | Pad an 'XDouble' on both sides to reach the desired extent.  This
-- increases the length and exponent without changing the value (it is
-- a lossless operation). It is an error to call this function if the
-- selected extent does not contain the extent of the input 'XDouble'.
xdouble_pad_to_extent :: (Monad m) => m x -> (Int, Int) -> XDouble x -> m (XDouble x)
xdouble_pad_to_extent zero (hi, lo) x
  | lo <= lo_x && hi_x <= hi
    =  xdouble_pad_left zero (hi - hi_x) =<< xdouble_pad_right zero (lo_x - lo) x
  | otherwise
    = error "qdouble_pad_to_extent: bad extent"
    where
      (hi_x, lo_x) = xdouble_extent x

-- | Remove the /n/ low bits of an 'XDouble'. This sends /xxx.yyyzzz/
-- to /xxx.yyy/. It is an error to call this function when the
-- 'XDouble' has fewer than /n/ digits.
xdouble_truncate_right :: Int -> QDouble -> QDouble
xdouble_truncate_right n (XDouble k (SInt digits s)) = (XDouble k' (SInt digits' s))
  where 
    k' = k - n
    digits' | length digits >= n = reverse $ drop n $ reverse digits
            | otherwise          = error "xdouble_truncate_right"

-- | Convert a 'SignedInt' to an 'XDouble' with exponent 0.
xdouble_of_sint :: SignedInt x -> XDouble x
xdouble_of_sint n = XDouble 0 n

-- ----------------------------------------------------------------------
-- ** Special cases for QDouble

-- | Add /n/ zeros to the high bits of the 'QDouble'. This sends
-- /xxx.yyy/ to 000/xxx.yyy/. This increases the length without
-- changing the exponent or value. This function does not return a
-- fresh copy; it reuses part of its input.
qdouble_pad_left :: Int -> QDouble -> Circ QDouble
qdouble_pad_left = xdouble_pad_left (qinit False)

-- | Add /n/ zeros to the low bits of the 'QDouble'. This sends
-- /xxx.yyy/ to /xxx.yyy000/. This increases the length and the
-- exponent without changing the value. This function does not return
-- a fresh copy; it reuses part of its input.
qdouble_pad_right :: Int -> QDouble -> Circ QDouble
qdouble_pad_right = xdouble_pad_right (qinit False)

-- | Pad a 'QDouble' on both sides to reach the desired extent.  This
-- increases the length and exponent without changing the value (it is
-- a lossless operation). It is an error to call this function if the
-- selected extent does not contain the extent of the input
-- 'QDouble'. This function does not return a fresh copy; it reuses
-- part of its input.
qdouble_pad_to_extent :: (Int, Int) -> QDouble -> Circ QDouble
qdouble_pad_to_extent = xdouble_pad_to_extent (qinit False)

-- | Remove the /n/ low bits of a 'QDouble'. This sends /xxx.yyyzzz/
-- to /xxx.yyy/. Note that the /n/ low qubits are not terminated and
-- become garbage. It is an error to call this function when the
-- 'QDouble' has fewer than /n/ digits. 
qdouble_truncate_right :: Int -> QDouble -> QDouble
qdouble_truncate_right = xdouble_truncate_right
  
-- ----------------------------------------------------------------------
-- ** Special cases for FDouble

-- | Add /n/ zeros to the low bits of the 'FDouble'. This sends
-- /xxx.yyy/ to /xxx.yyy000/. This increases the length and the
-- exponent without changing the value.
fdouble_pad_right :: Int -> FDouble -> FDouble
fdouble_pad_right k x = getId $ xdouble_pad_right (return False) k x

-- | Pad a 'FDouble' on both sides to reach the desired extent.  This
-- increases the length and exponent without changing the value (it is
-- a lossless operation). It is an error to call this function if the
-- selected extent does not contain the extent of the input 'FDouble'.
fdouble_pad_to_extent :: (Int, Int) -> FDouble -> FDouble
fdouble_pad_to_extent extent x = getId $ xdouble_pad_to_extent (return False) extent x
  
-- ----------------------------------------------------------------------
-- * Operations for FDouble

-- ----------------------------------------------------------------------
-- ** Casts

-- | @'fdouble_of_double' /k/ /m/ /x/@: Convert /x/ to an 'FDouble' of
-- exponent /k/ and length /m/ ≥ 0. Note that the exponent does not
-- need to be between 0 and /m/; it can even be negative.
fdouble_of_double :: Int -> Int -> Double -> FDouble
fdouble_of_double k m x 
  | abs n >= integer_power 2 m 
    = error "fdouble_of_double: number too large" 
  | otherwise
    = XDouble k (fsint_of_integer m n)
  where
    d = double_power 2 k
    n = round (d * x)

-- | Convert an 'FDouble' to a 'Double'.
double_of_fdouble :: FDouble -> Double
double_of_fdouble (XDouble k n) = (fromIntegral x) / (double_power 2 k)
  where
    x = integer_of_fsint n

-- | Convert an 'FSignedInt' to an 'FDouble' with exponent 0.
fdouble_of_fsint :: FSignedInt -> FDouble
fdouble_of_fsint = xdouble_of_sint

-- | Make an 'FDouble' value of exponent /k/, length /m/, and value /a/2[sup /-k/].
fdouble_of_integer :: Int -> Int -> Integer -> FDouble
fdouble_of_integer k m a = XDouble k (fsint_of_integer m a)

-- | Construct a 'Double' from an 'FDouble', using some arbitrary
-- method to guess the length and exponent.
fdouble :: Double -> FDouble
fdouble x = fromRational $ toRational x

-- | Convert an 'FDouble' to a string in human-readable form. 
show_fdouble :: FDouble -> String
show_fdouble x@(XDouble k (SInt digits s)) = sign ++ binary ++ " (" ++ (show float) ++ ")"
  where
    float = double_of_fdouble x
    sign = if s then "-" else "+"
    m = length digits
    binary_full = [ if h then '1' else '0' | h <- digits ]
    binary | k < 0     = binary_full ++ "e" ++ show (-k)
           | k > m     = "." ++ binary_full ++ "e" ++ show (m-k)
           | otherwise = binary1 ++ "." ++ binary2
    (binary1,binary2) = splitAt ((fromIntegral m) - k) binary_full

-- ----------------------------------------------------------------------
-- ** Type class instances
    
-- $ We make 'FDouble' an instance of 'Eq', 'Ord', 'Real', 'Num',
-- 'Fractional', and 'RealFrac'. See the source code for details.

-- Note: none of the arithmetic operations pass via the native
-- 'Double' type, and therefore they are not subject to arbitrary
-- precision limits. However, most operations set the precision of the
-- result to the maximum precision of the inputs.
    
    
-- | Express a pair of 'FDouble' values as a pair of 'FSignedInt's with a
-- common exponent.
fdouble_align :: FDouble -> FDouble -> (Int, FSignedInt, FSignedInt)
fdouble_align (XDouble h m) (XDouble k n)
  | h <= k     = (k, fsint_shift (k-h) m, n)
  | otherwise  = (h, m, fsint_shift (h-k) n)

instance Eq FDouble where
  x == y  =  m == n  where  (k,m,n) = fdouble_align x y

instance Ord FDouble where
  compare x y  =  compare m n  where  (k,m,n) = fdouble_align x y

instance Real FDouble where
  toRational (XDouble h n) 
    | h >= 0    = (Ratio.%) nx (integer_power 2 h)
    | otherwise = fromInteger (nx * integer_power 2 (-h))
    where
      nx = integer_of_fsint n

instance Num FDouble where
  -- Additive operations set the exponent to the maximum of the two
  -- exponents, and extend the length if necessary. Signum keeps the
  -- length but resets the exponent to 0.
  x + y  =  XDouble k (m + n)    where  (k,m,n) = fdouble_align x y
  x - y  =  XDouble k (m - n)    where  (k,m,n) = fdouble_align x y
  abs x  =  XDouble k (abs m)    where  XDouble k m = x
  signum x = fdouble_of_fsint (signum m)  where  XDouble k m = x
  
  -- fromInteger uses the fixed exponent 'after_radix_length'.
  fromInteger = fdouble_pad_right after_radix_length . fdouble_of_fsint . fromInteger
  
  -- Multiplication sets the extent to the maximum of the two extents. 
  x * y  | k >= 0    = fdouble_of_integer k len (a*b `div_round` integer_power 2 k)
         | otherwise = fdouble_of_integer k len (a*b * integer_power 2 (-k))
    where
      (k,m,n) = fdouble_align x y
      a = integer_of_fsint m
      b = integer_of_fsint n
      len = max (sint_length m) (sint_length n)

instance Fractional FDouble where
  -- Division sets the extent to the maximum of the two extents.
  x / y  | k >= 0    = fdouble_of_integer k len ((a * integer_power 2 k) `div_round` b)
         | otherwise = fdouble_of_integer k len (a `div_round` (b * integer_power 2 (-k)))
    where
      (k,m,n) = fdouble_align x y
      a = integer_of_fsint m
      b = integer_of_fsint n
      len = max (sint_length m) (sint_length n)

  fromRational x = fdouble_of_double before_radix_length (before_radix_length+after_radix_length) ((fromInteger $ Ratio.numerator x) / (fromInteger $ Ratio.denominator x))

instance RealFrac FDouble where
  properFraction x 
    | k <= 0    = (0, x)
    | otherwise = (fromInteger q, fdouble_of_integer k len r)
    where 
      XDouble k m = x
      a = integer_of_fsint m
      len = sint_length m
      (q, r) = a `quotRem` integer_power 2 k

-- ----------------------------------------------------------------------
-- Operations for QDouble

-- ----------------------------------------------------------------------
-- QCData instance

type instance QCType x y (XDouble z) = XDouble (QCType x y z)
type instance QTypeB FDouble = QDouble

instance QCLeaf x => QCData (XDouble x) where
  qcdata_mapM ~(XDouble _ shape) f g (XDouble n xs) =
    mmap (XDouble n) $ qcdata_mapM shape f g xs
  qcdata_zip ~(XDouble _ shape) q c q' c' (XDouble n xs) (XDouble m ys) e
    | n == m
      = XDouble n $ qcdata_zip shape q c q' c' xs ys (const $ e "XDouble length mismatch")
    | otherwise 
      = error (e "XDouble exponent mismatch")
  qcdata_promote (XDouble n b) (XDouble m q) e 
    | n == m 
      = XDouble n $ qcdata_promote b q (const $ e "XDouble length mismatch")
    | otherwise 
      = error (e "XDouble exponent mismatch")

-- Labeling of QDouble is s.sign, s[hi-1], ..., s[lo], where lo = -k.
instance QCLeaf x => Labelable (XDouble x) String where
  label_rec (XDouble k (SInt digits sign)) s = do
    label_rec sign s `dotted_indexed` "sign"
    sequence_ [ label_rec d s `indexed` show i | (d,i) <- zip rdigits [-k,-k+1..] ]
    where
      rdigits = reverse digits
  
instance CircLiftingUnpack (Circ QDouble) (Circ QDouble) where
  pack x = x
  unpack x = x

-- ----------------------------------------------------------------------
-- * Casts
  
-- | Convert a 'QSignedInt' to a 'QDouble' with exponent 0. This
-- function does not return a fresh copy; instead, it uses the input
-- qubits.
qdouble_of_qsint :: QSignedInt -> Circ QDouble
qdouble_of_qsint x = do
  (_,y) <- qc_copy_fun x
  return $ xdouble_of_sint y  

-- ----------------------------------------------------------------------
-- ** Type class instances

-- $ We make 'QDouble' an instance of 'QOrd'.

instance QOrd QDouble where
  q_less x y | kx < ky   = do
                           x <- qdouble_pad_right (ky-kx) x
                           compare_right x y
           | kx > ky   = do
                           y <- qdouble_pad_right (kx-ky) y
                           compare_right x y
           | otherwise = compare_right x y
    where
      kx = xdouble_exponent x
      ky = xdouble_exponent y

      -- compare_right assumes matching exponent, i.e., both bit strings
      -- are right-aligned.
      compare_right :: QDouble -> QDouble -> Circ Qubit
      compare_right (XDouble _ n) (XDouble _ m) = q_less n m

-- | Express a pair of 'QDouble' values as a pair of 'QSignedInt's with a
-- common exponent.
qdouble_align :: QDouble -> QDouble -> Circ (Int, QSignedInt, QSignedInt)
qdouble_align (XDouble h m) (XDouble k n)
  | h <= k     = do
                  m <- qsint_shift (k-h) m
                  return (k, m, n)
  | otherwise  = do
                  n <- qsint_shift (h-k) n
                  return (k, m, n)


instance QNum QDouble where
  -- Additive operations set the exponent to the maximum of the two
  -- exponents, and extend the length if necessary. Signum keeps the
  -- length but resets the exponent to 0.
  q_add x y = do 
    (k,m,n) <- qdouble_align x y
    (_, _, r) <- q_add m n
    return (x, y, XDouble k r)
  q_sub x y = do 
    (k,m,n) <- qdouble_align x y
    (_, _, r) <- q_sub m n
    return (x, y, XDouble k r)
  q_abs x = do   
    let XDouble k m = x
    (_, r) <- q_abs m
    return (x, XDouble k r)
  q_negate x = do
    let XDouble k m = x
    (_, r) <- q_negate m
    return (x, XDouble k r)
  q_signum x = do
    let XDouble k m = x
    (_, r) <- q_signum m
    y <- qdouble_of_qsint r
    return (x, y)
  q_fromQDInt x = do
    (_,y) <- q_fromQDInt x
    z <- qdouble_of_qsint y
    w <- qdouble_pad_right after_radix_length z
    return (x,w)
  -- 'q_mult' currently does not work with negative exponents.
  q_mult x y = let m = max (xdouble_exponent x) (xdouble_exponent y) in
               let s = (xdouble_exponent x) + (xdouble_exponent y) in
               do
               ext_x <- qdouble_pad_left m x
               ext_y <- qdouble_pad_left m y
               let XDouble kx nx = ext_x
               let XDouble ky ny = ext_y
               (_,_,nz) <- q_mult nx ny
               let z = XDouble s nz
               return (x,y,qdouble_truncate_right (s-m) z)


-- ----------------------------------------------------------------------
-- * Other functions



-- Developer note: the following instances are to be able to use
-- named_gate_safe, which is probably not at all safe. Also, it
-- requires us to define an Eq instance for every type where this is
-- used. The instances are defined as follows, and are considered a
-- temporary hack.

-- Textual equality for 'QDouble'.
instance Eq QDouble where
  XDouble a b == XDouble a' b' =  (a,b) == (a',b')

-- Textual equality for 'QSignedInt'.
instance Eq QSignedInt where
  (SInt b c) == (SInt b' c')  =  (b,c) == (b',c')


-- | Coercion from 'QSignedInt' to 'QDouble'.
q_fromIntegral :: QSignedInt -> Circ QDouble
q_fromIntegral x = do
        x' <- qsint_shift after_radix_length x
        return $ XDouble after_radix_length x'

-- | QDouble of 'ceiling': coercion from 'QDouble' to 'QSignedInt'.

-- Note: This rounds to 0 and not to infinity.
q_ceiling :: QDouble -> Circ QSignedInt
q_ceiling (XDouble k (SInt x b)) = return $ SInt (reverse . drop k . reverse $ x) b


-- | Real division with 'QDouble'.
q_div_real :: QDouble -> QDouble -> Circ QDouble
q_div_real (XDouble kx (SInt x bx)) (XDouble ky (SInt y by)) = 
           if (kx /= ky) then error "q_div_real"
           else 
           let k = kx in do
                pad_x <- qinit (replicate k False)
                pad_y <- qinit (replicate k False)
                let ext_x = x ++ pad_x
                let ext_y = pad_y ++ y
                (_,_,ext_z) <- q_quot (qdint_of_qulist_bh ext_x)
                                      (qdint_of_qulist_bh ext_y)
                let z = reverse $ drop k $ reverse $ qulist_of_qdint_bh ext_z
                bz <- qinit False
                qnot_at bz `controlled` bx
                qnot_at bz `controlled` by
                return (XDouble k (SInt z bz))




my_test = let x = fromRational $ toRational (12345.34) in
          let y = fromRational $ toRational (323.1) in
          let last (x,y,z) = z in
          do
          putStrLn $ show_fdouble x
          putStrLn $ show_fdouble y
          putStrLn $ show_fdouble $ snd $ run_classical_generic q_negate x






instance Num (FDouble,FDouble) where
  x + y = undefined 
  x * y = undefined 
  x - y = undefined 
  fromInteger x = undefined 
  abs x = undefined 
  signum x = undefined 


instance QNum (QDouble,QDouble) where
  q_add (x1,x2) (y1,y2) = do 
      (_,_,z1) <- q_add x1 y1
      (_,_,z2) <- q_add x2 y2
      return ((x1,x2),(y1,y2),(z1,z2))

  q_mult (x1,x2) (y1,y2) = do 
      (_,_,a) <- q_mult x1 y1
      (_,_,b) <- q_mult x2 y2
      (_,_,z1) <- q_sub a b
      (_,_,c) <- q_mult x1 y2
      (_,_,d) <- q_mult x2 y1
      (_,_,z2) <- q_add c d
      return ((x1,x2),(y1,y2),(z1,z2))

  q_sub (x1,x2) (y1,y2) = do 
      (_,_,z1) <- q_sub x1 y1
      (_,_,z2) <- q_sub x2 y2
      return ((x1,x2),(y1,y2),(z1,z2))
  
  q_abs x = do z <- qinit $ qc_false x; named_gate "abs" (x,z)
  q_negate x = do z <- qinit $ qc_false x; named_gate "neg" (x,z)
  q_signum x = do z <- qinit $ qc_false x; named_gate "sigNum" (x,z)
  q_fromQDInt x = undefined
