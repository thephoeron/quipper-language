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

-- | This library provides a quantum implementation of fixed-precision real numbers (i.e., with precision determined at circuit-generation time), and classical counterpart types.
--
-- Currently still significantly experimental.  TODO: 
--
-- * decide on how much access to provide to underlying representation of 'FPReal'.  Full 'fpreal_case', or more like just what’s available through Haskell’s 'RealFloat'?
--
-- * decide how to use 'ErrMsg': in internal functions only, or exported ones too?
--
-- * many specific TODO’s in code throughout this file.
--
-- * write export list.
 
module QuipperLib.FPReal where

import Quipper
import Quipper.Internal

import QuipperLib.Arith

import Libraries.Auxiliary

import Control.Monad (foldM)
import Data.Maybe (fromJust)
import Data.Ratio (numerator, denominator)
import Data.Typeable

-- ===========================================
-- * Fixed-precision real arithmetic: the FPReal family

-- | 'FPRealX': a family of datatypes for fixed-precision real numbers.
-- (That is, the precision is a parameter, fixed at circuit-generation time.)
-- 
-- 'FPRealX' is based on the family 'XInt' of fixed-length integer types:
-- @'FPRealX' /n/ /a/@ represents 2[sup /n/] /a/, where /a/ is some fixed-length integer.
--
-- Alternately, in the specific case /x/ = 'Bool', a Haskell 'Double' may be 
-- used as an 'FPReal', considered as having indeterminate length and exponent.
-- This is exactly analogous to the case of indeterminate length in 'XInt' / 'IntM'; for a more
-- detailed explanation, see the documentation there.
data FPRealX x = FPRealX Int (XInt x) | FPReal_indet Double (Identity IntM (XInt x))
  deriving (Show, Typeable)

-- | Fixed-precision real parameters.  As with 'IntM', the length and/or exponent
-- of an 'FPReal' may be indeterminate; such an 'FPReal' may only be used in 
-- certain contexts, typically either when the length/exponent can be inferred from context 
-- (e.g., terminating a 'FPRealQ'), or where the result can again be indeterminate.
--
-- As with indeterminate 'IntM's, indeterminate 'FPReal's may be used for efficient, 
-- high-precision classical calculation, and then explicitly or implicitly coerced
-- to determinate 'FPReal's when required for interfacing with quantum computation.
type FPReal     = FPRealX Bool

instance Show FPReal where
  show (FPRealX n x) = "fprealx " ++ show n ++ " (" ++ show x ++ ")"
  show (FPReal_indet r id) = show r

-- | Fixed-precision reals for quantum circuits.
type FPRealQ    = FPRealX Qubit

instance Show FPRealQ where
  show (FPRealX n x) = "fprealx " ++ show n ++ " (" ++ show x ++ ")"
  show (FPReal_indet _ _) = error "FPRealX: internal error"

-- | Fixed-precision reals for classical circuits.
type FPRealC    = FPRealX Bit

{- -- for when Qubit /= Bit:
instance Show FPRealC where
  show (FPRealX n x) = "fprealx " ++ show n ++ " (" ++ show x ++ ")"
  show (FPReal_indet _ _) = error "FPRealX: internal error"
-}

-- ----------------------------------------------------------------------
-- ** Primitive combinators on FPReal

-- $ Like 'XInt', the type 'FPReal' is intended to be an abstract data type,
-- and all access to it should pass through the functions of this
-- section.

-- *** Constructors

-- | Create an 'FPRealX' from an 'XInt' together with an exponent.
fprealx :: Int -> XInt x -> FPRealX x
fprealx n x = FPRealX n x

-- | Create an indeterminate 'FPReal' from a 'Double'. 
fpreal_of_double :: Double -> FPReal
fpreal_of_double r = FPReal_indet r reflexivity

-- *** Destructor

-- | If the 'FPRealX' is of determinate exponent, return its exponent and mantissa.
-- 
-- If the 'FPRealX' is indeterminate, return a pair (/r/, /id/), where /r/ is the underlying 'Double', and /id/ is a witness of the fact that /x/ = 'Bool'.
-- 
-- This is a lowest-level access function not intended to be used by
-- user-level code, and is not exported. 
fprealx_case :: FPRealX x -> Either (Int, XInt x) (Double, Identity IntM (XInt x))
fprealx_case (FPRealX n x) = Left (n,x)
fprealx_case (FPReal_indet r id) = Right (r, id)

-- ----------------------------------------------------------------------
-- ** Other low-level operations

-- $ The operations in this section are the only ones intended to use
-- 'fprealx_case' directly.

-- TODO: fprealx_expt, fprealx_num should probably take ErrMsg arguments, at least for internal use --- I guess only the versions specialized to FPRealQ, FPRealC should be written as though unconditional?  Perhaps only these, plus the 'Maybe' version specialized to 'FPReal', should be exported?
 
-- | Extract the exponent of an 'FPRealX', assumed to be determinate.
--
-- When /x/ is not 'Bool', this and 'fprealx_num' should be considered the destructors of 'FPRealX x'. 
fprealx_expt :: FPRealX x -> Int
fprealx_expt x = 
  case fprealx_case x of
    Left (n, _) -> n
    Right _ -> error "fprealx_expt: indeterminate exponent"

-- | Extract the mantissa of an 'FPRealX', assumed to be of determinate exponent.
--
-- When /x/ is not 'Bool', this and 'fprealx_num' should be considered the destructors of 'FPRealX x'. 
fprealx_num :: FPRealX x -> XInt x
fprealx_num x = 
  case fprealx_case x of
    Left (_, xi) -> xi
    Right _ -> error "fprealx_num: indeterminate exponent"

-- | Extract the length (in bits) of an 'FPRealX', assumed to be of determinate exponent and length.
fprealx_length :: FPRealX x -> Int
fprealx_length x = 
  case fprealx_case x of
    Left (_, xi) -> fromJust $ xint_maybe_length xi
    Right _ -> error "fprealx_length: indeterminate exponent"

-- | Set the exponent of an 'FPReal' to /n/. This operation is only
-- legal if the input (a) has indeterminate exponent or (b) has
-- determinate exponent already equal to /m/. In particular, it cannot
-- be used to change the exponent from anything other than from
-- indeterminate to determinate.
-- 
-- If both arguments already have determinate exponents, and they do not
-- coincide, throw an error. The 'String' argument is used as an error
-- message in that case.

-- Implementation note: the “intm_of_integer” may seem unnecessary,
-- but needed so that when /r/ is “undefined”, the result is
-- “intm_of_integer undefined” not just “undefined”. 
fprealx_set_expt :: Int -> FPRealX x -> String -> FPRealX x
fprealx_set_expt n xr errstr = case fprealx_case xr of
  Left (n', xi) -> if n' == n then fprealx n xi else error errstr
  Right (r, id) -> fprealx n (identity id $ intm_of_integer $ round $
                     if n >= 0 then (r / 2^n) else (r * 2^(-n)))

-- | Return the (possibly indeterminate) exponent of an 'FPRealX'.
fprealx_maybe_expt :: FPRealX x -> Maybe (Int)
fprealx_maybe_expt xr = case fprealx_case xr of
  Left (n, _) -> Just n
  Right _ -> Nothing

-- | Given an 'FPReal', return either the exponent and numerator, or else the double it wraps.
--
-- A specialized and implementation-hiding wrapper for 'fprealx_case'.

-- TODO: should this be exported?
fpreal_case :: FPReal -> Either (Int, IntM) (Double)
fpreal_case (FPRealX n x) = Left (n, x)
fpreal_case (FPReal_indet r _) = Right r

-- | Equality test.  If both have indeterminate exponent, check equality of underlying 'Double's. 
-- Otherwise, if exponents are compatible (i.e. both determinate and equal, or one indeterminate), 
-- check equality of numerators.  If exponents are incompatible, throw an error (the test
-- should in this case be considered ill-typed).
fprealx_equals :: (Eq x) => FPRealX x -> FPRealX x -> Bool    
fprealx_equals x y =
  case (fprealx_case x, fprealx_case y) of
    (Left (n,xi), Left (n',yi)) 
      | n == n' -> xi == yi
      | otherwise -> error "Equality test on FPRealx: operands must be of equal exponent"
    (_, Left (m,yi)) -> fprealx_equals (fprealx_set_expt m x "fprealx_equals") y
    (Left (n,xi), _) -> fprealx_equals x (fprealx_set_expt n y "fprealx_equals")
    (Right (r, _), Right (r', _)) -> r == r'

-- ----------------------------------------------------------------------
-- ** Shape parameters

-- | Return a piece of shape data to represent an /l/-qubit quantum
-- real with exponent /n/.  
-- Please note that the data can only be used as shape; it
-- will be undefined at the leaves.
fprealq_shape :: Int -> Int -> FPRealQ
fprealq_shape n l = fprealx n $ qdint_shape l

-- | Return a piece of shape data to represent an /l/-bit 'FPRealC', 
-- with exponent /n/.
-- Please note that the data can only be used as shape; it will be
-- undefined at the leaves.
fprealc_shape :: Int -> Int -> FPRealC
fprealc_shape n l = fprealx n $ cint_shape l

-- ======================================================================
-- ** Circuit type class instances

-- Note: instance declarations do not show up in the documentation

-- | Try to set the exponent/length of an 'FPReal' to that of another 'FPRealX'
-- value (e.g. an 'FPRealQ', an 'FPRealC', or another 'FPReal').
-- This will fail with an error if both numbers already have determinate
-- lengths that don't coincide. In this case, the string argument is
-- used as an error message.
--
-- The possible “shapes” of 'FPReal's may be seen as a partial order, where 
-- /s1/ ≤ /s2/ means that values of shape /s1/ are coercible to values of shape
-- /s2/.  'fpreal_promote' may be seen as taking the binary /sup/ in this poset.
fpreal_promote :: FPReal -> FPRealX x -> ErrMsg -> FPReal
fpreal_promote br xr errmsg = 
  case fprealx_maybe_expt xr of
    Nothing -> br
    Just n -> 
      let br' = fprealx_set_expt n br (errmsg "FPReal: exponent mismatch")
      in fprealx n $ intm_promote (fprealx_num br') (fprealx_num xr) (errmsg "FPReal: length mismatch") 
 
type instance QCType x y (FPRealX z) = FPRealX (QCType x y z)
type instance QTypeB FPReal = FPRealQ

instance QCLeaf x => QCData (FPRealX x) where
  qcdata_mapM shape f g xr
    = mmap (fprealx (fprealx_expt xr)) $ qcdata_mapM (fprealx_num shape) f g (fprealx_num xr)  
  qcdata_zip shape q c q' c' xr yr e
    | fprealx_expt xr == fprealx_expt yr
      = fprealx (fprealx_expt xr) 
        $ qcdata_zip (fprealx_num shape) q c q' c' (fprealx_num xr) (fprealx_num yr) (const $ e "FPRealX: length mismatch")
    | otherwise
      = error (e "FPRealX: exponent mismatch")
  qcdata_promote = fpreal_promote

-- Labeling of FPRealX is s[hi-1], ..., s[lo], where lo is the exponent.
instance QCLeaf x => Labelable (FPRealX x) String where
  label_rec xr s = do
    let n = fprealx_expt xr
        xi = fprealx_num xr
        qx = list_of_xint_lh xi
    sequence_ [ label_rec q s `indexed` show i | (q,i) <- zip qx [n..] ]

-- ======================================================================
-- * Classical arithmetic on FPReal

-- | Convert an 'FPReal' to a 'Double'.
double_of_fpreal :: FPReal -> Double
double_of_fpreal xr = case fpreal_case xr of
  Left (n, xi) -> if n >= 0 then (fromIntegral xi) * (2^n)
                            else (fromIntegral xi) / (2^(abs n))
  Right r -> r

-- | From a list of 'FPReal's, extract a common shape, provided they have compatible shape
-- (i.e. if any have determinate exponent, they must agree; similarly for length),
-- and throw an error otherwise.
-- 
-- Can be seen as producing finitary suprema in the partial order of shapes.
--
-- The 'FPReal' produced should be considered just a shape; its value is a dummy that
-- should never be used (and will throw an error if it is).
fpreal_common_shape :: [FPReal] -> ErrMsg -> FPReal 
fpreal_common_shape xs e = foldl (\x y -> fpreal_promote x y e)
                         (fpreal_of_double (error $ e "fpreal_common_shape: dummy value produced here was later accessed"))
                         xs

-- | Auxiliary function for lifting a binary operator from 'Double'
-- to 'IntM'. The string argument is the name of the operator, for
-- error messages.
fpreal_binop :: (Double -> Double -> Double) -> String -> (FPReal -> FPReal -> FPReal) 
fpreal_binop op opname x y =
  fpreal_promote 
    (fpreal_of_double $ op (double_of_fpreal x) (double_of_fpreal y))
    (fpreal_common_shape [x,y] errmsg)
    (const "FPReal: internal error (fpreal_binop)")
  where errmsg = (\s -> "Binary operation " ++ opname ++ " on FPReal: " ++ s)

-- | Auxiliary function for lifting a unary operator from 'Double' to
-- 'FPReal'.
fpreal_unop :: (Double -> Double) -> FPReal -> FPReal
fpreal_unop op x = fpreal_promote (fpreal_of_double $ op $ double_of_fpreal x) x 
                                  (const "FPReal: internal error (fpreal_unop)")

------
-- Classical typeclass instances
------

instance Eq x => Eq (FPRealX x) where
  (==) = fprealx_equals

instance Num FPReal where
  (+) = fpreal_binop (+) "+"
  (*) = fpreal_binop (*) "*"
  (-) = fpreal_binop (-) "-"
  abs = fpreal_unop abs
  signum = fpreal_unop signum
  -- Note: signum on determinate exponent/length FPReals has slightly 
  -- surprising behavior if /n/ ≤ –/l/: this will give 
  -- 0, since then 1 = –1 = 0 mod 2^{l + n}. In other words, the
  -- output 1.0 or -1.0 is not representable in this fixed-precision format.
  fromInteger = fpreal_of_double . fromInteger

instance Ord FPReal where
  compare x y = compare (double_of_fpreal x) (double_of_fpreal y)
-- TODO: is this the  right thing to do?  Perhaps we should first check they have 
-- compatible shapes, and throw an error otherwise.

instance Enum FPReal where
  succ = fpreal_unop succ
  pred = fpreal_unop pred
  toEnum = fromIntegral
  fromEnum = fromEnum . double_of_fpreal

instance Real FPReal where
  toRational = toRational . double_of_fpreal

instance Fractional FPReal where
  fromRational = fpreal_of_double . fromRational
  recip = fpreal_unop recip

{- TODO: something along these lines would probably still be good to give.  Work on thinking of good interface.  Or maybe not really necessary??

-- | Convert from any 'RealFrac' type (eg 'Rational', 'Float') to 'FPReal', with specified precision and (possibly indeterminate) length.
fpreal_from_realfrac_with_precision :: (RealFrac a) => Int -> Maybe Int -> a -> FPReal
fpreal_from_realfrac_with_precision n l r = case l of 
  Just l -> FPRealX n $ intm l (round $ r * (2^n))
  Nothing -> FPRealX n $ fromIntegral (round $ r * (2^n))
-}

instance Floating FPReal where
  pi = fpreal_of_double pi
  log = fpreal_unop log
  exp = fpreal_unop exp 
  sin = fpreal_unop sin 
  cos = fpreal_unop cos 
  sinh = fpreal_unop sinh 
  cosh = fpreal_unop cosh 
  asin = fpreal_unop asin 
  acos = fpreal_unop acos 
  atan = fpreal_unop atan 
  asinh = fpreal_unop asinh 
  acosh = fpreal_unop acosh 
  atanh = fpreal_unop atanh 
  
instance RealFrac FPReal where
  properFraction x =
    let (x_int, x_frac_double) = properFraction $ double_of_fpreal x in
      (x_int, fpreal_promote (fpreal_of_double x_frac_double) x (const "FPReal: internal error (properFraction)")) 
  ceiling = ceiling . double_of_fpreal

{- TODO: would definitely be good to give.
instance RealFloat FPReal
-}

-- ** Shape/precision control

-- | Extend the length of a determinate length and precision 'FPReal' by /m/ high and /n/ low bits, without changing its value.  
fpreal_pad :: Int -> Int -> FPReal -> FPReal
fpreal_pad m n x = 
  case fprealx_maybe_expt x of
    Nothing -> error e_expt
    Just x_expt ->
      let x_num = fprealx_num x
      in case intm_length x_num of
        Nothing -> error e_length
        Just x_length ->
          fprealx (x_expt - n) (2^n * intm_extend_signed (x_length + m + n) x_num)
  where
    e_expt = "fpreal_pad: input of indeterminate exponent"
    e_length = "fpreal_pad: input of indeterminate length"

-- | Discard the top /m/ and bottom /n/ bits of a determinate length and precision 'FPReal'.
fpreal_unpad :: Int -> Int -> FPReal -> FPReal
fpreal_unpad m n x = 
  let x_bits = boollist_of_intm_bh $ fprealx_num x
      x_expt = fprealx_expt x
      x_bits_new = reverse $ drop n $ reverse $ drop m x_bits
  in fprealx (x_expt + n) (intm_of_boollist_bh x_bits_new)

-- | Fix the length of an 'IntM' (to automatically-generated values), if not already determinate.
--
-- TODO: belongs in 'QuipperLib.Arith'
intm_fix_length_auto :: IntM -> IntM
intm_fix_length_auto x = case intm_length x of
  Just _ -> x
  Nothing -> 
    let l = (1 +) $ ceiling $ logBase 2 $ fromIntegral $ abs x + (if x >= 0 then 1 else 0)
    in intm l (fromIntegral x)

-- | Fix the precision and length of an 'FPReal' (to automatically-generated values), 
-- leaving unchanged any parts of the shape that are already set. 
--
-- TODO: discuss \/ reconsider \/ improve implementation of this. 

-- Implementation note: aim to use as few bits as possible, while retaining accuracy.
--
-- Not clear what should be done in case denominator not a power of 2.  However,
-- Haskell’s 'Double' has radix 2, so ordinarily denominator always should be a power of 2.
--
-- However, this does give pretty high-precision by default!  Is that good?  Seems expensive in qubits.
fpreal_fix_shape_auto :: FPReal -> FPReal
fpreal_fix_shape_auto x = case fpreal_case x of
  Left (e, n) -> fprealx e (intm_fix_length_auto n)
  Right x -> 
    let r = toRational x
        d = denominator r
    in if d == 2^(round $ logBase 2 $ fromIntegral d)
       then fprealx
              (negate $ round $ logBase 2 $ fromIntegral d)
              (intm_fix_length_auto $ fromIntegral $ numerator r)
       else error "fpreal_fix_shape_auto: not yet fully implemented"

-- ======================================================================
-- * Quantum operations: FPRealQ

-- ** Shape/precision control

-- | Extend the length of an 'FPRealQ' by /m/ high bits and /n/ low bits, without changing its value.  
fprealq_pad :: Int -> Int -> FPRealQ -> Circ FPRealQ
fprealq_pad m n x = do
  let x_bits = qulist_of_qdint_bh $ fprealx_num x
      x_expt = fprealx_expt x
  new_high_bits <- qinit $ replicate m False
  new_high_bits <- case x_bits of 
                     [] -> return new_high_bits 
                     (x_high:_) -> mapUnary qnot new_high_bits `controlled` x_high
  new_low_bits <- qinit $ replicate n False
  return $ fprealx (x_expt - n) $ qdint_of_qulist_bh $ new_high_bits ++ x_bits ++ new_low_bits

-- | Cut off the top /m/ and bottom /n/ bits of an 'FPRealQ', retaining them as explicit garbage.
fprealq_unpad :: Int -> Int -> FPRealQ -> Circ (FPRealQ, [Qubit])
fprealq_unpad m n x =
  let x_bits = qulist_of_qdint_bh $ fprealx_num x
      x_expt = fprealx_expt x
      x_bits_new = reverse $ drop n $ reverse $ drop m x_bits
      garbage = (take m x_bits) ++ (take n $ reverse x_bits)
  in return (fprealx (x_expt + n) (qdint_of_qulist_bh x_bits_new), garbage)

-- | Formally shift an 'FPRealQ' up /n/ bits, i.e. add /n/ to its exponent.
fprealq_shift :: Int -> FPRealQ -> FPRealQ
fprealq_shift n x =
  let num = fprealx_num x
      expt = fprealx_expt x
  in fprealx (expt + n) num

-- ** Quantum arithmetic

-- $ Besides the functions appearing here in the documentation, basic operations ('q_add', etc) are also provided as methods of the 'QNum' type class instance; see 'QNum' for documentation of these functions.

------
-- Quantum typeclass instances
------ 

instance QNum FPRealQ where
  q_add x y =
    let ex = fprealx_expt x
        ey = fprealx_expt y
    in if ex == ey then do
      let nx = fprealx_num x
          ny = fprealx_num y
      (nx,ny,ns) <- q_add nx ny
      return ((fprealx ex nx), (fprealx ey ny), (fprealx ex ns))
    else error "q_add // FPReal: exponent mismatch in arguments."
  q_mult x y =                              -- TODO: to implement
    let ex = fprealx_expt x
        ey = fprealx_expt y
    in if ex == ey then do
      let nx = fprealx_num x
          ny = fprealx_num y
      np <- qinit $ qc_false $ nx
      (nx,ny,np) <- named_gate "q_mult // FPReal" (nx,ny,np)
      return ((fprealx ex nx), (fprealx ey ny), (fprealx ex np))
    else error "q_mult // FPReal: length mismatch in arguments."
  q_sub x y =
    let ex = fprealx_expt x
        ey = fprealx_expt y
    in if ex == ey then do
      let nx = fprealx_num x
          ny = fprealx_num y
      (nx,ny,nd) <- q_sub nx ny
      return ((fprealx ex nx), (fprealx ey ny), (fprealx ex nd))
    else error "q_sub // FPReal: length mismatch in arguments."
  q_abs x = 
    let ex = fprealx_expt x
        nx = fprealx_num x
    in do
      (nx,nx') <- q_abs nx
      return ((fprealx ex nx), (fprealx ex nx'))
  q_negate x = 
    let ex = fprealx_expt x
        nx = fprealx_num x
    in do
      (nx,nx') <- q_negate nx
      return ((fprealx ex nx), (fprealx ex nx'))
  q_signum = error "FPReal // q_signum: not yet implemented." -- TODO!
  q_fromQDInt x = do
    (x,x') <- qc_copy_fun x
    return (x,(fprealx 0 x'))

instance QOrd FPRealQ where
  q_less x y = 
    let ex = fprealx_expt x
        ey = fprealx_expt y
        nx = fprealx_num x
        ny = fprealx_num y
    in if ex == ey then do
      x_less_y <- q_less nx ny
      return x_less_y
    else error "q_less // FPReal: length mismatch in arguments."
  q_leq x y = 
    let ex = fprealx_expt x
        ey = fprealx_expt y
        nx = fprealx_num x
        ny = fprealx_num y
    in if ex == ey then do
      x_leq_y <- q_leq nx ny
      return x_leq_y
    else error "q_leq // FPReal: length mismatch in arguments."

-- | Analogue of 'q_add_in_place', for 'FPRealQ'.
fprealq_add_in_place ::  FPRealQ -> FPRealQ -> Circ (FPRealQ,FPRealQ)
fprealq_add_in_place x y =
    let ex = fprealx_expt x
        ey = fprealx_expt y
        nx = fprealx_num x
        ny = fprealx_num y
    in if ex == ey then do
      (x,y) <- q_add_in_place nx ny
      return ((fprealx ex nx), (fprealx ey ny))
    else error "q_add_in_place_fprealq // FPReal: length mismatch in arguments."

-- | Analogue of 'q_sub_in_place', for 'FPRealQ'.
fprealq_sub_in_place ::  FPRealQ -> FPRealQ -> Circ (FPRealQ,FPRealQ)
fprealq_sub_in_place x y =
    let ex = fprealx_expt x
        ey = fprealx_expt y
        nx = fprealx_num x
        ny = fprealx_num y
    in if ex == ey then do
      (x,y) <- q_sub_in_place nx ny
      return ((fprealx ex nx), (fprealx ey ny))
    else error "q_sub_in_place_fprealq // FPReal: length mismatch in arguments."

-- | Subtract a parameter 'FPReal' from an 'FPRealQ', in place.  Assume compatible precision.
-- 
-- Note: highly sub-optimal.  TODO: optimize!
fprealq_sub_param_in_place :: FPReal -> FPRealQ -> Circ FPRealQ
fprealq_sub_param_in_place x qy = 
  with_ancilla_init (fpreal_promote x qy $ const e_prec)  (\qx -> do
    (qx, qy) <- fprealq_sub_in_place qx qy
    return qy)
  where
    e_prec = "fprealq_sub_param_in_place: incompatible precision"

-- | Add a parameter 'FPReal' to an 'FPRealQ', in place.  Assume compatible precision.
-- 
-- Note: highly sub-optimal.  TODO: optimize!
fprealq_add_param_in_place :: FPReal -> FPRealQ -> Circ FPRealQ
fprealq_add_param_in_place x qy = 
  with_ancilla_init (fpreal_promote x qy $ const e_prec)  (\qx -> do
    (qx, qy) <- fprealq_add_in_place qx qy
    return qy)
  where
    e_prec = "fprealq_sub_param_in_place: incompatible precision"

-- | Multiply an 'FPRealQ' by a parameter 'FPReal'.  The parameter may have any shape.
fprealq_mult_param_het :: FPReal -> FPRealQ -> Circ (FPRealQ, FPRealQ)
fprealq_mult_param_het x_in qy = do
  let x = fpreal_fix_shape_auto x_in
      e = fprealx_expt x
      l = fromJust $ intm_length $ fprealx_num x
      x_bits = boollist_of_intm_bh $ fprealx_num x
      qy_expt = fprealx_expt qy
      qy_num = fprealx_num qy
      qy_length = qdint_length qy_num
      prod_bits = [ (is_neg, i) | (x_i, i) <- zip x_bits [e+l-1,e+l-2..e]
                                    , x_i == True
                                    , let is_neg = i == e+l-1 ]
  qprod <- if null prod_bits 
           then qinit $ fpreal_promote 0 qy ("internal error: fprealq_mult_param_het promotion: " ++)
           else with_computed (do
             let i_max = snd $ head prod_bits
                 i_min = snd $ last prod_bits
  -- Initialise an accumulating product at 0, with as many bits as may be needed in intermediate calculation:
             qprod_accum <- qinit $ fprealx (qy_expt + i_min) $ intm (1 + qy_length + i_max - i_min) 0
  -- Add the appropriate shifts of qy to it:
             qprod_accum <- foldM
               (\qprod_accum (is_neg, i) -> do 
                 qy_i <- qc_copy $ fprealq_shift i qy
                 qy_i <- fprealq_pad (1 + i_max - i) (i - i_min) qy_i
                 (qy_i, qprod_accum) <- if is_neg
                   then fprealq_sub_in_place qy_i qprod_accum
                   else fprealq_add_in_place qy_i qprod_accum
                 return qprod_accum)
               qprod_accum
               prod_bits
  -- Now shift/truncate the product to match the input length/precision:
             qprod_large <- fprealq_pad (max (-i_max) 0) (max i_min 0) qprod_accum
             (qprod, garbage) <- fprealq_unpad (1 + max i_max 0) (max (-i_min) 0) qprod_large
             return qprod)
  -- Copy it for output, before erasing garbage:
           qc_copy
  return (qy, qprod)

-- | Compare an 'FPRealQ' to a parameter 'FPReal'.  Assume compatible precision.
-- 
-- Note: highly sub-optimal.  TODO: optimize!
fprealq_ge_param :: FPReal -> FPRealQ -> Circ (FPRealQ, Qubit)
fprealq_ge_param x qy =
  with_ancilla_init (fpreal_promote x qy $ const e_prec)  (\qx -> do
    (qx, qy, test) <- q_ge qx qy
    return (qy, test))
  where
    e_prec = "fprealq_ge_param: incompatible precision"

-- | 'q_add_fpreal_het' /p/ /l/ /qx/ /qy/: add two 'FPRealQ's, of potentially different precisions and lengths, into a fresh one with precision 'p' and length 'l'. 
--
-- TODO: not yet implemented; currently just black box.
fprealq_add_het :: Int -> Int -> FPRealQ -> FPRealQ -> Circ (FPRealQ,FPRealQ,FPRealQ)
fprealq_add_het p l qx qy = do
  qz <- qinit (fprealx p (intm l 0))
  (qx,qy,qz) <- named_gate "q_add_fpreal_het" (qx,qy,qz)
  return (qx,qy,qz)

-- | @'fprealq_logBase_internal' /errmsg/ /b/ /h/ /p/ /qx/'@: compute log[sub /b/](/qx/), returning /l/ binary digits before the point and /p/ after.  The underlying implementation of the rest of the 'fprealq_log' family. 
--
-- Behavior on non-positive /qx/: currently unspecified.  TODO: decide and fix this.  Make assertion/post-selection on positivity?  Or treat as unsigned?
--
-- Time-complexity (estimated): /O/((log /l/[sup /qx/] + log log /b/)(/l/[sup /qx/] + (/h/+/p/)[sup 2])).

-- Implementation note: see 'q_logBase_with_high_low' in "tests/FPRealLogs.hs" for discussion and tests.
fprealq_logBase_internal :: (Floating a, RealFrac a) => ErrMsg -> a -> Int -> Int -> FPRealQ -> Circ (FPRealQ, FPRealQ)
fprealq_logBase_internal e b h_out p_out x =
  if h_out + p_out < 0 
  then error $ e "negative length specified."
  else if b <= 0
  then error $ e "base of logarithm must be > 0"
  else do
    y <- with_computed 
      (do
  -- Shift x into the interval [0,1], and pad it for intermediate calculation:
        let l_in = qdint_length $ fprealx_num x
            e_in = fprealx_expt x
            l_in_pad = 1 + l_in `div` 2
            p_in_pad = p_out - (floor $ logBase 2 $ log b) + 1
        x_0 <- fprealq_pad l_in_pad p_in_pad $ fprealx (1 - l_in) $ fprealx_num x
  -- Bound the length and precision needed for computing log_2 x' to precision p_out: 
        let y_size_bound = 1 + (ceiling $ logBase 2 $ fromIntegral $ l_in - 1)
            y_h_pad = max 0 (y_size_bound - h_out)
            y_p_pad = 2 + (ceiling $ logBase 2 $ fromIntegral $ l_in_pad + p_in_pad - 1)
        y_0 <- qinit $ fprealx (- p_out - y_p_pad) $ intm (y_h_pad + h_out + p_out + y_p_pad) 0
  -- Iteratively compute log x_0, starting with (x0,y0): 
        let ks_big = 2^(l_in `div` 2)
                     : (reverse $ [ 2^(2^i) | i <- [0..(ceiling $ logBase 2 $ (fromIntegral l_in) / 2) - 1] ])
            ks_small = [ (2^i + 1)/(2^i) | i <- [1..p_out - (floor $ logBase 2 $ log b) + 1]]
        -- bound in ks_small chosen to ensure   logBase b k_fin < 2^(-p_out)
        (x_fin,y_fin) <- foldM
          (\(xi,yi) ki -> do
            (xi, xi_ki) <- fprealq_mult_param_het ki xi
            (xi_ki, test1) <- fprealq_ge_param 1 xi_ki
            (xi_ki, xi, test2) <- q_gt xi_ki xi
            (xi1, yi1) <- qc_copy (xi,yi)
            (xi1,xi) <- controlled_not xi1 xi `controlled` test1 .&&. test2 
            (xi1,xi_ki) <- controlled_not xi1 xi_ki `controlled` test1 .&&. test2 
            yi1 <- fprealq_sub_param_in_place (logBase (realToFrac b) ki) yi1 `controlled` test1 .&&. test2
            return (xi1, yi1))
          (x_0,y_0)
          (ks_big ++ ks_small)
    -- Correct for the shift between x and x_, then unpad y to the output precision:
        y_fin <- fprealq_add_param_in_place ((log 2 / log (realToFrac b)) * (fromIntegral $ l_in + e_in - 1)) y_fin
        (y_fin, garbage) <- fprealq_unpad y_h_pad y_p_pad y_fin
        return y_fin)
      qc_copy
    return (x,y)

-- | Compute the natural log of an 'FPRealQ', with length and precision as in the input.
--
-- Note: the behavior on negative inputs is unspecified.
fprealq_log :: FPRealQ -> Circ (FPRealQ,FPRealQ)
fprealq_log x = 
  let h = fprealx_length x + fprealx_expt x
      l = - fprealx_expt x 
  in fprealq_logBase_internal ("fprealq_log: " ++ ) (exp 1) h l x

-- | Compute the log (to arbitrary base) of an 'FPRealQ', with length and precision as in the input.
--
-- Note: the behavior on negative inputs is unspecified.
fprealq_logBase :: (Floating a, RealFrac a) => a -> FPRealQ -> Circ (FPRealQ,FPRealQ)
fprealq_logBase b x =
  let h = fprealx_length x + fprealx_expt x
      l = - fprealx_expt x 
  in fprealq_logBase_internal ("fprealq_logBase: " ++ ) b h l x

-- | @'fprealq_log_with_shape' /x/ /y/@: compute the natural log /y/, with length and precision of /x/.
--
-- Note: the behavior on negative inputs is unspecified.
fprealq_log_with_shape :: FPRealQ -> FPRealQ -> Circ (FPRealQ,FPRealQ)
fprealq_log_with_shape x = 
  let h = fprealx_length x + fprealx_expt x
      l = - fprealx_expt x 
  in fprealq_logBase_internal ("fprealq_log_with_shape: " ++ ) (exp 1) h l

-- | @'fprealq_log_with_shape' /b/ /x/ /y/@: compute log[sup /b/] /y/, with length and precision of /x/.
--
-- Note: the behavior on negative inputs is unspecified.
fprealq_logBase_with_shape :: (Floating a, RealFrac a)
                     => a -> FPRealQ -> FPRealQ -> Circ (FPRealQ,FPRealQ)
fprealq_logBase_with_shape b x =
  let h = fprealx_length x + fprealx_expt x
      l = - fprealx_expt x 
  in fprealq_logBase_internal ("fprealq_logBase_with_shape: " ++ ) b h l
