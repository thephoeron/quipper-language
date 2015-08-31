-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE DeriveDataTypeable  #-}

-- | This library provides a type of quantum integers, as well as
-- basic arithmetic functions on them.
-- 
-- The type 'QDInt' holds a fixed-size, ℓ-qubit quantum integer,
-- considered modulo 2[sup ℓ]. The integers may be regarded as
-- signed or unsigned, depending on the operation. If signs are used,
-- they are assumed to be in two's complement.
-- 
-- Some of the arithmetic operations are adapted from the GFI for the
-- Triangle Finding algorithm. Most algorithms used are, for now, very
-- naïve (ripple adders, etc).  Gate count estimates are given in the
-- Toffoli gatebase.

-- Documentation note: the table of contents is organized slightly
-- differently than the source code. The guiding idea is that the
-- documentation should expose the interface that is accessible to
-- user-level code, and changeable implementation details are hidden.

module QuipperLib.Arith (
  -- * Quantum integers
  -- ** Data type definitions
  -- $DATATYPES
  XInt,  -- constructors not exported
  QDInt,
  CInt,
  IntM,
  -- ** Operations on QDInt
  qulist_of_qdint_bh,
  qdint_of_qulist_bh,
  qulist_of_qdint_lh,
  qdint_of_qulist_lh,
  qdint_length,
  qdint_extend_unsigned,
  qdint_extend_signed,
  -- ** Operations on CInt
  bitlist_of_cint_bh,
  cint_of_bitlist_bh,
  bitlist_of_cint_lh,
  cint_of_bitlist_lh,
  cint_length,
  cint_extend_unsigned,
  cint_extend_signed,
  -- ** Operations on IntM
  -- $INTMCLASSES
  boollist_of_intm_bh,
  intm_of_boollist_bh,
  intm_length,
  integer_of_intm_unsigned,
  integer_of_intm_signed,
  intm_with_length,
  intm_of_integer,
  intm,
  intm_promote,
  intm_interval_signed,
  intm_interval_unsigned,
  intm_extend_unsigned,
  intm_extend_signed,
  -- ** Shape parameters
  qdint_shape,
  cint_shape,
  -- ** Operations on XInt
  xint_maybe_length,
  list_of_xint_bh,
  xint_of_list_bh,
  list_of_xint_lh,
  xint_of_list_lh,
  -- * Quantum arithmetic operations
  -- ** The QNum type class
  QNum(..),
  -- ** In-place increment and decrement
  q_increment,
  q_decrement,
  -- ** In-place addition and subtraction
  q_add_in_place,
  q_sub_in_place,
  q_negate_in_place,
  -- ** Arithmetic with classical parameter
  q_add_param,
  q_sub_param,
  q_add_param_in_place,
  q_sub_param_in_place,
  q_mult_param,
  -- ** Comparison
  q_le_unsigned,
  q_le_signed,
  q_lt_signed,
  q_negative,
  -- ** Division and remainder
  q_moddiv_unsigned_in_place,
  q_mod_unsigned,
  q_divrem_unsigned,
  q_div_unsigned,
  q_div,
  q_quot,
  q_div_exact_unsigned,
  q_div_exact,
  -- ** Specialized functions
  q_ext_euclid,
  -- * Lifting of arithmetic functions
  -- $LIFTING
  template_symb_plus_,
  ) where

import Quipper
import Quipper.Internal

import Libraries.Sampling
import Libraries.Auxiliary

import Control.Monad
import Data.Typeable

-- ======================================================================
-- * Quantum integers

-- ** Data type definitions

-- $DATATYPES 
-- We define three versions of the fixed-length integer type: quantum,
-- classical input, and classical parameter. The triple ('IntM',
-- 'QDInt', 'CInt') forms an instance of the 'QShape' class.  All three
-- types are special cases of the type 'XInt' /x/.

-- | 'XInt' /x/ is the type of fixed-length integers, but using
-- elements of type /x/ instead of bits. It is an abstract type, and
-- details of its implementation is not exposed to user-level code.

-- Implemenation notes: The integer types are currently implemented as
-- big-headian bit lists. However, the details of the implementation
-- are not exposed to user-level code, and are subject to change.
-- 
-- The form ('XInt_indet' /n/ /id/) is permitted as a special case, to
-- represent an integer of indeterminate length. Such a value can only
-- be used when the length is deducible from the context. This form is
-- only allowed in the special case /x/ = 'Bool', and we use an
-- identity type to enforce this.
-- 
-- Integers of indeterminate length may only be used in certain
-- operations where the shape information is available from other
-- data. It can be used, for example, for terminating or controlling a
-- 'QDInt', but not for initializing a 'QDInt'.
data XInt x = XInt [x] | XInt_indet Integer (Identity Bool x)
  deriving (Show, Typeable)

-- | The type of fixed-length /m/-qubit quantum integers. This is a
-- circuit execution time value.
type QDInt = XInt Qubit

instance Show QDInt where
  show (XInt l) = "#" ++ show l
  show (XInt_indet n id) = error "IntM: internal error"

-- A better implementation might be something like:
--   show (XInt l) = "qdint_of_qulist_bh " ++ show l
-- However, as 'CInt' and 'QDInt' are currently synonyms, it seems best
-- to keep the instance agnostic between them, while still distinguishing
-- them somehow from naked lists.

-- | The type of fixed-length /m/-bit classical integer inputs. This
-- is a circuit execution time value.
type CInt = XInt Bit

-- Currently, 'CInt' is literally a synonym of 'QDInt', since 'Qubit' is
-- a synonym of 'Bit'.  If this changes, the following instance will be
-- required:
--
-- instance Show CInt where
--   show (XInt l) = show l
--   show (XInt_indet n id) = error "IntM: internal error"

-- | The type of fixed-length /m/-bit integer parameters.  Values of
-- this type are parameters, i.e., they are classical and known at
-- circuit generation time.
-- 
-- Unlike values of type 'QDInt' and 'CInt', a value of type 'IntM'
-- may have an indeterminate length. This happens, for example, if the
-- value is specified by means of an integer literal (e.g., 17), which
-- does not carry length information. In such cases, the value can
-- only be used when it can be deduced from the context. For example,
-- such values may be used for terminating or controlling a 'QDInt',
-- but not for initializing a 'QDInt'.
type IntM = XInt Bool

instance Show IntM where
  show (XInt l) = "intm " ++ show (length l) ++ " " ++ show (int_of_boollist_signed_bh l)
  show (XInt_indet n id) = show n

-- Note: for the purpose of forming intervals, we regard 'IntM' as an
-- /unsigned/ type.  This disagrees with the 'Enum' instance, where
-- 'IntM' is regarded as a /signed/ type. So for example, when /x/ =
-- 'intm' 4 (-2) = 'intm' 4 14 and /y/ = 'intm' 4 10, then [/x/../y/]
-- and 'interval' /y/ /x/ are non-empty, but [/y/../x/] and 'interval'
-- /x/ /y/ are empty. 
-- 
-- This is confusing but for the time being there is no better
-- alternative, unless we create distinct signed and unsigned types.

instance Interval IntM where
  interval x y = intm_interval_unsigned x y

instance Zero IntM where
  zero x = intm_with_length (intm_length x) 0
  
-- ----------------------------------------------------------------------
-- ** Primitive combinators on XInt

-- $ 'XInt' is intended to be an abstract data type, and all access to
-- it should pass through the three access functions of this
-- section.

-- *** Constructors

-- | Create a 'XInt' /x/ from a list of /x/s. The conversion is
-- big-headian, i.e., the head of the list holds the most significant
-- digit.
xint_of_list_bh :: [x] -> XInt x
xint_of_list_bh xs = XInt xs

-- | Create an 'IntM' of indeterminate length from an 'Integer'. 
intm_of_integer :: Integer -> IntM
intm_of_integer n = XInt_indet n reflexivity

-- *** Destructor

-- | If the 'XInt' is of determinate length, return its list of digits
-- as a big-headian list, i.e., the head of the list holds the most
-- significant digit. If the 'XInt' is of indeterminate length, return
-- (/n/, /id/), where /n/ is the underlying 'Integer' and /id/ is the
-- witness proving that /x/ = 'Bool'.
-- 
-- This is a lowest-level access function not intended to be used by
-- user-level code.
xint_case :: XInt x -> Either [x] (Integer, Identity Bool x)
xint_case (XInt xs) = Left xs
xint_case (XInt_indet n id) = Right (n, id)

-- ----------------------------------------------------------------------
-- ** Other low-level operations

-- $ The operations in this section are the only ones intended to use
-- 'xint_case' directly.

-- | Set the length of an 'XInt' to /m/ ≥ 0. This operation is only
-- legal if the input (a) has indeterminate length or (b) has
-- determinate length already equal to /m/. In particular, it cannot
-- be used to change the length from anything other than from
-- indeterminate to determinate.
-- 
-- If both arguments already have determinate lengths, and they do not
-- coincide, throw an error. The 'String' argument is used as an error
-- message in that case.
-- 
-- Note that if /x/ ≠ 'Bool', the input is guaranteed to have
-- determinate length. However, we cannot test for equality of types
-- in a polymorphic function. This is where the 'id' argument to
-- 'XInt_indet' is used.
xint_set_length :: Int -> XInt x -> String -> XInt x
xint_set_length m x errmsg | m < 0 = 
  error "xint_set_length: negative length not permitted"  
xint_set_length m x errmsg =
  case xint_case x of
    Left xs | m == length xs -> x
            | otherwise -> error errmsg
    Right (n, id) -> XInt xs where
      xs = [ identity id b | b <- boollist_of_int_bh m n ]

-- | Return 'True' if the 'XInt' is of determinate length, and 'False'
-- if it is of indeterminate length. 
xint_is_determinate :: XInt x -> Bool
xint_is_determinate x = 
  case xint_case x of
    Left _ -> True
    Right _ -> False

-- | From a 'XInt', which must be of determinate length, extract a
-- list of /x/s. The conversion is big-headian, i.e., the head of the
-- list holds the most significant digit. It is an error to call this
-- function with an 'XInt' of indeterminate length.
list_of_xint_bh :: XInt x -> [x]
list_of_xint_bh x = 
  case xint_case x of
    Left xs -> xs
    Right _ -> error "list_of_xint_bh: integer has indeterminate length"

-- | Return the size of a 'XInt', or 'Nothing' if indeterminate.
xint_maybe_length :: XInt x -> Maybe Int
xint_maybe_length x =
  case xint_case x of
    Left xs -> Just (length xs)
    Right _ -> Nothing

-- | Convert an 'IntM' of length /m/ to an 'Integer' in the range {0,
-- …, 2[sup /m/]-1}. If the 'IntM' has indeterminate length, return the
-- original 'Integer'.
integer_of_intm_unsigned :: IntM -> Integer
integer_of_intm_unsigned x = 
  case xint_case x of
    Left xs -> int_of_boollist_unsigned_bh xs
    Right (n, id) -> n

-- | Convert an 'IntM' of length /m/ to an 'Integer' in the range
-- {-2[sup /m/-1], …, 2[sup /m/-1]-1}. If the 'IntM' has indeterminate
-- length, return the original 'Integer'.
integer_of_intm_signed :: IntM -> Integer
integer_of_intm_signed x =
  case xint_case x of
    Left xs -> int_of_boollist_signed_bh xs
    Right (n, id) -> n

-- | Equality test. If at least one argument has determinate length,
-- test equality modulo 2[sup /m/]. If both have indeterminate length,
-- check equality of the underlying integers.
xint_equals :: (Eq x) => XInt x -> XInt x -> Bool    
xint_equals x y =
  case (xint_case x, xint_case y) of
    (Left xs, Left ys) 
      | length xs == length ys -> xs == ys
      | otherwise -> error "Equality test on XInt: operands must be of equal length"
    (_, Left ys) -> xint_equals (xint_set_length m x "xint_equals") y
        where m = length ys
    (Left xs, _) -> xint_equals x (xint_set_length m y "xint_equals")
        where m = length xs
    (Right (n, _), Right (n', _)) -> n == n'
    
-- ----------------------------------------------------------------------
-- ** Derived operations on XInt

-- | Get the nominal length of an integer (in bits). It is an error to
-- apply this function to an integer of indeterminate length.
xint_length :: XInt x -> Int
xint_length x = 
  case xint_maybe_length x of
    Just m -> m
    Nothing -> error "xint_length: integer has indeterminate length"

-- | Convert an integer to a bit list. The conversion is
-- little-headian, i.e., the head of the list holds the least
-- significant digit.
list_of_xint_lh :: XInt x -> [x]
list_of_xint_lh = reverse . list_of_xint_bh

-- | Convert a bit list to an integer. The conversion is
-- little-headian, i.e., the head of the list holds the least
-- significant digit.
xint_of_list_lh :: [x] -> XInt x
xint_of_list_lh = xint_of_list_bh . reverse

-- | Extend a 'XInt' to the given length without changing its
-- (unsigned) value. This is done by adding the required number of
-- high bits initialized to /zero/. It is an error to call this
-- function when the new length is shorter than the old one.
xint_extend_unsigned :: (Monad m) => Int -> m x -> XInt x -> m (XInt x)
xint_extend_unsigned len zero x 
  | len < m =
    error "pad_xint: requested length is shorter than current length"
  | otherwise = do
    pad <- sequence (replicate extra zero)
    return $ xint_of_list_bh (pad ++ digits)
  where
    digits = list_of_xint_bh x
    m = length digits
    extra = len - m

-- | Extend a 'XInt' to the given length without changing its (signed)
-- value. This is done by adding the required number of high bits
-- initialized to copies of the sign bit (or to /zero/ if the original
-- integer was of length 0). It is an error to call this function when
-- the new length is shorter than the old one.
xint_extend_signed :: (Monad m) => Int -> m x -> (x -> m x) -> XInt x -> m (XInt x)
xint_extend_signed len zero copy x
  | len < m 
    = error "pad_xint: requested length is shorter than current length"
  | m == 0
    = xint_extend_unsigned len zero x
  | otherwise = do
    pad <- sequence (replicate extra (copy sign))
    return $ xint_of_list_bh (pad ++ digits)
  where
    digits = list_of_xint_bh x
    m = length digits
    extra = len - m
    sign = head digits

-- ----------------------------------------------------------------------
-- ** Operations on IntM

-- | Return the size of an 'IntM', or 'Nothing' if indeterminate.
intm_length :: IntM -> Maybe Int
intm_length = xint_maybe_length
  
-- | Convert an 'IntM' to a list of booleans. The conversion is
-- big-headian, i.e., the head of the list holds the most significant
-- digit. As usual, 'False' is 0 and 'True' is 1. It is an error to
-- apply this operation to an 'IntM' whose length is indeterminate.
boollist_of_intm_bh :: IntM -> [Bool]
boollist_of_intm_bh = list_of_xint_bh

-- | Convert a boolean list to an 'IntM'. The conversion is
-- big-headian, i.e., the head of the list holds the most significant
-- digit.
intm_of_boollist_bh :: [Bool] -> IntM
intm_of_boollist_bh = xint_of_list_bh

-- | Create an 'IntM' of the specified length (first argument) and
-- value (second argument).
intm :: Int -> Integer -> IntM
intm m n = intm_set_length m (intm_of_integer n) "intm: internal error"

-- | Set the length of an 'IntM' to /m/ ≥ 0. This operation is only
-- legal if the input (a) has indeterminate length or (b) has
-- determinate length already equal to /m/. In particular, it cannot
-- be used to change the length from anything other than from
-- indeterminate to determinate. (Use 'intm_extend_unsigned' or
-- 'intm_extend_signed' to increase a determinate length).
-- 
-- If both arguments already have determinate lengths, and they do not
-- coincide, throw an error. The 'String' argument is used as an error
-- message in that case.
intm_set_length :: Int -> IntM -> String -> IntM
intm_set_length = xint_set_length

-- | Extend an 'IntM' to the given length without changing its
-- (unsigned) value. This is done by adding the required number of
-- high bits initialized to 0. It is an error to call this function
-- when the new length is shorter than the old one.
intm_extend_unsigned :: Int -> IntM -> IntM
intm_extend_unsigned len x =
  getId $ xint_extend_unsigned len (return False) x

-- | Extend an 'IntM' to the given length without changing its
-- (signed) value. This is done by adding the required number of
-- high bits initialized to copies of the sign bit. It is an error to
-- call this function when the new length is shorter than the old one.
intm_extend_signed :: Int -> IntM -> IntM
intm_extend_signed len x =
  getId $ xint_extend_signed len (return False) (return) x

-- ----------------------------------------------------------------------
-- ** Operations on CInt

-- | Convert a 'CInt' to a list of qubits. The conversion is
-- big-headian, i.e., the head of the list holds the most significant
-- digit.
bitlist_of_cint_bh :: CInt -> [Bit]
bitlist_of_cint_bh = list_of_xint_bh

-- | Convert a list of qubits to a 'CInt'. The conversion is
-- big-headian, i.e., the head of the list holds the most significant
-- digit.
cint_of_bitlist_bh :: [Bit] -> CInt
cint_of_bitlist_bh = xint_of_list_bh

-- | Convert a 'CInt' to a list of bits. The conversion is
-- little-headian, i.e., the head of the list holds the least
-- significant digit.
bitlist_of_cint_lh :: CInt -> [Bit]
bitlist_of_cint_lh = list_of_xint_lh

-- | Convert a list of bits to a 'CInt'. The conversion is
-- little-headian, i.e., the head of the list holds the least significant
-- digit.
cint_of_bitlist_lh :: [Bit] -> CInt
cint_of_bitlist_lh = xint_of_list_lh

-- | Return the length of a 'CInt', in bits.
cint_length :: CInt -> Int
cint_length = xint_length

-- | Extend a 'CInt' to the given length without changing its
-- (unsigned) value. This is done by adding the required number of
-- high bits initialized to 0. It is an error to call this function
-- when the new length is shorter than the old one.
cint_extend_unsigned :: Int -> CInt -> Circ CInt
cint_extend_unsigned len x =
  xint_extend_unsigned len (cinit False) x

-- | Extend a 'CInt' to the given length without changing its
-- (signed) value. This is done by adding the required number of
-- high bits initialized to copies of the sign bit. It is an error to
-- call this function when the new length is shorter than the old one.
cint_extend_signed :: Int -> CInt -> Circ CInt
cint_extend_signed len x =
  xint_extend_signed len (cinit False) (qc_copy) x

-- ----------------------------------------------------------------------
-- ** Operations on QDInt

-- | Convert a 'QDInt' to a list of qubits. The conversion is
-- big-headian, i.e., the head of the list holds the most significant
-- digit.
qulist_of_qdint_bh :: QDInt -> [Qubit]
qulist_of_qdint_bh = list_of_xint_bh

-- | Convert a list of qubits to a 'QDInt'. The conversion is
-- big-headian, i.e., the head of the list holds the most significant
-- digit.
qdint_of_qulist_bh :: [Qubit] -> QDInt
qdint_of_qulist_bh = xint_of_list_bh

-- | Convert a 'QDInt' to a list of qubits. The conversion is
-- little-headian, i.e., the head of the list holds the least significant
-- digit.
qulist_of_qdint_lh :: QDInt -> [Qubit]
qulist_of_qdint_lh = list_of_xint_lh

-- | Convert a list of qubits to a 'QDInt'. The conversion is
-- little-headian, i.e., the head of the list holds the least significant
-- digit.
qdint_of_qulist_lh :: [Qubit] -> QDInt
qdint_of_qulist_lh = xint_of_list_lh

-- | Return the length of a 'QDInt', in bits.
qdint_length :: QDInt -> Int
qdint_length = xint_length

-- | Extend a 'QDInt' to the given length without changing its
-- (unsigned) value. This is done by adding the required number of
-- high bits initialized to 0. It is an error to call this function
-- when the new length is shorter than the old one.
qdint_extend_unsigned :: Int -> QDInt -> Circ QDInt
qdint_extend_unsigned len x =
  xint_extend_unsigned len (qinit False) x

-- | Extend a 'QDInt' to the given length without changing its
-- (signed) value. This is done by adding the required number of
-- high bits initialized to copies of the sign bit. It is an error to
-- call this function when the new length is shorter than the old one.
qdint_extend_signed :: Int -> QDInt -> Circ QDInt
qdint_extend_signed len x =
  xint_extend_signed len (qinit False) (qc_copy) x

-- ----------------------------------------------------------------------
-- ** Shape parameters

-- | Return a piece of shape data to represent an /m/-qubit quantum
-- integer. Please note that the data can only be used as shape; it
-- will be undefined at the leaves.
qdint_shape :: Int -> QDInt
qdint_shape m = xint_of_list_bh (replicate m qubit)

-- | Return a piece of shape data to represent an /m/-bit 'CInt'.
-- Please note that the data can only be used as shape; it will be
-- undefined at the leaves.
cint_shape :: Int -> CInt
cint_shape m = xint_of_list_bh (replicate m bit)

-- ======================================================================
-- ** Type class instances

-- Note: instance declarations do not show up in the documentation

-- | Input the lengths of two inputs to a binary operation, and return
-- the common length. If one length is indeterminate, return the other;
-- if both are indeterminate, return 'Nothing'; if both are determinate but
-- not equal, throw an error with the given error message.
combine_length :: String -> Maybe Int -> Maybe Int -> Maybe Int
combine_length s Nothing m = m
combine_length s m Nothing = m
combine_length s (Just m) (Just m') | m == m' = Just m
                                    | otherwise = error s

-- | Try to set the length of an 'IntM' to that of another 'XInt'
-- value (which could be a 'QDInt', a 'CInt', or another 'IntM'). This
-- will fail with an error if both numbers already have determinate
-- lengths that don't coincide. In this case, the string argument is
-- used as an error message.
intm_promote :: IntM -> XInt x -> String -> IntM
intm_promote bi xi errmsg = 
  case xint_maybe_length xi of
    Nothing -> bi
    Just m -> intm_set_length m bi errmsg
    
type instance QCType x y (XInt z) = XInt (QCType x y z)
type instance QTypeB IntM = QDInt

instance QCLeaf x => QCData (XInt x) where
  qcdata_mapM shape f g xs = 
    mmap xint_of_list_bh $ qcdata_mapM (list_of_xint_bh shape) f g (list_of_xint_bh xs)
  qcdata_zip shape q c q' c' xs ys e = 
    xint_of_list_bh $ qcdata_zip (list_of_xint_bh shape) q c q' c' (list_of_xint_bh xs) (list_of_xint_bh ys) (const $ e "XInt length mismatch")
  qcdata_promote b q e = intm_promote b q (e "IntM length mismatch")

-- Labeling of QDInt is s[m-1], ..., s[0], with the least significant
-- bit at index 0.
instance QCLeaf x => Labelable (XInt x) String where
  label_rec qa = label_rec (list_of_xint_lh qa)

instance CircLiftingUnpack (Circ QDInt) (Circ QDInt) where
  pack x = x
  unpack x = x

-- ======================================================================
-- * Classical arithmetic on 'IntM'

-- ----------------------------------------------------------------------
-- ** Auxiliary functions
  
-- | A useful auxiliary function that converts a list of 'IntM's to a
-- list of 'Integer's, while also returning their common length. All
-- arguments whose length is not indeterminate must have the same common
-- length. If the lengths don't match, throw an error with the error
-- message specified by the 'String' argument.
integers_of_intms_signed :: [IntM] -> String -> (Maybe Int, [Integer])
integers_of_intms_signed xs s = (m, is) where
  m = foldl (combine_length s) Nothing [ intm_length x | x <- xs ]
  is = [ integer_of_intm_signed x | x <- xs ]  

-- | Like 'integers_of_intms_signed', but regards the 'IntM's as
-- unsigned integers.
integers_of_intms_unsigned :: [IntM] -> String -> (Maybe Int, [Integer])
integers_of_intms_unsigned xs s = (m, is) where
  m = foldl (combine_length s) Nothing [ intm_length x | x <- xs ]
  is = [ integer_of_intm_unsigned x | x <- xs ]  

-- | Create an 'IntM' of the given length and value. Leave the length
-- indeterminate if it is given as 'Nothing'.
intm_with_length :: Maybe Int -> Integer -> IntM
intm_with_length (Just m) n = intm m n
intm_with_length Nothing n = intm_of_integer n

-- | Auxiliary function for lifting a binary operator from 'Integer'
-- to 'IntM'. The string argument is the name of the operator, for
-- error messages.
intm_binop :: (Integer -> Integer -> Integer) -> String -> IntM -> IntM -> IntM 
intm_binop op opname x y = intm_with_length m (op x' y') where
  (m, [x',y']) = integers_of_intms_signed [x, y] ("Binary operation " ++ opname ++ " on IntM: operands must be of equal length")

-- | Auxiliary function for lifting a unary operator from 'Integer' to
-- 'IntM'.
intm_unop :: (Integer -> Integer) -> IntM -> IntM
intm_unop op x = intm_with_length xm (op x') where
  xm = intm_length x
  x' = integer_of_intm_signed x
  
-- ----------------------------------------------------------------------
-- ** Type class instances

-- $INTMCLASSES 
-- 
-- 'IntM' is an instance of Haskell's 'Eq', 'Num', 'Ord', 'Real',
-- 'Enum', and 'Integral' type classes. This means that integer
-- literals (e.g., 17), and the usual arithmetic functions, such as
-- '+', '-', '*', 'abs', 'succ', 'pred', 'mod', 'div', and others, can
-- be used for values of type 'IntM'. In general, we treat 'IntM' as a
-- signed integer type. Use 'fromIntegral' to convert an integer to an
-- 'IntM' of indeterminate length.
-- 
-- The general convention for binary operations (such as
-- multiplication) is: both operands must have the same length,
-- except: if one operand has indeterminate length, it takes on the
-- length of the other; if both operands have indeterminate length, the
-- result will have indeterminate length.

instance Eq x => Eq (XInt x) where
  x == y = xint_equals x y
    
instance Num IntM where
  (+) = intm_binop (+) "+"
  (*) = intm_binop (*) "*"
  (-) = intm_binop (-) "-"
  abs = intm_unop abs
  signum = intm_unop signum
  fromInteger = intm_of_integer

instance Ord IntM where
  compare x y = compare (toInteger x) (toInteger y)

instance Real IntM where
  toRational = toRational . integer_of_intm_signed

instance Enum IntM where
  succ = intm_unop succ
  pred = intm_unop pred
  toEnum = intm_of_integer . fromIntegral
  fromEnum = fromIntegral . integer_of_intm_signed
  enumFrom x = map (intm_with_length m) [x'..] where
    (m, [x']) = integers_of_intms_signed [x] "enumeration: IntM"
  enumFromThen x y = map (intm_with_length m) [x',y'..] where
    (m, [x',y']) = integers_of_intms_signed [x,y] "enumeration: IntM operands must be of equal length"
  enumFromTo x y = map (intm_with_length m) [x'..y'] where
    (m, [x',y']) = integers_of_intms_signed [x,y] "enumeration: IntM operands must be of equal length"
  enumFromThenTo x y z = map (intm_with_length m) [x',y'..z'] where
    (m, [x',y',z']) = integers_of_intms_signed [x,y,z] "enumeration: IntM operands must be of equal length"

-- | Return the interval @[/x/../y/]@, with /x/ and /y/ regarded as
-- signed values of type 'IntM'.
intm_interval_signed :: IntM -> IntM -> [IntM]
intm_interval_signed x y = [x..y]  -- this comes from the 'Enum' instance defined above

-- | Return the interval @[/x/../y/]@, with /x/ and /y/ regarded as
-- unsigned values of type 'IntM'.
intm_interval_unsigned :: IntM -> IntM -> [IntM]
intm_interval_unsigned x y = map (intm_with_length m) [x'..y'] where
  (m, [x',y']) = integers_of_intms_unsigned [x,y] "intm_interval: operands must be of equal length"

instance Integral IntM where
  toInteger = integer_of_intm_signed
  quotRem x y = (intm_with_length m q', intm_with_length m r') where
    (m, [x',y']) = integers_of_intms_signed [x, y] "Division on IntM: operands must be of equal length"
    (q',r') = quotRem x' y'

-- ======================================================================
-- * Quantum arithmetic on 'QDInt'

-- Developer note: each quantum arithmetic function is implemented by
-- an underlying low-level function operating on qubit lists. However,
-- these lower-level functions are *not* exported. If any module needs
-- them, it should define them explicitly using 'qulist_of_qdint_bh'
-- and 'qdint_of_qulist_bh'. In particular, the low-level functions
-- may not perform error checking if it is already performed by their
-- high-level counterparts.

-- ----------------------------------------------------------------------
-- ** Auxiliary functions

-- | @'common_value' error_str [n1,n2,n3]@: if /n1/, /n2/, /n3/ all equal, return this value; else throw an error.  Useful for checking that sizes of 'QDInt's match.
common_value :: (Eq a) => String -> [a] -> a
common_value _ [] = error "common_value: no inputs given"
common_value _ [n] = n
common_value error_str (n:ns) = if common_value error_str ns == n then n else error error_str

-- | @'common_length' error_str [x1,x2,x3]@: if /x1/, /x2/, /x3/ all have the same length, return this value; else throw an error. 
common_length :: String -> [QDInt] -> Int
common_length error_str xs = common_value error_str $ map qdint_length xs

-- ----------------------------------------------------------------------
-- ** Incrementing and decrementing

-- | Increment a 'QDInt' in place.  /O/(ℓ) gates. 
-- 
-- Implementation note: currently tries to minimize gate count, at the cost of a rather long Quipper description.  Can the latter be reduced without increasing the former?  
q_increment :: QDInt -> Circ QDInt
q_increment = mmap xint_of_list_bh . q_increment_qulist . list_of_xint_bh

-- | Low-level implementation of 'q_increment': represents integers as
-- big-headian qubit lists.
q_increment_qulist :: [Qubit] -> Circ [Qubit]
q_increment_qulist [] = return []
q_increment_qulist [x_0] = do x_0 <- qnot x_0; return [x_0]
q_increment_qulist [x_1,x_0] = do x_0 <- qnot x_0; x_1 <- qnot x_1 `controlled` (x_0 .==. 0); return [x_1,x_0]
q_increment_qulist [x_2,x_1,x_0] = do
  x_0 <- qnot x_0
  x_1 <- qnot x_1 `controlled` (x_0 .==. 0)
  x_2 <- qnot x_2 `controlled` (x_0 .==. 0) .&&. (x_1 .==. 0)
  return [x_2,x_1,x_0]
q_increment_qulist x_bits = do
  let x_0 = last x_bits
      x_1 = last $ init x_bits
      x_higher = init $ init $ x_bits
  x_0 <- qnot x_0
  x_1 <- qnot x_1 `controlled` (x_0 .==. 0)
  (x_higher,x_1,x_0) <- with_ancilla (\c -> do
    c <- qnot c `controlled` (x_0 .==. 0) .&&. (x_1 .==. 0)
    (c,rev_x_higher) <- q_increment_qulist_aux c (reverse x_higher)
    c <- qnot c `controlled` (x_0 .==. 0) .&&. (x_1 .==. 0)
    return (reverse rev_x_higher, x_1, x_0))
  return (x_higher ++ [x_1,x_0])
  where
  -- increment a LITTLE-endian bit-string, controlled by a single qubit.
    q_increment_qulist_aux :: Qubit -> [Qubit] -> Circ (Qubit,[Qubit])
    q_increment_qulist_aux b [] = return (b,[])
    q_increment_qulist_aux b [x_0] =
      do x_0 <- qnot x_0 `controlled` b; return (b,[x_0])
    q_increment_qulist_aux b [x_0,x_1] = do
      x_0 <- qnot x_0 `controlled` b
      x_1 <- qnot x_1 `controlled` b .&&. (x_0 .==. 0)
      return (b,[x_0,x_1])
    q_increment_qulist_aux b (x_0:x_higher) = do
      x_0 <- qnot x_0 `controlled` b 
      (b,x_0,x_higher) <- with_ancilla (\c -> do
        c <- qnot c `controlled` b .&&. (x_0 .==. 0)
        (c,x_higher) <- q_increment_qulist_aux c x_higher
        c <- qnot c `controlled` b .&&. (x_0 .==. 0)
        return (b,x_0,x_higher))
      return (b, (x_0:x_higher))
    
-- | Decrement a 'QDInt' in place.  Inverse of 'q_increment'. /O/(ℓ).
q_decrement :: QDInt -> Circ QDInt
q_decrement = reverse_generic_endo q_increment

-- ----------------------------------------------------------------------
-- ** Addition and subtraction

-- | Add two 'QDInt's into a fresh one.  Arguments are assumed to be of equal size.  /O/(ℓ) gates, both before and after transformation to Toffoli.
q_add_qdint :: QDInt -> QDInt -> Circ (QDInt, QDInt, QDInt)
q_add_qdint x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (x', y', z') <- q_add_qulist x' y'
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  let z = xint_of_list_bh z'
  return (x, y, z)

-- | Low-level implementation of 'q_add_qdint': represents integers as
-- big-headian qubit lists.
q_add_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit], [Qubit], [Qubit])
q_add_qulist x y = do
  let l = length x
  when (l /= length y) $ do
    error "q_add_qdint: cannot add QDInts of different lengths"

  ((x,y),s_out) <- with_computed_fun (x,y)
    (\(x,y) -> do
      s <- qinit (replicate l False) -- holds the eventual sum
      c <- qinit (replicate l False) -- holds the carries

      -- bring the lists’ indexing in line with usual numeric indexing of binary expansons
      x <- return $ reverse x
      y <- return $ reverse y
      s <- return $ reverse s
      c <- return $ reverse c

      (x,y,s,c) <- loop_with_indexM (l-1) (x,y,s,c) (\j (x,y,s,c) -> do
        let c_j1 = c !! (j+1)
        let s_j = s !! j
        -- If any two of the current bits x_j, y_j, and the carry c_j are true, then set the next carry:
        -- (Note: we use that (a & b) xor (a & c) xor (b & c) == (a & b) or (a & c) or (b & c).)
        c_j1 <- qnot c_j1 `controlled` (x!!j .&&. y!!j)
        c_j1 <- qnot c_j1 `controlled` (x!!j .&&. c!!j)
        c_j1 <- qnot c_j1 `controlled` (y!!j .&&. c!!j)
        -- Now the current sum digit is computed mod 2:
        s_j <- qnot s_j `controlled` (x!!j)
        s_j <- qnot s_j `controlled` (y!!j)
        s_j <- qnot s_j `controlled` (c!!j) 
        c <- return $ overwriteAt (j+1) c_j1 c
        s <- return $ overwriteAt j s_j s

        return (x,y,s,c))

      -- Final sum digit; no carry required:
      let s_l1 = s !! (l-1)
      s_l1 <- qnot s_l1 `controlled` (x!!(l-1))
      s_l1 <- qnot s_l1 `controlled` (y!!(l-1))
      s_l1 <- qnot s_l1 `controlled` (c!!(l-1)) 
      s <- return $ overwriteAt (l-1) s_l1 s
     
      x <- return $ reverse x
      y <- return $ reverse y
      s <- return $ reverse s
      c <- return $ reverse c

      return (x,y,s,c))
    
    (\(x,y,s,c) -> do
      (s,s_out) <- qc_copy_fun s
      return ((x,y,s,c), s_out))
  return (x, y, s_out)

-- | Subtract two 'QDInt's, into a fresh one.  Arguments are assumed to be of equal size.  /O/(ℓ).
q_sub_qdint :: QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt)
q_sub_qdint x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (x', y', z') <- q_sub_qulist x' y'
  let x = xint_of_list_bh x'  
  let y = xint_of_list_bh y'
  let z = xint_of_list_bh z'
  return (x, y, z)

-- | Low-level implementation of 'q_sub_qdint': represents integers as
-- big-headian qubit lists.
q_sub_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit], [Qubit], [Qubit])
q_sub_qulist x y = do
  let l = length x
  when (l /= length y) $ do
    error "q_sub_qdint: cannot subtract QDInts of different lengths"
  
  ((x,y),d_out) <- with_computed_fun (x,y)
    (\(x,y) -> do
      d <- qinit (replicate l False) -- holds the eventual difference
      b <- qinit (replicate l False) -- holds the borrows

      -- bring the lists’ indexing in line with usual numeric indexing of binary expansons
      x <- return $ reverse x
      y <- return $ reverse y
      d <- return $ reverse d
      b <- return $ reverse b

      (x,y,d,b) <- loop_with_indexM (l-1) (x,y,d,b) (\j (x,y,d,b) -> do
        let b_j1 = b !! (j+1)
        let d_j = d !! j
        -- If any two of (not x_j), y_j, and the borrow c_j hold, then set the next borrow.
        -- (Note: we use that (a & b) xor (a & c) xor (b & c) == (a & b) or (a & c) or (b & c).)
        b_j1 <- qnot b_j1 `controlled` (x!!j .==. 0) .&&. (y!!j .==. 1)
        b_j1 <- qnot b_j1 `controlled` (x!!j .==. 0) .&&. (b!!j .==. 1)
        b_j1 <- qnot b_j1 `controlled` (y!!j .==. 1) .&&. (b!!j .==. 1)
        -- Now the current difference digit is computed mod 2:
        d_j <- qnot d_j `controlled` (x!!j)
        d_j <- qnot d_j `controlled` (y!!j)
        d_j <- qnot d_j `controlled` (b!!j) 
        b <- return $ overwriteAt (j+1) b_j1 b
        d <- return $ overwriteAt j d_j d
        return (x,y,d,b))

      -- Final difference digit; no carry required:
      let d_l1 = d !! (l-1)
      d_l1 <- qnot d_l1 `controlled` (x!!(l-1))
      d_l1 <- qnot d_l1 `controlled` (y!!(l-1))
      d_l1 <- qnot d_l1 `controlled` (b!!(l-1)) 
      d <- return $ overwriteAt (l-1) d_l1 d

      -- bring the lists’ indexing in line with usual numeric indexing of binary expansons
      x <- return $ reverse x
      y <- return $ reverse y
      d <- return $ reverse d
      b <- return $ reverse b

      return (x,y,d,b))
    
    (\(x,y,d,b) -> do
      (d,d_out) <- qc_copy_fun d
      return ((x,y,d,b), d_out))
  return (x, y, d_out)

-- | Add one 'QDInt' onto a second, in place; i.e. (/x/,/y/) ↦ (/x/,/x/+/y/).  Arguments are assumed to be of equal size.  /O/(ℓ) gates.
q_add_in_place :: QDInt -> QDInt -> Circ (QDInt,QDInt)
q_add_in_place x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (x', y') <- q_add_in_place_qulist x' y'
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  return (x, y)

-- | Low-level implementation of 'q_add_in_place': represents integers
-- as big-headian qubit lists.
q_add_in_place_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit], [Qubit])
q_add_in_place_qulist [] [] = return ([], [])
q_add_in_place_qulist [x0] [y0] = do
  y0 <- qnot y0 `controlled` x0
  return ([x0], [y0])
q_add_in_place_qulist x y = do
  let (x0:x_higher) = reverse x  
      (y0:y_higher) = reverse y

  y0 <- qnot y0 `controlled` x0

  ((x0,y0),(x_higher,y_higher)) <- with_computed_fun (x0,y0)
    (\(x0,y0) -> do
      c <- qinit False
      c <- qnot c `controlled` (x0 .==. 1) .&&. (y0 .==. 0)
      return (x0,y0,c))
    (\(x0,y0,c) -> do
      (x_higher,y_higher,c) <- q_add_aux (x_higher) (y_higher) c
      return ((x0,y0,c),(x_higher,y_higher)))
  return (reverse (x0:x_higher), reverse (y0:y_higher))
  where
  -- Aux: add two LITTLE-endian bit strings, and an optional extra 1.
    q_add_aux :: [Qubit] -> [Qubit] -> Qubit -> Circ ([Qubit],[Qubit],Qubit)
    q_add_aux [] [] c = return ([],[],c)
    q_add_aux [x0] [y0] c = do
      y0 <- qnot y0 `controlled` x0
      y0 <- qnot y0 `controlled` c
      return ([x0],[y0],c)
    q_add_aux (x0:xs) (y0:ys) c = do
      y0 <- qnot y0 `controlled` x0
      y0 <- qnot y0 `controlled` c
      ((x0,y0,c),(xs,ys)) <- with_computed_fun (x0,y0,c)
        (\(x0,y0,c) -> do
          c' <- qinit False
          c' <- qnot c' `controlled` (x0 .==. 1) .&&. (y0 .==. 0)
          c' <- qnot c' `controlled` (x0 .==. 1) .&&. (c .==. 1)
          c' <- qnot c' `controlled` (y0 .==. 0) .&&. (c .==. 1)
          return (x0,y0,c,c'))
        
        (\(x0,y0,c,c') -> do
          (xs,ys,c') <- q_add_aux xs ys c'
          return ((x0,y0,c,c'),(xs,ys)))
      return (x0:xs,y0:ys,c)
    q_add_aux _ _ _ = error "q_add_in_place: cannot add integers of different sizes."

-- | Subtract one 'QDInt' from a second, in place; i.e. (/x/,/y/) ↦ (/x/,/y/–/x/).  Arguments are assumed to be of equal size.  /O/(ℓ) gates.
q_sub_in_place :: QDInt -> QDInt -> Circ (QDInt,QDInt)
q_sub_in_place x y = reverse_generic_endo (\(x,d) -> q_add_in_place x d) (x,y)

-- | Low-level version of 'q_sub_in_place': represents integers
-- as big-headian qubit lists.
q_sub_in_place_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit],[Qubit])
q_sub_in_place_qulist x y = reverse_generic_endo (\(x,d) -> q_add_in_place_qulist x d) (x,y)

-- ----------------------------------------------------------------------
-- ** Arithmetic with parameters

-- | Add a parameter 'IntM' and a 'QDInt', into a fresh 'QDInt': (/x/, /y/) ↦ (/y/, /x/+/y/).  The parameter /x/ must be of the same length as /y/, or /x/ can also be of undetermined length.  /O/(ℓ).
q_add_param :: IntM -> QDInt -> Circ (QDInt,QDInt)
q_add_param x1 y = do
  let x = intm_promote x1 y "q_add_param: inputs must have equal length"
  let x' = boollist_of_intm_bh x
  let y' = list_of_xint_bh y
  (y', z') <- q_add_param_qulist x' y'
  let y = xint_of_list_bh y'
  let z = xint_of_list_bh z'
  return (y, z)
  
-- | Low-level implementation of 'q_add_param': represents integers as
-- big-headian qubit lists. Precondition: /x/ and /y/ have the same length.
q_add_param_qulist :: [Bool] -> [Qubit] -> Circ ([Qubit], [Qubit])
q_add_param_qulist x y = do 
  -- Implementation note: compare with q_add_qdint.  The code is almost verbatim identical, but since x consists of parameter Bools, `controlled` will omit gates when appropriate.

  -- Further slight optimisation would be possible, since if x doesn’t have low bits then no low carry qubits are required. 

  -- Implementation note: once we have a general-purpose classical
  -- circuit optimizer (even a primitive one), then this kind of
  -- source-code level optimization will hopefully become moot.
  
  let l = length x

  (y,s_out) <- with_computed_fun y
    (\y -> do
      s <- qinit (replicate l False) -- holds the eventual sum
      c <- qinit (replicate l False) -- holds the carries

      -- bring the lists’ indexing in line with usual numeric indexing of binary expansons
      x <- return $ reverse x
      y <- return $ reverse y
      s <- return $ reverse s
      c <- return $ reverse c

      (y,s,c) <- loop_with_indexM (l-1) (y,s,c) (\j (y,s,c) -> do
        let c_j1 = c !! (j+1)
        let s_j = s !! j
        -- If any two of the current bits x_j, y_j, and the carry c_j are true, then set the next carry:
        -- (Note: we use that (a & b) xor (a & c) xor (b & c) == (a & b) or (a & c) or (b & c).)
        c_j1 <- qnot c_j1 `controlled` (x!!j .&&. y!!j)
        c_j1 <- qnot c_j1 `controlled` (x!!j .&&. c!!j)
        c_j1 <- qnot c_j1 `controlled` (y!!j .&&. c!!j)
        -- Now the current sum digit is computed mod 2:
        s_j <- qnot s_j `controlled` (x!!j)
        s_j <- qnot s_j `controlled` (y!!j)
        s_j <- qnot s_j `controlled` (c!!j) 
        c <- return $ overwriteAt (j+1) c_j1 c
        s <- return $ overwriteAt j s_j s

        return (y,s,c))

      -- Final sum digit; no carry required:
      let s_l1 = s !! (l-1)
      s_l1 <- qnot s_l1 `controlled` (x!!(l-1))
      s_l1 <- qnot s_l1 `controlled` (y!!(l-1))
      s_l1 <- qnot s_l1 `controlled` (c!!(l-1)) 
      s <- return $ overwriteAt (l-1) s_l1 s
     
      x <- return $ reverse x
      y <- return $ reverse y
      s <- return $ reverse s
      c <- return $ reverse c

      return (y,s,c))
    
    (\(y,s,c) -> do
      (s,s_out) <- qc_copy_fun s
      return ((y,s,c), s_out))
  return (y, s_out)

-- | Subtract a parameter 'IntM' from a 'QDInt', into a fresh 'QDInt'.  The 'IntM' cannot be shorter than the 'QDInt' (that would give ill-defined behavior), but can be of undetermined length.  /O/(ℓ).
q_sub_param :: IntM -> QDInt -> Circ (QDInt,QDInt)
q_sub_param x y = q_add_param (-x) y

-- | Add a parameter 'IntM' onto a 'QDInt', in place; i.e. (/x/,/y/) ↦ /x/+/y/. The parameter /x/ must be of the same length as /y/, or /x/ can also be of undetermined length.  /O/(ℓ).
q_add_param_in_place :: IntM -> QDInt -> Circ QDInt
q_add_param_in_place x1 y = do
  let x = intm_promote x1 y "q_add_param_in_place: inputs must have equal length"
  let x' = boollist_of_intm_bh x
  let y' = list_of_xint_bh y
  y' <- q_add_param_in_place_qulist x' y'
  let y = xint_of_list_bh y'
  return y

-- | Low-level implementation of 'q_add_param_in_place': represents
-- integers as big-headian qubit lists. Precondition: /xlist/ and /y/
-- have the same length. Precondition: /x/ and /y/ have the same length.
q_add_param_in_place_qulist :: [Bool] -> [Qubit] -> Circ [Qubit]
q_add_param_in_place_qulist [] [] = return []
q_add_param_in_place_qulist [False] [y0] = return [y0]
q_add_param_in_place_qulist [True] [y0] = do
  y0 <- qnot y0
  return [y0]
q_add_param_in_place_qulist x y = do
  let l = length x

  let (x0:x_higher) = reverse x  
      (y0:y_higher) = reverse y

  y0 <- qnot y0 `controlled` x0

  (y0,y_higher) <- with_computed_fun y0
    (\y0 -> do
      c <- qinit False
      c <- qnot c `controlled` (x0 == 1) .&&. (y0 .==. 0)
      return (y0,c))
    (\(y0,c) -> do
      (y_higher,c) <- q_add_aux x_higher y_higher c
      return ((y0,c),y_higher))
  return (reverse (y0:y_higher))
  where
  -- Aux: add two LITTLE-endian bit strings, and an optional extra 1.
    q_add_aux :: [Bool] -> [Qubit] -> Qubit -> Circ ([Qubit],Qubit)
    q_add_aux [] [] c = return ([],c)
    q_add_aux [x0] [y0] c = do
      y0 <- qnot y0 `controlled` x0
      y0 <- qnot y0 `controlled` c
      return ([y0],c)
    q_add_aux (x0:xs) (y0:ys) c = do
      y0 <- qnot y0 `controlled` x0
      y0 <- qnot y0 `controlled` c
      ((y0,c),ys) <- with_computed_fun (y0,c)
        (\(y0,c) -> do
          c' <- qinit False
          c' <- qnot c' `controlled` (x0 == 1) .&&. (y0 .==. 0)
          c' <- qnot c' `controlled` (x0 == 1) .&&. (c .==. 1)
          c' <- qnot c' `controlled` (y0 .==. 0) .&&. (c .==. 1)
          return (y0,c,c'))
        
        (\(y0,c,c') -> do
          (ys,c') <- q_add_aux xs ys c'
          return ((y0,c,c'),ys))
      return (y0:ys,c)
    q_add_aux _ _ _ = error "q_add_in_place: cannot add integers of different sizes."

-- | Subtract a parameter 'IntM' from a 'QDInt', in place; i.e. (/x/,/y/) ↦ (/x/,/x/-/y/).  /x/ cannot be shorter than /y/.  /O/(/l/) gates.
q_sub_param_in_place :: IntM -> QDInt -> Circ QDInt
q_sub_param_in_place x = q_add_param_in_place (-x)

-- | Multiply a parameter 'IntM' by a 'QDInt', into a fresh 'QDInt'.  The 'IntM' cannot be shorter than the 'QDInt' (that would give ill-defined behavior), but can be of undetermined length.  /O/(ℓ).
q_mult_param :: IntM -> QDInt -> Circ (QDInt,QDInt)
q_mult_param x1 y = do
  let x = intm_promote x1 y "q_add_param: inputs must have equal length"
  let x' = boollist_of_intm_bh x
  let y' = list_of_xint_bh y
  (y', z') <- q_mult_param_qulist x' y'
  let y = xint_of_list_bh y'
  let z = xint_of_list_bh z'
  return (y, z)

-- | Low-level implementation of 'q_mult_param': represents integers as
-- big-headian (qu)bit lists.
q_mult_param_qulist :: [Bool] -> [Qubit] -> Circ ([Qubit],[Qubit])
q_mult_param_qulist [] [] = return ([], [])
q_mult_param_qulist xs ys = do
  let x0 = last xs 
      x_higher = init xs
      y_high = head ys
      y_lower = tail ys
  (y_lower, p_higher)
    <- q_mult_param_qulist x_higher y_lower
  p0 <- qinit False
  let y = y_high:y_lower
      p = p_higher ++ [p0]
  -- Once we have some optimisation, the following line should be replaced by:
  -- (y,p) <- q_add_in_place_qulist y p `controlled` x0
  (y,p) <- if x0 then q_add_in_place_qulist y p else return (y,p)
  return (y, p)  

-- ----------------------------------------------------------------------
-- ** Sign and negation

-- | Negate a (signed) 'QDInt' in place. /O/(ℓ).
q_negate_in_place :: QDInt -> Circ QDInt
q_negate_in_place x = do
  x <- mapUnary qnot x
  x <- q_increment x
  return x

-- | Low-level version of 'q_negate_in_place': represents integers as
-- big-headian qubit lists.
q_negate_in_place_qulist :: [Qubit] -> Circ [Qubit]
q_negate_in_place_qulist = mmap list_of_xint_bh . q_negate_in_place . xint_of_list_bh

-- | Compute the negation of a (signed) 'QDInt'. /O/(ℓ).
-- 
-- (Fixes the minimum value, consistently with Haskell’s @'negate' 'minBound' :: 'Int'@.) 
q_negate_qdint :: QDInt -> Circ (QDInt,QDInt)
q_negate_qdint x = do
  (x,nx) <- qc_copy_fun x
  nx <- q_negate_in_place nx
  return (x,nx)

-- | Compute the absolute value of a (signed) 'QDInt'.  /O/(ℓ).
-- 
-- (Fixes the minimum value, consistently with Haskell’s @'abs' 'minBound' :: 'Int'@.) 
q_abs_qdint :: QDInt -> Circ (QDInt,QDInt)
q_abs_qdint x = do
  let x' = list_of_xint_bh x
  (x', a') <- q_abs_qulist x'
  let x = xint_of_list_bh x'
  let a = xint_of_list_bh a'
  return (x, a)

-- | Low-level implementation of 'q_abs_qdint': represents integers as
-- big-headian qubit lists.
q_abs_qulist :: [Qubit] -> Circ ([Qubit],[Qubit])
q_abs_qulist [] = return ([], [])
q_abs_qulist (x_high:x_lower) = do
  a_high <- qinit False
  (x_lower,a_lower) <- qc_copy_fun x_lower
  a_lower <- mapUnary qnot a_lower `controlled` x_high
  let a = a_high:a_lower
  a <- q_increment_qulist a `controlled` x_high
  return (x_high:x_lower, a)

-- | Compute a 'QDInt' of the same length as the input, with value 1, 0, or –1, depending on the sign of the input.  Analogous to Haskell’s 'signum'.  /O/(ℓ).
q_signum_qdint :: QDInt -> Circ (QDInt,QDInt)
q_signum_qdint x = do
  let x' = list_of_xint_bh x
  (x', a') <- q_signum_qulist x'
  let x = xint_of_list_bh x'
  let a = xint_of_list_bh a'
  return (x, a)

-- | Low-level implementation of 'q_abs_qdint': represents integers as
-- big-headian qubit lists.
q_signum_qulist :: [Qubit] -> Circ ([Qubit],[Qubit])
q_signum_qulist [] = return ([], [])
q_signum_qulist x = do
  let l = length x
  (s_higher, s_low) <- qinit (replicate (l-1) False, False)
  -- first set s = 1
  s_low <- qnot s_low
  -- case x < 0: set s to -1 
  s_higher <- mapUnary qnot s_higher `controlled` (head x)
  -- case x = 0: reset s to 0
  s_low <- qnot s_low `controlled` (x .==. replicate l 0)
  return (x,s_higher ++ [s_low])

-- ----------------------------------------------------------------------
-- ** Comparison

-- | Comparison of two 'QDInt's, considered as unsigned.  /O/(ℓ).
q_le_unsigned :: QDInt -> QDInt -> Circ (QDInt,QDInt,Qubit)
q_le_unsigned x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (x',y',le_out) <- q_le_unsigned_qulist x' y'
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  return (x,y,le_out)

-- | Low-level implementation of 'q_le_unsigned': represents integers
-- as big-headian qubit lists.
q_le_unsigned_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit],[Qubit],Qubit)
q_le_unsigned_qulist x y = do
  ((x,y),le_out) <- with_computed_fun (x,y) q_le_unsigned_aux
    (\(x,y,(le:garbage)) -> do
      (le,le_out) <- qc_copy_fun le
      return ((x,y,(le:garbage)),le_out))
  return (x,y,le_out)

-- | Same as 'q_le_unsigned', but uncurried, represents integers as
-- big-headian qubit lists, and doesn’t clean up its garbage.  (If
-- each recursive call cleans up its own garbage, gate use becomes
-- /O/(2[sup /n/]).)
q_le_unsigned_aux :: ([Qubit], [Qubit]) -> Circ ([Qubit],[Qubit],[Qubit])
q_le_unsigned_aux ([], []) = do q <- qinit True; return ([], [], [q])
q_le_unsigned_aux (x_high:x_lower, y_high:y_lower) = do
  -- Classically, one would make the recursive call only if needed; but quantumly, it’s cheaper to do it unconditionally. 
  (x_lower, y_lower, le_lower:garbage) <- q_le_unsigned_aux (x_lower, y_lower)
  (x_high,y_high,eq_high) <- q_is_equal x_high y_high
  le <- qinit False
  le <- qnot le `controlled` (x_high .==. 0) .&&. (y_high .==. 1)
  le <- qnot le `controlled` eq_high .&&. le_lower
  return (x_high:x_lower, y_high:y_lower, le:eq_high:le_lower:garbage)
q_le_unsigned_aux _ = error "q_le // QDInt: cannot compare QDInt’s of different lengths."

-- | Comparison of two 'QDInt's, considered as signed.  Used in @instance 'QOrd' 'QDInt'@.  /O/(ℓ).
q_le_signed :: QDInt -> QDInt -> Circ (QDInt,QDInt,Qubit)
q_le_signed x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (x',y',le_out) <- q_le_signed_qulist x' y'
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  return (x,y,le_out)

-- | Low-level implementation of 'q_le_signed': represents integers
-- as big-headian qubit lists.

-- Implementation note: defined in terms of q_le_unsigned_aux
q_le_signed_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit],[Qubit],Qubit)
q_le_signed_qulist [] [] = do q <- qinit True; return ([], [], q)
q_le_signed_qulist (x_high:x_lower) (y_high:y_lower) = do
  ((x,y), x_le_y) <- with_computed_fun (x_high:x_lower, y_high:y_lower)
    (\(x_high:x_lower, y_high:y_lower) -> do 
  -- Classically, one would make the recursive call only if needed; but quantumly, it’s cheaper to do it unconditionally. 
      (x_lower, y_lower, le_lower:garbage) <- q_le_unsigned_aux (x_lower, y_lower)
      (x_high,y_high,eq_high) <- q_is_equal x_high y_high
      return (x_high, y_high, x_lower, y_lower, le_lower, eq_high, garbage))
    (\(x_high, y_high, x_lower, y_lower, le_lower, eq_high, garbage) -> do
      le <- qinit False
      le <- qnot le `controlled` (x_high .==. 1) .&&. (y_high .==. 0)
      le <- qnot le `controlled` eq_high .&&. le_lower
      return ((x_high, y_high, x_lower, y_lower, le_lower, eq_high, garbage), le))
  return (x,y,x_le_y)
q_le_signed_qulist _ _ = error "q_le // QDInt: cannot compare QDInt’s of different lengths."

-- | Comparison of two 'QDInt's, considered as signed.  Used in @instance 'QOrd' 'QDInt'@. /O/(ℓ).
q_lt_signed :: QDInt -> QDInt -> Circ (QDInt,QDInt,Qubit)
q_lt_signed x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (y',x',y_le_x) <- q_le_signed_qulist y' x'
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  x_lt_y <- qnot y_le_x
  return (x,y,x_lt_y)

-- | Text whether a 'QDInt' is nonnegative.   /O/(1)
q_negative :: QDInt -> Circ (QDInt,Qubit)
q_negative x = do
  let (x_high:x_lower) = list_of_xint_bh x
  (x_high,x_neg) <- qc_copy_fun x_high
  return (xint_of_list_bh (x_high:x_lower),x_neg)

instance QOrd QDInt where
  q_less qx qy = do (qx,qy,q) <- q_lt_signed qx qy; return q
  q_leq qx qy = do (qx,qy,q) <- q_le_signed qx qy; return q

-- ----------------------------------------------------------------------
-- ** Multiplication

-- | Multiply two 'QDInt's into a fresh third.  Arguments are assumed to be of equal size.  /O/(ℓ[sup 2]).
q_mult_qdint :: QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt)
q_mult_qdint x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (x', y', z') <- q_mult_qulist x' y'
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  let z = xint_of_list_bh z'
  return (x, y, z)

-- | Low-level implementation of 'q_mult_qdint': represents integers as
-- big-headian qubit lists.
q_mult_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit],[Qubit],[Qubit])
q_mult_qulist [] [] = return ([], [], [])
q_mult_qulist xs ys = do
  let x0 = last xs 
      x_higher = init xs
      y_high = head ys
      y_lower = tail ys
  (x_higher, y_lower, p_higher)
    <- q_mult_qulist x_higher y_lower
  p0 <- qinit False
  let y = y_high:y_lower
      p = p_higher ++ [p0]
  (y,p) <- q_add_in_place_qulist y p `controlled` x0
  return (x_higher ++ [x0], y, p)

-- ----------------------------------------------------------------------
-- ** Division and remainder

-- | Reduce one 'QDInt' modulo another, in place, returning also the
-- integer quotient, i.e. (/x/, /y/) ↦ (/x/ mod /y/, /y/, /x/ div /y/).
-- All inputs and outputs are considered unsigned.  Inputs are assumed
-- to have the same length.  Division by zero returns (/x/,0,-1).
-- 
-- /O/(ℓ[sup 2]) gates, /O/(ℓ) qubits.
q_moddiv_unsigned_in_place :: QDInt -> QDInt -> Circ (QDInt, QDInt,QDInt)
q_moddiv_unsigned_in_place x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (r', y', q') <- q_moddiv_unsigned_in_place_qulist x' y'
  let r = xint_of_list_bh r'
  let y = xint_of_list_bh y'
  let q = xint_of_list_bh q'
  return (r, y, q)

-- | Low-level implementation of 'q_moddiv_unsigned_in_place':
-- represents integers as big-headian qubit lists.
-- 
-- Implementation note: this algorithm can be optimized significantly:
-- [scratch] is always 0, so can be optimized away.  This optimisation
-- is much clearer at the circuit level than the code level, however,
-- so is deferred for now.
q_moddiv_unsigned_in_place_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit], [Qubit],[Qubit])
q_moddiv_unsigned_in_place_qulist x y = do
  let l = common_value "q_divrem_unsigned_in_place: arguments must be same length" $ map length [x,y]
  -- Set quot = 0, rem = x.  At each stage, we will have y * quot + rem = x.
  quot_bits <- qinit (replicate l False)
  let rem = x
  with_ancilla_init (replicate (l-1) False) (\scratch -> do
    -- For j from (l-1) to 0, compute the jth bit of the quotient, and update the remainder 
    (y,scratch,quot_bits,rem) <- loop_with_indexM l (y,scratch,quot_bits,rem)
      (\i (y,scratch,quot_bits,rem) -> do
        let j = l-1-i
        -- Getting y*(2^j) requires no quantum operations, just formal re-bracketing of the data:
        let y_init = take j y
            y_2j = (drop j y) ++ (take j scratch)
            scratch_tail = drop j scratch
        -- Compare (2^j) y with rem.  If (2^j)y <= rem, then subtract (2^j)y from rem and flip the jth bit of quot.
        ((y_init,y_2j,rem,quot_bits),()) <- with_computed_fun 
          (y_init,y_2j,rem,quot_bits)
          (\(y_init,y_2j,rem,quot_bits) -> do
            -- first, test that (2^j)y has not overflowed the register, i.e. that y_init is still all 0;
            le1 <- qinit False
            le1 <- qnot le1 `controlled` (y_init .==. replicate (length y_init) False)
            -- next, test that (2^j)y <= rem (this will be correct if (2^j)y has not overflowed yet);
            (y_2j,rem,le2) <- q_le_unsigned_qulist y_2j rem
            return (y_init,y_2j,rem,quot_bits,le1,le2))
          (\(y_init,y_2j,rem,quot_bits,le1,le2) -> do
            -- flip jth bit of quot, if appropriate
            -- (leave rem unchanged for now, since it’s needed to uncompute le1)
            q_j <- qnot (quot_bits !! (l-1-j)) `controlled` le1 .&&. le2
            return ((y_init,y_2j,rem,(overwriteAt (l-1-j) q_j quot_bits),le1,le2),()))
        -- now, subtract (2^j) from rem, if appropriate.
        (y_2j,rem) <- q_sub_in_place_qulist y_2j rem `controlled` quot_bits !! (l-1-j)
        -- Finally, undo the formal re-bracketing:
        let y = y_init ++ (take (l-j) y_2j)
            scratch = (drop (l-j) y_2j) ++ scratch_tail
        return (y,scratch,quot_bits,rem))
    return (rem, y, quot_bits))

-- | Reduce one 'QDInt' modulo another, i.e. (/x/, /y/) ↦ (/x/, /y/, /x/ mod /y/).
-- All inputs and outputs are considered unsigned.  Inputs are assumed
-- to have the same length.  If /y/ = 0, returns (/x/,0,/x/).
-- 
-- /O/(ℓ[sup 2]) gates, /O/(ℓ) qubits.
q_mod_unsigned :: QDInt -> QDInt -> Circ (QDInt, QDInt,QDInt)
q_mod_unsigned x y = do
  ((x,y),x_mod_y) <- with_computed_fun (x,y)
    (\(x,y) -> q_moddiv_unsigned_in_place x y)
    (\(x_mod_y, y, x_div_y) -> do
      (x_mod_y, x_mod_y_out) <- qc_copy_fun x_mod_y
      return ((x_mod_y, y, x_div_y), x_mod_y_out))
  return (x,y,x_mod_y)

-- | Integer division of two 'QDInt's, returning the quotient and remainder,
-- i.e. (/x/,/y/) ↦ (/x/,/y/,/x/ div /y/,/x/ mod /y/). 
-- All inputs and outputs are considered unsigned.
-- Inputs are assumed to have the same length.
-- Division by zero returns (-1,/x/).
--
-- /O/(ℓ[sup 2]) gates, /O/(ℓ) qubits.
q_divrem_unsigned :: QDInt -> QDInt -> Circ (QDInt, QDInt,QDInt,QDInt)
q_divrem_unsigned x y = do
  (x,rem) <- qc_copy_fun x
  (rem,y,quot) <- q_moddiv_unsigned_in_place rem y
  return (x,y,quot,rem)

-- | Integer division of two 'QDInt's, returning just the quotient.  
-- All inputs/outputs considered unsigned.
-- Inputs are assumed to have the same length.
-- Division by zero returns –1.
-- 
-- /O/(ℓ[sup 2]) gates, /O/(ℓ) qubits.

-- Implementation note: We use a multiplication to do the
-- uncomputation of the remainder, because this uses fewer total gates
-- than uncomputing divrem would.
q_div_unsigned :: QDInt -> QDInt -> Circ (QDInt, QDInt,QDInt)
q_div_unsigned x y = do
  (x,y,quot,rem) <- q_divrem_unsigned x y
  ((x,y,quot),()) <- with_computed_fun (x,y,quot) 
    (\(x,y,quot) -> do
      (y,quot,y_quot) <- q_mult y quot
      (x,y_quot,rem_copy) <- q_sub x y_quot
      return (x,y,quot,y_quot,rem_copy))
    (\(x,y,quot,y_quot,rem_copy) -> do
      rem_copy <- qc_uncopy_fun rem_copy rem
      return ((x,y,quot,y_quot,rem_copy),()))
  return (x,y,quot)

-- | Low-level version of 'q_div_unsigned': represents integers as
-- big-headian qubit lists.
q_div_unsigned_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit], [Qubit], [Qubit])
q_div_unsigned_qulist x' y' = do
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  (x, y, q) <- q_div_unsigned x y            
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  let q' = list_of_xint_bh q
  return (x', y', q')

-- | Integer division of two 'QDInt's into a fresh third, rounding towards –∞. 
-- The first argument is the numerator, and is assumed to be signed.
-- The second argument is the denominator, and is assumed to be unsigned.
-- The output is signed.
-- Inputs are assumed to have the same length.
-- 
-- /O/(ℓ[sup 2]) gates, /O/(ℓ) qubits.
q_div :: QDInt -> QDInt -> Circ (QDInt, QDInt, QDInt)
q_div x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (x', y', q') <- q_div_qulist x' y'            
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  let q = xint_of_list_bh q'
  return (x, y, q)

-- | Low-level implementation of 'q_div': represents integers as
-- big-headian qubit lists.
q_div_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit], [Qubit], [Qubit])
q_div_qulist [] [] = return ([], [], [])
q_div_qulist (x_high:x_lower) y = do
  -- Writing x/y for unsigned division, we have x `div` y = 
  -- if x>0 then x/y else ~((~x)/y)
  -- where ~x := -1-x --- i.e. the bitflip of x.
  --
  -- We do this with an ancilla (which can easily be optimized away): 
  with_ancilla_init False (\fake_x_high -> do
    -- flip x if x<0:
    x_lower <- mapUnary qnot x_lower `controlled` x_high
    let x' = fake_x_high:x_lower
    -- x' now holds (if x > 0 then x else ~x) 
    (x',y,quot) <- q_div_unsigned_qulist x' y
    -- restore x and flip quotient, if necessary
    let fake_x_high:x_lower = x'
    x_lower <- mapUnary qnot x_lower `controlled` x_high
    quot <-  mapUnary qnot quot `controlled` x_high
    return (x_high:x_lower, y, quot))
q_div_qulist _ _ = error "q_div: arguments must have same length."

-- | Integer division of two 'QDInt's into a fresh third, rounding towards 0. 
-- The first argument is the numerator, and is assumed to be signed.
-- The second argument is the denominator, and is assumed to be unsigned.
-- The output is signed.
-- Inputs are assumed to have the same length.
-- 
-- /O/(ℓ[sup 2]) gates, /O/(ℓ) qubits.
q_quot :: QDInt -> QDInt -> Circ (QDInt, QDInt, QDInt)
q_quot x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (x', y', q') <- q_quot_qulist x' y'            
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  let q = xint_of_list_bh q'
  return (x, y, q)

-- | Low-level implementation of 'q_quot': represents integers as
-- big-headian qubit lists.
q_quot_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit], [Qubit], [Qubit])
q_quot_qulist [] [] = return ([], [], [])
q_quot_qulist (x_high:x_lower) y = do
  -- Writing x/y for unsigned division, we have x `div` y = 
  -- if x>0 then x/y else -((-x)/y)
  --
  -- We do this with an ancilla (which can easily be optimized away): 
  with_ancilla_init False (\fake_x_high -> do
    -- flip x if x<0:
    x_lower <- q_negate_in_place_qulist x_lower `controlled` x_high
    let x' = fake_x_high:x_lower
    -- x' now holds (if x > 0 then x else ~x) 
    (x',y,quot) <- q_div_unsigned_qulist x' y
    -- restore x and flip quotient, if necessary
    let fake_x_high:x_lower = x'
    x_lower <- q_negate_in_place_qulist x_lower `controlled` x_high
    quot <- q_negate_in_place_qulist quot `controlled` x_high
    return (x_high:x_lower, y, quot))
q_quot_qulist _ _ = error "q_quot: arguments must have same length."

-- | Integer division of two 'QDInt's, returning the quotient,
-- assuming that the second exactly divides the first and throwing an error otherwise.  
-- All inputs/outputs considered unsigned.
-- Inputs are assumed to have the same length.
-- 
-- /O/(ℓ[sup 2]) gates, /O/(ℓ) qubits.
q_div_exact_unsigned :: QDInt -> QDInt -> Circ (QDInt, QDInt,QDInt)
q_div_exact_unsigned x y = do
  (x,y,quot,rem) <- q_divrem_unsigned x y
  qterm 0 rem
  return (x,y,quot)

-- | Integer division of two 'QDInt's, returning the quotient,
-- assuming that the second exactly divides the first.  
-- The first argument is the numerator, considered signed.
-- The second argument is the denominator, considered unsigned.
-- The output is signed.
-- 
-- /O/(ℓ[sup 2]) gates, /O/(ℓ) qubits.
q_div_exact :: QDInt -> QDInt -> Circ (QDInt, QDInt,QDInt)
q_div_exact x y = do
  (x,(y,quot)) <- with_computed_fun x
    (\x -> do
      (x,x_neg) <- q_negative x
      x' <- q_negate_in_place x `controlled` x_neg
      return (x',x_neg))
    (\(x',x_neg) -> do
      (x',y,quot) <- q_div_exact_unsigned x' y
      quot <- q_negate_in_place quot `controlled` x_neg
      return ((x',x_neg),(y,quot)))
  return (x,y,quot)

-- ----------------------------------------------------------------------
-- * The QNum type class

-- $ This section defines a quantum analogue of Haskell’s 'Num' type
-- class.  See "Quipper.QClasses" for the general philosophy behind
-- quantum type classes.
-- 
-- The type class 'QNum' corresponds to Haskell’s 'Num', with methods
-- including 
-- 
-- > add_q :: (QNum qa) => qa -> qa -> Circ (qa,qa,qa), 
-- 
-- and so on.
-- 
-- Note: type class instances don't show up in the documentation. View
-- the source code to see them.

-- | Quantum analogue of Haskell’s 'Num' type class. This provides
-- basic addition, subtraction, multiplication, sign operations, and
-- conversion from integers.

class (QData qa) => QNum qa where
  -- | Add two quantum numbers into a fresh one. The arguments are
  -- assumed to be of equal size. The 'QDInt' instance uses /O/(ℓ)
  -- gates, both before and after transformation to Toffoli.
  q_add :: qa -> qa -> Circ (qa,qa,qa)
  
  -- | Multiply two quantum numbers into a fresh third. The arguments
  -- are assumed to be of equal size.  The 'QDInt' instance is
  -- /O/(ℓ[sup 2]).
  q_mult :: qa -> qa -> Circ (qa,qa,qa)
  
  -- | Subtract two quantum numbers into a fresh one. The arguments
  -- are assumed to be of equal size. The 'QDInt' instance uses /O/(ℓ)
  -- gates, both before and after transformation to Toffoli.
  q_sub :: qa -> qa -> Circ (qa,qa,qa)
  
  -- | Compute the absolute value of a (signed) quantum number. The
  -- 'QDInt' instance is /O/(ℓ).
  q_abs :: qa -> Circ (qa,qa)
  
  -- | Compute the negation of a (signed) quantum number. The 'QDInt'
  -- instance is /O/(ℓ).
  q_negate :: qa -> Circ (qa,qa)
  
  -- | Compute a quantum number of the same precision as the input,
  -- with value 1, 0, or –1, depending on the sign of the
  -- input. Analogous to Haskell’s 'signum'. The 'QDInt' instance is
  -- /O/(ℓ).
  q_signum :: qa -> Circ (qa,qa)
  
  -- | Convert a 'QDInt' to a quantum number. For the 'QDInt'
  -- instance, this is just a copy operation.
  q_fromQDInt :: QDInt -> Circ (QDInt,qa)
   
instance QNum QDInt where
  q_add = q_add_qdint
  q_mult = q_mult_qdint
  q_sub = q_sub_qdint
  q_abs = q_abs_qdint
  q_negate = q_negate_qdint
  q_signum = q_signum_qdint
  q_fromQDInt = qc_copy_fun

-- ----------------------------------------------------------------------
-- ** Specialized functions

-- | Euclid's extended algorithm. 'q_ext_euclid' /a/ /b/: returns
-- (/a/,/b/,/x/,/y/,/d/) such that /ax/ + /by/ = /d/ = gcd(/a/,/b/).
q_ext_euclid :: QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt,QDInt,QDInt)
q_ext_euclid a b = do
  let l = common_length "q_ext_euclid: inputs must have equal length" [a,b]

  -- Extended Euclidean algorithm:
  --
  -- compute three series of numbers (a_i), (x_i), (y_i), such that
  --
  -- a_0 = a, a_1 = b,
  -- a_{i+2} = a_i `mod` a_{i+1},
  -- and always a_i = (x_i * a) + (y_i * b),
  --
  -- When we first get a_{i+2} = 0, we know that a_{i+1} is gcd(a_0,a_1),
  -- so we save a_{i+1}, x_{i+1} and y_{i+1} for output.
  --
  -- The bound on the length of this loop is standard.

  ((a,b),(x,y)) <- with_computed_fun (a,b) (\(a,b) -> do
    x0 <- qinit (intm l 1)
    y0 <- qinit (intm l 0)
    x1 <- qinit (intm l 0)
    y1 <- qinit (intm l 1)
    done_yet <- qinit False
    x_final <- qinit (intm l 0)
    y_final <- qinit (intm l 0)

    (stuff1, stuff2, stuff3, (done_yet, x_final, y_final))
            <- loopM (euclid_bound l) ((a,b,x0,x1,y0,y1),[],[],(done_yet,x_final,y_final))
      (\((a_i, a_i1, x_i, x_i1, y_i, y_i1), quots_scratch, tests_scratch, (done_yet, x_final, y_final)) -> do
        (a_i2, a_i1, q_i) <- q_moddiv_unsigned_in_place a_i a_i1
        ((x_i1, y_i1, q_i), (x_i2, y_i2)) <- with_computed_fun
          (x_i1, y_i1, q_i)
          (\(x_i1, y_i1, q_i) -> do
            (q_i, x_i1, qx) <- q_mult q_i x_i1
            (q_i, y_i1, qy) <- q_mult q_i y_i1
            return (x_i1, y_i1, q_i, qx, qy))
          (\(x_i1, y_i1, q_i, qx, qy) -> do
            (qx,x_i2) <- q_sub_in_place qx x_i
            (qy,y_i2) <- q_sub_in_place qy y_i
            return ((x_i1, y_i1, q_i, qx, qy),(x_i2,y_i2)))
        done_this_time <- qinit False
        done_this_time <- qnot done_this_time `controlled` (a_i2 .==. 0) .&&. (done_yet .==. False)
        (x_i1,x_final) <- controlled_not x_final x_i1 `controlled` done_this_time
        (y_i1,y_final) <- controlled_not y_final y_i1 `controlled` done_this_time
        done_yet <- qnot done_yet `controlled` done_this_time
        return ((a_i1, a_i2, x_i1, x_i2, y_i1, y_i2),
                (q_i:quots_scratch), (done_this_time:tests_scratch), 
                (done_yet, x_final, y_final)))
    qterm True done_yet -- Assert that we really did reach the end of the algorithm. 
    return (x_final,y_final,(stuff1, stuff2, stuff3)))

    (\(x_final, y_final, stuff) -> do
      (x_final,x) <- qc_copy_fun x_final
      (y_final,y) <- qc_copy_fun y_final
      return ((x_final, y_final, stuff),(x,y)))

  ((a,b,x,y),gcd) <- with_computed_fun
    (a,b,x,y)
    (\(a,b,x,y) -> do
      (a,x,ax) <- q_mult a x
      (b,y,by) <- q_mult b y
      return (a,b,x,y,ax,by))
    (\(a,b,x,y,ax,by) -> do
      (ax,by,gcd) <- q_add ax by
      return ((a,b,x,y,ax,by),gcd))

  return (a,b,x,y,gcd)

  where
  -- Classical bound on running time (Lamé’s theorem), assuming b < a:
  -- t <= 1 + log_{phi} b <= 1 + l / (log_2 phi)
  --  
  -- We allow one extra step since we may have a < b, in which case first step swaps them.
    euclid_bound :: Int -> Int
    euclid_bound l = 2 + ceiling ( (fromIntegral l) / (logBase 2 phi) )
    phi = (1+sqrt(5))/2

-- ----------------------------------------------------------------------
-- * Lifting of arithmetic functions

-- $LIFTING 
-- This sections provides templates for lifting various arithmetic
-- functions in connection with the @build_circuit@ keyword. This
-- extends the liftings given in "Quipper.CircLifting" to operations
-- of the 'Num' type class.

-- | Quantum lifting of the '+' operator.
template_symb_plus_ :: (QNum qa) => Circ (qa -> Circ (qa -> Circ qa))
template_symb_plus_ = return $ \qx -> return $ \qy -> do (qx,qy,qz) <- q_add qx qy; return qz

-- TODO: complete templates of methods.

