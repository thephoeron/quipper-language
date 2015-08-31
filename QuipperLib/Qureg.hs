-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | This module provides a data type of quantum registers, as well as
-- associated types of classical and boolean registers.

module QuipperLib.Qureg (
  -- * Quantum registers
  Qureg,
  qureg_of_qulist_te,
  qulist_of_qureg_te,
  qureg_length,
  qinit_register,
  qterm_register,
  qmeasure_register,
  with_ancilla_reg,
  with_ancilla_reg_init,
  qureg_shape,
  
  -- * Bit registers
  Bitreg,
  bitreg_of_bitlist_te,
  bitlist_of_bitreg_te,
  bitreg_length,
  
  -- * Boolean registers
  Boolreg,
  boolreg_of_boollist_te,
  boollist_of_boolreg_te,
  boolreg_length,
  boolreg_of_int_le,
  int_of_boolreg_unsigned_le,
              
  -- * General registers
  Register,
  (.!)
  
  ) where

import Quipper
import Quipper.Internal

import Libraries.Auxiliary

import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Data.Typeable

-- ----------------------------------------------------------------------
-- * Quantum registers

-- ** General registers

-- | A register is an array of elements of some type /x/, indexed by
-- natural numbers in the range from 0 to /n/-1, where /n/ is the
-- length of the register.
newtype Register x = Register { unRegister :: IntMap x }
                   deriving (Typeable, Show)

-- | @/r/ !.(/i/)@: Return the /i/th element of a register /r/.
(.!) :: Register x -> Int -> x
a .!(i) = (unRegister a) IntMap.! i

infixl 9  .!   -- same precedence as !!

-- | Convert a list to a register. The conversion is tail-endian,
-- i.e., /r/.!(0) holds the tail of the list.
register_of_list_te :: [x] -> Register x
register_of_list_te l = Register $ IntMap.fromList (zip [n-1, n-2 .. 0] l)
  where n = length l
    
-- | Convert a register to a list. The conversion is tail-endian,
-- i.e., /r/.!(0) holds the tail of the list.
list_of_register_te :: Register x -> [x]
list_of_register_te r = map (r .!) [n-1, n-2 .. 0]
  where n = register_length r

-- | Return the length of a register.
register_length :: Register x -> Int
register_length = IntMap.size . unRegister

-- ----------------------------------------------------------------------
-- ** Qubit registers

-- | The type of quantum registers. A quantum register is an array of
-- qubits, indexed by natural numbers in the range from 0 to /n/-1,
-- where /n/ is the length of the register. The syntax /a/ .!(/i/) is
-- used to access the /i/th element of the register /a/. 
-- 
-- The main advantage of a register over a list is constant-time
-- access. The main disadvantage is that registers don't allow easy
-- appending, pattern matching, or recursion.
type Qureg = Register Qubit

-- | Convert a 'Qulist' to a 'Qureg'. The conversion is tail-endian,
-- i.e., /r/.!(0) holds the tail of the list.
qureg_of_qulist_te :: Qulist -> Qureg
qureg_of_qulist_te = register_of_list_te

-- | Convert a 'Qureg' to a 'Qulist'. The conversion is tail-endian,
-- i.e., /r/.!(0) holds the tail of the list.
qulist_of_qureg_te :: Qureg -> Qulist
qulist_of_qureg_te = list_of_register_te

-- | Return the length of a 'Qureg'. 
qureg_length :: Qureg -> Int
qureg_length = register_length

-- | Return a piece of shape data to represent an /m/-qubit quantum
-- register. Please note that the data can only be used as shape; it
-- will be undefined at the leaves.
qureg_shape :: Int -> Qureg
qureg_shape m = qureg_of_qulist_te (replicate m qubit)

-- ----------------------------------------------------------------------
-- ** Bit registers

-- | The type of 'Bit' registers. The syntax /a/ .!(/i/) is used to
-- access the /i/th element of the register /a/.
type Bitreg = Register Bit

-- | Turn a bit vector into a bit register. The conversion is tail-endian,
-- i.e., /r/.!(0) holds the tail of the list.
bitreg_of_bitlist_te :: Bitlist -> Bitreg
bitreg_of_bitlist_te = register_of_list_te

-- | Turn a bit register into a bit vector. The conversion is tail-endian,
-- i.e., /r/.!(0) holds the tail of the list.
bitlist_of_bitreg_te :: Bitreg -> Bitlist
bitlist_of_bitreg_te = list_of_register_te

-- | Return the length of a 'Bitreg'.
bitreg_length :: Bitreg -> Int
bitreg_length = register_length

-- ----------------------------------------------------------------------
-- ** Boolean registers

-- | The type of boolean registers.
type Boolreg = Register Bool

-- | Turn a bool vector into a bool register. The conversion is tail-endian,
-- i.e., /r/.!(0) holds the tail of the list.
boolreg_of_boollist_te :: Boollist -> Boolreg
boolreg_of_boollist_te = register_of_list_te

-- | Turn a bool register into a bool vector. The conversion is tail-endian,
-- i.e., /r/.!(0) holds the tail of the list.
boollist_of_boolreg_te :: Boolreg -> Boollist
boollist_of_boolreg_te = list_of_register_te

-- | Return the length of a 'Boolreg'.
boolreg_length :: Boolreg -> Int
boolreg_length = register_length

-- ----------------------------------------------------------------------
-- * Special functions for quantum registers

-- | Creates a new quantum register, initialized from a list of
-- booleans. The conversion is tail-endian, i.e., /r/.!(0) holds the
-- tail of the list.
qinit_register :: [Bool] -> Circ Qureg
qinit_register bs = do
  qs <- qinit bs
  return (qureg_of_qulist_te qs)

-- | Terminates a quantum register, and assert that its state is as
-- specified by the list of booleans. The conversion is tail-endian,
-- i.e., /r/.!(0) holds the tail of the list.
qterm_register :: [Bool] -> Qureg -> Circ ()
qterm_register bs r = do
  let qs = qulist_of_qureg_te r
  qterm bs qs
  
-- | Measure a quantum register, yielding a list of 'Bit's. 
qmeasure_register :: Qureg -> Circ [Bit]
qmeasure_register r =
  measure (qulist_of_qureg_te r)
  
-- | Temporarily create a quantum register of size /n/ for use as an
-- ancilla. This can be used to introduce an ancilla with a local scope, like this: 
-- 
-- > with_ancilla_reg n $ \r -> do {
-- >   <<<code block using ancilla register r>>>
-- > }
with_ancilla_reg :: Int -> (Qureg -> Circ a) -> Circ a
with_ancilla_reg n f = do
  let falselist = (take n $ repeat False)
  q <- qinit_register falselist
  a <- f q
  qterm_register falselist q
  return a

-- | Like 'with_ancilla_reg', except also initialize the register as
-- specified by a bit vector. In this case, the argument /n/ is not
-- required, because it equals the length of the bit vector. When the
-- ancilla is terminated at the end of its scope, it is asserted to be
-- in the same state it was prepared in.
with_ancilla_reg_init :: Boollist -> (Qureg -> Circ a) -> Circ a
with_ancilla_reg_init v f = do
  q <- qinit_register v
  a <- f q
  qterm_register v q
  return a

-- ----------------------------------------------------------------------
-- * Special functions for boolean registers

-- | @boolreg_of_int m x@: Initialize a bool register directly from an
-- integer /x/, regarded as a binary string of length /m/. The
-- conversion is little-endian, i.e., the register holds the least
-- significant digit at index 0.
boolreg_of_int_le :: Integral a => Int -> a -> Boolreg
boolreg_of_int_le m x = boolreg_of_boollist_te (boollist_of_int_bh m x)

-- | @int_of_boolreg_unsigned_le m r@: Turn a bool register into an
-- integer, regarded as a binary string. The conversion is
-- little-endian, i.e., the register holds the least significant digit
-- at index 0. The integer is unsigned.
int_of_boolreg_unsigned_le :: Integral a => Boolreg -> a
int_of_boolreg_unsigned_le r = int_of_boollist_unsigned_bh (boollist_of_boolreg_te r)

-- ----------------------------------------------------------------------

-- Make 'Qureg' an instance of 'QData' and 'QCData'.
type instance QCType x y Qureg = Register x
type instance QCType x y Bitreg = Register y
type instance QTypeB Boolreg = Qureg
instance QCData Qureg where
  
  qcdata_mapM shape f g (Register xs) = do
    ys <- intmap_mapM f xs
    return (Register ys)
  
  qcdata_zip shape q c q' c' (Register xs) (Register ys) e = (Register zs) where
    zs = intmap_zip_errmsg xs ys (e "register length mismatch")

  qcdata_promote as xs e
    | register_length as == register_length xs = as
    | otherwise = error (e "register length mismatch")

instance QCData Bitreg where
  
  qcdata_mapM shape f g (Register xs) = do
    ys <- intmap_mapM g xs
    return (Register ys)

  qcdata_zip shape q c q' c' (Register xs) (Register ys) e = (Register zs) where
    zs = intmap_zip_errmsg xs ys (e "register length mismatch")

  qcdata_promote as xs e
    | register_length as == register_length xs = as
    | otherwise = error (e "register length mismatch")

instance Labelable Qureg String where
  label_rec (Register xs) s = do
    sequence_ [ label_rec x s `indexed` show i | (i,x) <- IntMap.toList xs ]

instance Labelable Bitreg String where
  label_rec (Register xs) s = do
    sequence_ [ label_rec x s `indexed` show i | (i,x) <- IntMap.toList xs ]
