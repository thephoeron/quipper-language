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
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A module implementing signed quantum integers. We piggy-back on
-- the type 'IntM', considering it as a type of unsigned quantum
-- integers.
module Algorithms.QLS.QSignedInt where

import Data.Typeable

import Quipper
import Quipper.Internal

import QuipperLib.Arith
import QuipperLib.Simulation

import Algorithms.QLS.Utils
import Algorithms.QLS.QSignedIntAux

import Libraries.Auxiliary

-- ----------------------------------------------------------------------
-- * Signed integer type

-- | Data type for signed integers. Note that this particular variant
-- does not use two's complement to represent negative numbers, but an
-- explicit sign bit. In particular, there are two different
-- representations of 0 (however, the arithmetic operations always
-- produce +0).
-- 
-- This is the generic type, where /x/ represents a bit. An integer is
-- represented as 'Sint' /digits/ /sign/, where /digits/ is a
-- big-headian list of digits (i.e., the most significant bit occupies
-- the head of the list), and /sign/ is the sign, with 'False'
-- representing plus and 'True' representing minus.
-- 
-- When we speak of the \"length\" of a 'SignedInt', we mean the
-- number of digits excluding the sign.
data SignedInt x = SInt [x] x
   deriving (Show, Typeable)

-- | The parameter type of signed integers.
type FSignedInt = SignedInt Bool

-- | The quantum type of signed integers.
type QSignedInt = SignedInt Qubit

-- | The classical type of signed integers.
type CSignedInt = SignedInt Bit

-- ----------------------------------------------------------------------
-- * Conversions for 'FSignedInt'

-- | Take a length and an integer, and return a 'FSignedInt' of the
-- given length.
fsint_of_integer :: Int -> Integer -> FSignedInt
fsint_of_integer m x = SInt digits sign where
  digits = boollist_of_int_bh m (abs x)
  sign = (x < 0)
  
-- | Convert an 'FSignedInt' to an integer.
integer_of_fsint :: FSignedInt -> Integer
integer_of_fsint (SInt digits sign) = if sign then -a else a where
  a = int_of_boollist_unsigned_bh digits

-- | Get the length of a 'SignedInt'.
sint_length :: SignedInt x -> Int
sint_length (SInt digits sign) = length digits

instance Enum FSignedInt where
  succ x = fsint_of_integer m . succ . integer_of_fsint $ x
    where m = sint_length x
  pred x = fsint_of_integer m . pred . integer_of_fsint $ x
    where m = sint_length x
  toEnum x = fsint_of_integer m (fromIntegral x) 
    where m = (+) 1 $ ceiling $ logBase 2 $ fromIntegral x
  fromEnum x = fromIntegral . integer_of_fsint $ x

-- QCData instance

type instance QCType x y (SignedInt z) = SignedInt (QCType x y z)
type instance QTypeB FSignedInt = QSignedInt

instance QCLeaf x => QCData (SignedInt x) where
  qcdata_mapM (shape :: SignedInt x) f g (SInt digits sign) = do
    digits' <- qcdata_mapM [dummy :: x] f g digits
    sign' <- qcdata_mapM (dummy :: x) f g sign
    return (SInt digits' sign')
  
  qcdata_zip (shape :: SignedInt x) q c q' c' (SInt digits sign) (SInt digits' sign') e
    = (SInt digits'' sign'')
      where
        digits'' = qcdata_zip [dummy :: x] q c q' c' digits digits' errmsg
        sign'' = qcdata_zip (dummy :: x) q c q' c' sign sign' e
        errmsg x = e "SignedInt length mismatch"

  qcdata_promote (SInt digits sign) (SInt digits' sign') e
    | length digits /= length digits'
      = error (e "SignedInt length mismatch")
    | otherwise 
      = (SInt digits'' sign'')
    where
      digits'' = qcdata_promote digits digits' e
      sign'' = sign

-- Labeling of QSignedInt is s.sign, s[m-1], ..., s[0]
instance QCLeaf x => Labelable (SignedInt x) String where
  label_rec (SInt digits sign) s = do
    label_rec (reverse digits) s
    label_rec sign s `dotted_indexed` "sign"

-- * Operations

-- | Make two qubit lists be of the same length, by prepending qubits
-- initialized to 'False' to the head of the shorter of the two lists. 
left_pad_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit],[Qubit])
left_pad_qulist l1 l2 = if (length l1 == length l2) then return (l1,l2)
        else do
        let m = abs (length l1 - length l2)
        pad <- qinit (replicate m False)
        if (length l1 > length l2) then return (l1,pad ++ l2)
        else return (pad ++ l1, l2)

-- | Shift an 'FSignedInt' by /k/ digits to the left. In other words,
-- multiply it by 2[sup /k/], while simultaneously increasing the
-- length by /k/.
fsint_shift :: Int -> FSignedInt -> FSignedInt
fsint_shift k (SInt digits sign) = (SInt digits' sign)
  where
    digits' = digits ++ replicate k False


-- | One half of an isomorphism between 'QSignedInt' and ('Qubit', 'QDInt').
s_qdint_of_qsint :: QSignedInt -> (Qubit, QDInt)
s_qdint_of_qsint (SInt q b) = (b, qdint_of_qulist_bh q)

-- | The other half of an isomorphism between 'QSignedInt' and
-- ('Qubit', 'QDInt').
qsint_of_s_qdint :: (Qubit, QDInt) -> QSignedInt
qsint_of_s_qdint (b, q) = SInt (qulist_of_qdint_bh q) b

-- | Shift a 'QSignedInt' by /k/ digits to the left. In other words,
-- multiply it by 2[sup /k/], while simultaneously increasing the
-- length by /k/.
qsint_shift :: Int -> QSignedInt -> Circ QSignedInt
qsint_shift k (SInt digits sign) = do
  pad <- qinit (replicate k False)
  let digits' = digits ++ pad
  return (SInt digits' sign)




-- Ordering on QSignedInt. If two operands are to be compared, it is
-- not necessarily assumed that they are of the same length, and this
-- feature is actually exploited by the QOrd QDouble instance.
-- However, note that the default implementations of 'max' and 'min'
-- do assume equal length.
instance QOrd QSignedInt where
    q_less (SInt x' b) (SInt y' c) = do 
       (x,y) <- left_pad_qulist x' y'
       unpack template_be_signed_boollist_less (b, x) (c, y)


instance Eq FSignedInt where
  x == y = (integer_of_fsint x) == (integer_of_fsint y)
                                          
                                          
instance Ord FSignedInt where
  compare x y = compare (integer_of_fsint x) (integer_of_fsint y)


instance Num FSignedInt where
  x + y = fsint_of_integer m $ (integer_of_fsint x) + (integer_of_fsint y)
    where
      m = max (sint_length x) (sint_length y)
  x * y = fsint_of_integer m $ (integer_of_fsint x) * (integer_of_fsint y)
    where
      m = max (sint_length x) (sint_length y)
  x - y = fsint_of_integer m $ (integer_of_fsint x) - (integer_of_fsint y)
    where
      m = max (sint_length x) (sint_length y)
  fromInteger x = fsint_of_integer fixed_int_register_length x
  abs x = fsint_of_integer m . abs . integer_of_fsint $ x
    where
      m = sint_length x
  signum x = fsint_of_integer m . signum . integer_of_fsint $ x
    where
      m = sint_length x


instance Real FSignedInt where
  toRational = toRational . integer_of_fsint

instance Integral FSignedInt where
  quotRem x y = (fsint_of_integer m q, fsint_of_integer m r) where
    m = max (sint_length x) (sint_length y)
    (q,r) = quotRem (integer_of_fsint x) (integer_of_fsint y)
  toInteger = integer_of_fsint


instance QNum QSignedInt where
  q_add (SInt x' b) (SInt y' c) = do
      (x,y) <- left_pad_qulist x' y'
      (d,z) <- unpack template_be_signed_boollist_add (b,x) (c,y)
      return (SInt x' b, SInt y' c, SInt z d)
      
  q_mult (SInt x' b) (SInt y' c) = do 
      (x,y) <- left_pad_qulist x' y'
      (_, _, z') <- q_mult (qdint_of_qulist_bh x) (qdint_of_qulist_bh y)
      (_, _, d') <- q_add  (qdint_of_qulist_bh [b]) (qdint_of_qulist_bh [c])
      let z = qulist_of_qdint_bh z'
      let d = qulist_of_qdint_bh d'
      return (SInt x' b, SInt y' c, SInt z $ head d)

  q_sub x y = do
      (y,z)   <- q_negate y
      (x,z,t) <- q_add x z
      return (x,y,t)

  q_abs (SInt l s) = do 
      l' <- qinit $ qc_false l;
      s' <- qinit False
      controlled_not_at l' l
      return (SInt l s, SInt l' s')

  q_negate (SInt l s) = do 
      l' <- qinit $ qc_false l;
      s' <- qinit False
      controlled_not_at l' l
      qnot_at s' `controlled` s .==. 0
      return (SInt l s, SInt l' s')

  q_signum (SInt l s) = do 
      l' <- qinit $ qc_false l;
      s' <- qinit False
      qnot s' `controlled` s
      return (SInt l s, SInt l' s')
      
  q_fromQDInt l1 = do
      let l = qulist_of_qdint_bh l1
      l' <- qinit $ qc_false l;
      controlled_not_at l' l
      s' <- qinit False
      return (qdint_of_qulist_bh l, SInt l' s')



-- | The modulo operation on 'QSignedInt'.
q_mod :: QSignedInt -> QSignedInt -> Circ QSignedInt
q_mod x y = do
    let (x_b, x') = s_qdint_of_qsint x    
    let (y_b, y') = s_qdint_of_qsint y
    (_,_,z1) <- q_quot x' y'
    (_,_,z2) <- q_mult y' z1
    (_,_,z3) <- q_sub  x' z2
    z_b <- qinit False
    qnot_at z_b `controlled` x_b
    qnot_at z_b `controlled` y_b  -- XXXXXXXXXX TO CHECK
    let z = qsint_of_s_qdint (z_b,z3)
    return z



my_test = let x = fsint_of_integer 50 1595713 in
          let y = fsint_of_integer 30 547137 in
          let last (x,y,z) = z in
          do
          putStrLn $ show (x < y)
          putStrLn $ show $ last $ run_classical_generic q_add x y
          putStrLn $ show (x - y)
          putStrLn $ show $ last $ run_classical_generic q_sub x y
          putStrLn $ show $ run_classical_generic q_less x y
          putStrLn $ show $ run_classical_generic q_less y x
          print_simple GateCount $ do
              a <- qinit x
              b <- qinit y
              b <- q_less a b
              return ()


