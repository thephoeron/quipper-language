-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module implements the Quantum Fourier Transform.

module QuipperLib.QFT (
  qft_little_endian,
  qft_big_endian,
  qft_rev,
  qft_int
  ) where

import Quipper
import QuipperLib.Arith

import Libraries.Auxiliary (mmap)

-- ----------------------------------------------------------------------
-- * Low-level implementation

-- | Like 'qft_rev', but without the comments and labels.
-- 
-- Apply the Quantum Fourier Transform to a list of /n/ qubits.
-- The input is little-endian and the output is big-endian.
-- 
-- Unlike 'qft_little_endian' and 'qft_big_endian', this function can
-- be used in imperative style, i.e., it modifies its arguments \"in
-- place\".
qft_internal :: [Qubit] -> Circ [Qubit]
qft_internal [] = return []
qft_internal [x] = do 
  hadamard x
  return [x]
qft_internal (x:xs) = do 
  xs' <- qft_internal xs
  xs'' <- rotations x xs' (length xs')
  x' <- hadamard x
  return (x':xs'')
  where
    -- Auxiliary function used by 'qft'.
    rotations :: Qubit -> [Qubit] -> Int -> Circ [Qubit]
    rotations _ [] _ = return []
    rotations c (q:qs) n = do 
      qs' <- rotations c qs n
      q' <- rGate ((n + 1) - length qs) q `controlled` c
      return (q':qs')

-- ----------------------------------------------------------------------
-- * Wrappers

-- | Apply the Quantum Fourier Transform to a list of /n/ qubits.
-- Both the input and output qubit lists are little-endian, i.e., the
-- leftmost qubit (head of the list) is the least significant one.
-- 
-- Note that this function cannot be used in imperative style, i.e.,
-- it does not update its arguments \"in place\". The output qubits
-- are in different physical locations than the input ones.
qft_little_endian :: [Qubit] -> Circ [Qubit]
qft_little_endian qs = do
  comment_with_label "ENTER: qft_little_endian" qs "qs"
  qs' <- qft_internal qs
  let qs = reverse qs'
  comment_with_label "EXIT: qft_little_endian" qs "qs"
  return qs
  
-- | Apply the Quantum Fourier Transform to a list of /n/ qubits.
-- Both the input and output qubit lists are big-endian, i.e., the
-- leftmost qubit (head of the list) is the most significant one.
-- 
-- Note that this function cannot be used in imperative style, i.e.,
-- it does not update its arguments \"in place\". The output qubits
-- are in different physical locations than the input ones.
qft_big_endian :: [Qubit] -> Circ [Qubit]  
qft_big_endian qs = do
  comment_with_label "ENTER: qft_big_endian" qs "qs"
  qs <- qft_internal (reverse qs)
  comment_with_label "EXIT: qft_big_endian" qs "qs"
  return qs

-- | Apply the Quantum Fourier Transform to a list of /n/ qubits.
-- The input is little-endian and the output is big-endian.
-- 
-- Unlike 'qft_little_endian' and 'qft_big_endian', this function can
-- be used in imperative style, i.e., it modifies its arguments
-- \"in place\".
qft_rev :: [Qubit] -> Circ [Qubit]
qft_rev qs = do
  comment_with_label "ENTER: qft_rev" qs "qs"
  qs <- qft_internal qs
  comment_with_label "EXIT: qft_rev" qs "qs"
  return qs

-- | Apply the Quantum Fourier Transform to a 'QDInt'.
-- 
-- Note that this function cannot be used in imperative style, i.e.,
-- it does not update its arguments \"in place\". The output qubits
-- are in different physical locations than the input ones.
qft_int :: QDInt -> Circ QDInt
qft_int x = do
  comment_with_label "ENTER: qft_int" x "x"
  x <- mmap qdint_of_qulist_bh $ qft_big_endian $ qulist_of_qdint_bh x
  comment_with_label "ENTER: qft_int" x "x"
  return x

-- ----------------------------------------------------------------------
-- * Testing

-- | A simple test.
test :: Int -> IO ()
test n = print_generic Preview qft_little_endian (replicate n qubit)
