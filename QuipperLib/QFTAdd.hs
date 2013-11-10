-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides an implementation of the addition circuit found in 
-- Thomas G. Draper's  paper \"Addition on a Quantum Computer\".
module QuipperLib.QFTAdd 
(
  qft_add_in_place
)
where

import Quipper
import QuipperLib.Arith -- we make use of the QDInt data type for quantum integers
import QuipperLib.QFT -- we make use of the big endian QFT

-- | Add one 'QDInt' onto a second, in place; i.e. (/x/,/y/) ↦ (/x/,/x/+/y/).  
-- Arguments are assumed to be of equal size.
-- This implementation follows the implementation in Thomas G. Draper's 
-- paper \"Addition on a Quantum Computer\" which doesn't require the use of any
-- ancilla qubits through a clever use of the Quantum Fourier Transform.
qft_add_in_place :: QDInt -> QDInt -> Circ (QDInt,QDInt)
qft_add_in_place x y = do
  let x' = list_of_xint_bh x
  let y' = list_of_xint_bh y
  (x', y') <- qft_add_in_place_qulist x' y'
  let x = xint_of_list_bh x'
  let y = xint_of_list_bh y'
  return (x, y)

-- | Low-level implementation of 'qft_add_in_place': represents integers
-- as big-headian qubit lists.
qft_add_in_place_qulist :: [Qubit] -> [Qubit] -> Circ ([Qubit], [Qubit])
qft_add_in_place_qulist a b = do
  label (a,b) ("a","b")
  with_computed (box "QFT" qft_big_endian b) $ \b' -> do
   qft_adder a (reverse b')
  label (a,b) ("a","b")
  return (a,b)

-- | The circuit that performs the addition after a QFT
qft_adder :: [Qubit] -> [Qubit] -> Circ ()
qft_adder _ [] = return ()
qft_adder as (b:bs) = do
  qft_adder' as b 1
  qft_adder (tail as) bs
 where
  qft_adder' :: [Qubit] -> Qubit -> Int -> Circ [Qubit]
  qft_adder' [] _ _ = return []
  qft_adder' (a:as) b n = do
   b <- rGate n b `controlled` a
   qft_adder' as b (n+1)
