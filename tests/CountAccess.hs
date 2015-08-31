-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | Consider the following problem, suggested by Dmitry Maslov: Input
-- a list of bits. Let /i/ be the weight of the list, i.e., the number
-- of \"1\" bits in the list. Output the /i/th element, where elements
-- are counted from 0 and we wrap around cyclically if /i/ equals the
-- length of the list.

import Quipper
import QuipperLib.Arith
import QuipperLib.Qram

import Prelude hiding (truncate)

-- | Figure out how many bits are needed to store a given integer. 
hibit :: Int -> Int
hibit 0 = 0
hibit n = 1 + hibit (n `div` 2)

-- | @'truncate' n q@: Input a classical integer /n/ and a quantum
-- integer /q/. Output /0/ if /q/=/n/, and /q/ otherwise. For the
-- problem at hand, this is cheaper than full modular arithmetic. 
truncate :: IntM -> QDInt -> Circ QDInt
truncate n q = do
  q' <- qc_copy q
  with_controls (q .==. n) $ do
    controlled_not q' q
  return q'

-- | Input a list of qubits and return its weight.
weight :: [Qubit] -> Circ QDInt
weight qs = q where
  len = length qs
  bits = hibit len
  zero = intm bits 0
  q = do
    q <- qinit zero
    q <- aux qs q
    q1 <- truncate (intm bits (toInteger len)) q
    return q1

  aux [] q = return q
  aux (h:t) q = do
    q <- q_increment q `controlled` h
    q <- aux t q
    return q

-- | Input a list of qubits, and output the /i/th qubit, where /i/ is
-- the weight of the list.
countshift :: [Qubit] -> Circ Qubit
countshift qs = do
  q <- weight qs
  a <- indexed_access qs q
  return a

-- | Reversible version of 'countshift'. 
countshift_rev :: [Qubit] -> Circ ([Qubit], Qubit)
countshift_rev qs = do
  b <- with_computed (countshift qs) $ \a -> do
    qc_copy a
  return (qs, b)

-- | A main function to print the circuit.
main = 
  print_generic Preview countshift_rev (replicate 7 qubit)
