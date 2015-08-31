-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

-- Unboxed version of subroutine
my_sub :: (Qubit, Qubit, Qubit) -> Circ (Qubit, Qubit, Qubit)
my_sub (a,b,c) = do
  hadamard_at a `controlled` b
  hadamard_at a `controlled` c
  hadamard_at b `controlled` c
  return (a,b,c)
  
-- Boxed version of subroutine
boxed_sub :: (Qubit, Qubit, Qubit) -> Circ (Qubit, Qubit, Qubit)
boxed_sub = box "my_sub" my_sub

-- Unboxed version of circuit
my_circuit :: [Qubit] -> Circ [Qubit]
my_circuit [] = return []
my_circuit [a] = return [a]
my_circuit [a,b] = return [a,b]
my_circuit (a:b:c:rest) = do
  (a,b,c) <- my_sub (a,b,c)
  x <- my_circuit (b:c:rest)
  return (a:x)

-- Boxed version of circuit
my_circuit_boxed :: [Qubit] -> Circ [Qubit]
my_circuit_boxed [] = return []
my_circuit_boxed [a] = return [a]
my_circuit_boxed [a,b] = return [a,b]
my_circuit_boxed (a:b:c:rest) = do
  (a,b,c) <- boxed_sub (a,b,c)
  x <- my_circuit_boxed (b:c:rest)
  return (a:x)

main = do
  print_generic Preview my_circuit_boxed (replicate 6 qubit)
