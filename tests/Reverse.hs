-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

my_circuit :: (Qubit, Qubit) -> Circ (Qubit, Qubit)
my_circuit (a,b) = do
  qnot_at a `controlled` b
  hadamard b `controlled` a
  return (a,b) 
  
rev_circuit :: (Qubit, Qubit) -> Circ (Qubit, Qubit)
rev_circuit = reverse_simple my_circuit

main =
  print_simple Preview rev_circuit
