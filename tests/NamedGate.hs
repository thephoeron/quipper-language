-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper hiding (gate_V)

my_unary_gate :: Qubit -> Circ Qubit
my_unary_gate = named_gate "Q"

my_binary_gate :: (Qubit, Qubit) -> Circ (Qubit, Qubit)
my_binary_gate = named_gate "R"

my_unary_gate_at :: Qubit -> Circ ()
my_unary_gate_at = named_gate_at "Q"

my_binary_gate_at :: (Qubit, Qubit) -> Circ ()
my_binary_gate_at = named_gate_at "R"

gate_V :: Qubit -> Circ Qubit
gate_V = named_gate "V"

circuit :: Qubit -> Qubit -> Circ (Qubit, Qubit)
circuit a b = do
  a <- gate_V a
  (c,d) <- my_binary_gate (a,b)
  c <- my_unary_gate a `controlled` d
  my_binary_gate_at (c, d)
  my_binary_gate_at (d, c)
  my_unary_gate_at d
  c <- gate_V c
  d <- gate_V d
  return (c,d)

main = print_simple Preview circuit
