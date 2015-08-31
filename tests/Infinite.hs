-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper
import QuipperLib.Decompose

-- Outputs an infinite circuit. This illustrates the use of laziness
-- in the Quipper circuit generation code. 

-- Please note that currently only the ASCII backend can make actual
-- use of laziness; the graphics-based backends must generate the
-- whole circuit before it can be printed.

-- We also apply a transformer, to illustrate the laziness of
-- transformers as well.

infinite_circuit :: Qubit -> Qubit -> Qubit -> Circ (Qubit, Qubit, Qubit)
infinite_circuit q r s = do
  qnot_at q `controlled` [r,s]
  hadamard_at r
  infinite_circuit s q r
  
infinite_circuit_transformed = decompose_generic Binary infinite_circuit

main1 = 
  print_simple ASCII infinite_circuit

main = 
  print_simple ASCII infinite_circuit_transformed
