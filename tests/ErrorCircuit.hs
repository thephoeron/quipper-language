-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper
import QuipperLib.Decompose

-- Outputs a partially undefined circuit. This illustrates the use of
-- laziness in the Quipper circuit generation code.

-- Please note that currently only the ASCII backend can make actual
-- use of laziness; the graphics-based backends must generate the
-- whole circuit before it can be printed.

-- We also apply a transformer, to illustrate the laziness of
-- transformers as well.

circuit_with_error :: Qubit -> Qubit -> Qubit -> Circ (Qubit, Qubit, Qubit)
circuit_with_error q r s = do
  qnot_at q `controlled` [r,s]
  hadamard_at r
  error "A runtime error occurred!"
  hadamard_at r
  return (q, r, s)  
  
circuit_with_error_transformed = decompose_generic Binary circuit_with_error

main =
  print_simple ASCII circuit_with_error

main2 = 
  print_simple ASCII circuit_with_error_transformed
