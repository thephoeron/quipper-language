-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

circuit :: (Bit, Qubit) -> Circ (Qubit, Qubit)
circuit (b,q) = do
  qnot_at q `controlled` b
  r <- prepare b
  gate_W_at q r
  return (q,r)
  
main =   
  print_simple Preview circuit
  
