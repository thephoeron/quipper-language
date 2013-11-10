-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

circuit :: Qubit -> Qubit -> Qubit -> Circ (Qubit, Qubit, Qubit, Qubit)
circuit a b c = do
  qnot_at a `controlled` c .==. 1
  hadamard_at b `controlled` c .==. 0
  d <- qinit False
  qnot_at d `controlled` b .==. 1
  return (a,b,c,d)

main = print_simple Preview circuit
