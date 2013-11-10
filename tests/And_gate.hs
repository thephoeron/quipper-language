-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

and_gate :: (Qubit, Qubit) -> Circ (Qubit)
and_gate (a, b) = do
  c <- qinit False
  qnot_at c `controlled` [a, b]
  return c

main =
  print_simple PDF and_gate
