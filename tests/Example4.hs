-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

example4 :: (Qubit, Qubit, Qubit) -> Circ (Qubit, Qubit, Qubit)
example4(q, a, b) = do
  with_ancilla $ \c -> do
    qnot_at c `controlled` [a, b]
    hadamard q `controlled` [c]
    qnot_at c `controlled` [a, b]
  return (q, a, b)

main = print_simple Preview example4
