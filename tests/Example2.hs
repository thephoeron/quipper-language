-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

  import Quipper

  example2 (q, a, b) = do
    hadamard a
    with_ancilla $ \c -> do
      qnot_at c `controlled` [a, b]
      hadamard_at q `controlled` [c]
      qnot_at c `controlled` [a, b]
    hadamard_at a
    return (q, a, b)

  main = print_simple Preview example2
