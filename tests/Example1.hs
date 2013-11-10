-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

  import Quipper

  example1 (q, a, b, c) = do
    hadamard a
    qnot_at c `controlled` [a, b]
    hadamard q `controlled` [c]
    qnot_at c `controlled` [a, b]
    hadamard a
    return (q, a, b, c)

  main = print_simple Preview example1
