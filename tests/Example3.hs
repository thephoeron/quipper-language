-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

example1 :: (Qubit,Qubit,Qubit,Qubit) -> Circ (Qubit,Qubit,Qubit,Qubit)
example1 (q, a, b, c) = do
    hadamard a
    qnot_at c `controlled` [a, b]
    hadamard q `controlled` [c]
    qnot_at c `controlled` [a, b]
    hadamard a
    return (q, a, b, c)

example3 :: (Qubit,Qubit,Qubit,Qubit,Qubit,Qubit) -> Circ (Qubit,Qubit,Qubit,Qubit,Qubit,Qubit)
example3 (q, a, b, c, d, e) = do
    example1 (q, a, b, c)
    with_controls (d .==. 0 .&&. e .==. 1) $ do
      example1 (q, a, b, c)
      example1 (q, a, b, c)
    example1 (q, a, b, c)
    return (q, a, b, c, d, e)

main = print_simple Preview example3
