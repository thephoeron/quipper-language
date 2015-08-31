-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

example1 :: (Qubit,Qubit,[Qubit]) -> Circ (Qubit,Qubit,[Qubit])
example1 (q, a, b) = do
    comment_with_label "Start of example 1" (q,a,b) ("q","a","b")
    hadamard a
    qnot_at a `controlled` b
    hadamard q `controlled` a
    qnot_at a `controlled` b
    hadamard a
    comment "End of example 1"
    return (q, a, b)

example3 :: (Qubit,Qubit,[Qubit],Qubit,Qubit) -> Circ (Qubit,Qubit,[Qubit],Qubit,Qubit)
example3 (q, a, b, d, e) = do
    comment_with_label "Start of example 3" (q,a,b,d,e) ("q","a","b","d","e")
    example1 (q, a, b)
    with_controls (d .==. 0 .&&. e .==. 1) $ do
      example1 (q, a, b)
      example1 (q, a, b)
    example1 (q, a, b)
    comment "End of example 3"
    return (q, a, b, d, e)

main = print_generic Preview example3 (qubit, qubit, replicate 3 qubit, qubit, qubit)
