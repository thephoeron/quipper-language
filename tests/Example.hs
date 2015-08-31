-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================


import Quipper
import Prelude hiding (and)

example1 :: (Qubit, Qubit, Qubit) -> Circ (Qubit, Qubit, Qubit)
example1 (a,b,c) = do
  qnot_at a `controlled` [b, c]
  hadamard b `controlled` [a]
  qnot_at a `controlled` [b, c]
  hadamard c `controlled` [a]
  return (a,b,c)

example2 :: Qubit -> Qubit -> Qubit -> Qubit -> Circ ()
example2 h a b c = do
  qnot_at c `controlled` [a, b]
  hadamard h `controlled` [c]
  qnot_at c `controlled` [a, b]

example3 :: Qubit -> Qubit -> Qubit -> Circ ()
example3 h a b = do
  with_ancilla $ \c -> do
    qnot_at c `controlled` [a, b]
    hadamard h `controlled` [c]
    qnot_at c `controlled` [a, b]

example4 :: (Qubit, Qubit, Qubit, Qubit) -> Circ (Qubit, Qubit, Qubit, Qubit)
example4 (a,b,c,d) = do
  qnot_at a
  qnot_at b
  with_controls (c .&&. d) $ do
    qnot_at a
    qnot_at b
  qnot_at c
  return (a,b,c,d)

main =
  print_simple Preview example4
