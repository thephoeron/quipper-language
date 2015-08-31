-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

-- | 'example1': do a basis change, then perform some operation, then
-- uncompute the basis change. Drawback: if this is later controlled,
-- then the controls are applied to the basis change too, which is
-- unnecessary.

example1 :: Qubit -> Qubit -> Circ ()
example1 a b = do
  -- basis change
  gate_W_at a b
  qnot_at b `controlled` a
  
  -- some operation
  hadamard_at b `controlled` a
  
  -- undo basis change
  qnot_at b `controlled` a
  gate_W_at a b  

-- | 'example2': low-level solution. The 'without_controls' operator
-- can be used to inhibit the addition of further controls to blocks
-- of code.  (However, this is not very safe. A better way to do this
-- is shown in 'example3').

example2 :: Qubit -> Qubit -> Circ ()
example2 a b = do
  -- basis change
  without_controls $ do
    gate_W_at a b
    qnot_at b `controlled` a
  -- some operation
  hadamard_at b `controlled` a
  -- undo basis change
  without_controls $ do
    qnot_at b `controlled` a
    gate_W_at a b

-- | 'example3': a better way to achieve the effect of 'example2' is
-- to use the operator 'with_basis_change'. This will take care of the
-- uncomputation automatically, and also ensure that controls will not
-- be added to the basis change.
example3 :: Qubit -> Qubit -> Circ ()    
example3 a b = do
  with_basis_change basischange $ do
    hadamard_at b `controlled` a

    where
      basischange = do
        gate_W_at a b
        qnot_at b `controlled` a

-- | 'example4': a similar effect is introduced by the operator
-- 'with_ancilla'. Normally, the gates that initialize and terminate
-- ancillas cannot be controlled. However, when using the
-- 'with_ancilla' operator, the resulting circuit can be controlled as
-- a whole, provided that the body is controllable.

example4 :: Qubit -> Qubit -> Circ ()
example4 a b = do
  with_ancilla $ \d -> do
    with_basis_change (qnot_at d `controlled` b .==. False) $ do
      hadamard_at a `controlled` d

my_circuit :: Qubit -> Qubit -> Qubit -> Circ ()
my_circuit ctrl a b = do
  example1 a b `controlled` ctrl
  example2 a b `controlled` ctrl
  example3 a b `controlled` ctrl
  example4 a b `controlled` ctrl

main =
  print_simple Preview my_circuit
  
