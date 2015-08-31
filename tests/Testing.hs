-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- $
-- Generate some circuits for the slides in the PI presentation.

import Quipper

example_H3 :: Qubit -> Qubit -> Qubit -> Qubit -> Circ ()
example_H3 h a b c = do
  with_ancilla $ \d -> do
    with_ancilla $ \e -> do
      qnot_at d `controlled` a .==. 1 .&&. b .==. 1
      qnot_at e `controlled` c .==. 1 .&&. d .==. 1
      hadamard_at h `controlled` e .==. 1
      qnot_at e `controlled` c .==. 1 .&&. d .==. 1
      qnot_at d `controlled` a .==. 1 .&&. b .==. 1

example_H3' :: Qubit -> Qubit -> Qubit -> Qubit -> Qubit -> Qubit -> Circ ()
example_H3' h a b c d e = do
      qnot_at d `controlled` a .==. 1 .&&. b .==. 1
      qnot_at e `controlled` c .==. 1 .&&. d .==. 1
      hadamard_at h `controlled` e .==. 1
      qnot_at e `controlled` c .==. 1 .&&. d .==. 1
      qnot_at d `controlled` a .==. 1 .&&. b .==. 1

example :: Qubit -> Qubit -> Qubit -> Qubit -> Circ ()
example a b c d = do
  example_H3 a b c d
  qnot_at a `controlled` b .==. 1
  qnot_at b `controlled` c .==. 1
  qnot_at c `controlled` d .==. 1 .&&. a .==. 1
  qnot_at b `controlled` c .==. 1
  qnot_at a `controlled` b .==. 1
  example_H3 b c d a

example' :: Qubit -> Qubit -> Qubit -> Qubit -> Qubit -> Qubit -> Circ ()
example' a b c d anc1 anc2 = do
  example_H3' a b c d anc1 anc2
  qnot_at a `controlled` b .==. 1
  qnot_at b `controlled` c .==. 1
  qnot_at c `controlled` d .==. 1 .&&. a .==. 1
  qnot_at b `controlled` c .==. 1
  qnot_at a `controlled` b .==. 1
  example_H3' b c d a anc1 anc2


main3 =
  print_generic Preview example qubit qubit qubit qubit

main =
  print_simple Preview example'

ec1 :: Qubit -> Circ [Qubit]
ec1 a = do
  b <- qinit False
  c <- qinit False
  qmultinot_at (b,c) `controlled` a .==. 1
  return [a,b,c]

corr :: [Qubit] -> Circ Qubit
corr [a,b,c] = do
  qmultinot_at (a,c) `controlled` b .==. 1
  (a',c') <- measure (a,c)
  qnot_at b `controlled` a' .==. 1 .&&. c' .==. 1
  cdiscard (a',c')
  return b

ec2 :: [Qubit] -> Circ [Qubit]
ec2 [a,b,c] = do
  [a1,a2,a3] <- ec1 a
  [b1,b2,b3] <- ec1 b
  [c1,c2,c3] <- ec1 c
  x1 <- corr [a1,b1,c1]
  x2 <- corr [a2,b2,c2]
  x3 <- corr [a3,b3,c3]
  return [x1,x2,x3]


main4 = print_generic Preview ec2 [qubit, qubit, qubit]
