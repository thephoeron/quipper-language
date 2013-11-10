-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

plus_minus :: Bool -> Circ Qubit
plus_minus b = do
    q <- qinit b
    q <- hadamard q
    return q

share :: Qubit -> Circ (Qubit, Qubit)
share a = do
    b <- qinit False
    b <- qnot b `controlled` a
    return (a,b)

bell00 :: Circ (Qubit, Qubit)
bell00 = do
    a <- plus_minus False
    (a,b) <- share a
    return (a,b)

alice :: Qubit -> Qubit -> Circ (Bit,Bit)
alice q a = do
    a <- qnot a `controlled` q
    q <- hadamard q
    (x,y) <- measure (q,a)
    return (x,y)

bob :: Qubit -> (Bit,Bit) -> Circ Qubit
bob b (x,y) = do
    b <- gate_X b `controlled` y
    b <- gate_Z b `controlled` x
    cdiscard (x,y)
    return b

teleport :: Qubit -> Circ Qubit
teleport q = do
    (a,b) <- bell00
    (x,y) <- alice q a
    b <- bob b (x,y)
    return b

-- ----------------------------------------------------------------------
-- main functions

main_alice =
  print_simple Preview alice

main_bob =
  print_simple Preview bob

main_teleport =
  print_simple Preview teleport

main = main_teleport

