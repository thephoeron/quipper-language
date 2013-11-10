-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

crazy :: (QData a, QCData b) => (a -> Circ b) -> (a -> Circ (a,b))
crazy f a = do
  mapUnary hadamard a
  y <- with_computed (f a) $ \b -> do
    b' <- qc_copy b
    return (a,b')
  return y

circuit :: [Qubit] -> Circ ([Qubit], [Qubit])
circuit qs = do
  y <- with_computed values $ \values -> do
    qc_copy values
  return (qs, y)
  
    where
      values = do
        mapUnary hadamard qs
        a <- qinit True
        b <- qinit False
        qnot_at a `controlled` qs
        qnot_at b `controlled` qs .==. [0,0..]
        c <- qinit False
        qnot_at c `controlled` [a,b]
        qnot_at b `controlled` qs .==. [0,0..]
        qnot_at a `controlled` qs
        qterm False b  
        qterm True a
        return (c:qs)

circuit2 :: [Qubit] -> Circ ([Qubit], ([Qubit], [Qubit]))
circuit2 = crazy circuit

circuit3 :: [Qubit] -> Circ ([Qubit], ([Qubit], ([Qubit], [Qubit])))
circuit3 = crazy circuit2

circuit4 = crazy circuit3

main = print_generic Preview circuit4 (replicate 5 qubit)
