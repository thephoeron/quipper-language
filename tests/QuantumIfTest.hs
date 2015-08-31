-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper
import QuipperLib.Simulation
import Algorithms.BF.QuantumIf

-- ----------------------------------------------------------------------
-- * Testing quantum \"if then else\"

-- | A dummy value of type Double, to feed the type in the simulator
double :: Double
double = undefined

-- | A testing function that displays a circuit that tests the 'if_then_elseQ'
-- statement, and the results of running the circuit on various inputs.
if_test :: IO ()
if_test = do
    print_simple ASCII ifTest2
    print_simple Preview ifTest2
    res0 <- run_generic_io double ifTest2 (False,False,False)
    putStrLn (show res0)
    res1 <- run_generic_io double ifTest2 (False,False,True)
    putStrLn (show res1)
    res2 <- run_generic_io double ifTest2 (False,True,False)
    putStrLn (show res2)
    res3 <- run_generic_io double ifTest2 (False,True,True)
    putStrLn (show res3)
    res4 <- run_generic_io double ifTest2 (True,False,False)
    putStrLn (show res4)
    res5 <- run_generic_io double ifTest2 (True,False,True)
    putStrLn (show res5)
    res6 <- run_generic_io double ifTest2 (True,True,False)
    putStrLn (show res6)
    res7 <- run_generic_io double ifTest2 (True,True,True) 
    putStrLn (show res7)

-- | A test of the 'if_then_elseQ' function.
ifTest :: Circ (Qubit,Qubit,Qubit)
ifTest = do
    (q0,q1,q2,q3,q4,q5,q6) <- qinit (False,False,False,False,False,False,False)
    qnot_at q4
    if_then_elseQ (Or (A q0) (And (A q1) (Not (A q2))))
     ( --if q0 | (q1 & !q2)
      qnot_at q4
     )
     (
      if_then_elseQ (And (A q2) (A q3))
      ( --else if
       qnot_at q5 
      )
      ( -- else
        qnot_at q6
      )
     )
    return (q4,q5,q6)	

-- | Another test of the 'if_then_elseQ' function.
ifTest2 :: (Qubit,Qubit,Qubit) -> Circ (Qubit,Qubit)
ifTest2 (l,p,d) = do
   ctrl <- qinit True
   (x,y) <- qinit (False,False)
   with_controls ctrl 
    (
    do 
    if_then_elseQ (Or (A l) (And (A p) (Not (A d))))
     ( --if l | (p & !d) 
      qnot_at x
     )
     ( -- else
      qnot_at y
     )
    )
   qdiscard (l,p,d)
   qterm True ctrl
   return (x,y)

-- | A simple test of the 'if_then_elseQ' function.
ifTest3 :: Qubit -> Circ (Qubit,Qubit)
ifTest3 q = do
    (q0,q1) <- qinit (False,False)
    if_then_elseQ (A q)
     (
        qnot_at q0
     )
     (
       qnot_at q1
     )
    qdiscard q
    return (q0,q1) 

-- | A small circuit for testing 'if_then_elseQinv' statements.
small_circ :: [Qubit] -> Circ ([Qubit],Qubit,Qubit)
small_circ qs = do
   (q1,q2) <- qinit (False,False)
   tempReg0 <- qinit (replicate (length qs) False)
   tempReg1 <- qinit (replicate (length qs) True)
   let boolean_statement = foldr1 (\x y -> And x y) (map A qs)
   let boolean_statement_out = Not boolean_statement
   if_then_elseQinv boolean_statement
    (
     do
     qnot_at q1
     swap (reverse tempReg0) (reverse qs)
     return ()
    )
    (
     do
     swap tempReg1 qs
     qnot_at q2
    ) boolean_statement_out
   return (qs,q1,q2) 

-- | Display the 'small_circ'.
print_small_circ :: IO ()
print_small_circ = print_generic Preview small_circ (replicate 4 qubit) 

-- | Simulate the 'small_circ'.
test_small_circ :: [Bool] -> IO ()
test_small_circ bs = do
    putStr (show bs ++ " -> ")
    res <- run_generic_io double small_circ bs
    putStrLn (show res)

-- | A main function.
main :: IO ()
main = test_small_circ [True,True,False]

