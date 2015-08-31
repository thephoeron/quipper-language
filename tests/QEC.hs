-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================


import Quipper

-- import other stuff
import Control.Monad (zipWithM_)

-- ======================================================================
-- ALGORITHM SPECIFIC CODE

{- the test circuit from Alex V. and Benoit's email. It looks like
this:

In Alex's notation: 

  H(a)
  c = meas(a)
  if c then
    X(b)
  else Y(b)

In circuit notation:

 a -H--Meas===x==o==|
              |  |
 b -----------X--Y----

In QPL notation: 
-} 

testcircuit :: (Qubit, Qubit) -> Circ Qubit
testcircuit (a,b) = do
  hadamard a
  c <- measure a
  with_controls (c .==. 1) $ do {
    gate_X_at b
  }
  with_controls (c .==. 0) $ do {
    gate_Y_at b
  }
  cdiscard c
  return b

-- Let's see if we can implement some parts of the Steane
-- code. Working from Alex V.'s notes.


-- prepare the logical |+〉 state for the Steane code. This returns a list
-- of 7 qubits
plusState :: Circ [Qubit]
plusState = do
  -- prepare (a...g) in the state "00+0+++"
  [a,b,c,d,e,f,g] <- qinit_of_string "00+0+++"

  qnot_at a `controlled` c .==. 1
  qnot_at d `controlled` f .==. 1
  qnot_at b `controlled` g .==. 1
  qnot_at a `controlled` e .==. 1
  qnot_at d `controlled` g .==. 1
  qnot_at b `controlled` f .==. 1
  qnot_at a `controlled` g .==. 1
  qnot_at b `controlled` c .==. 1
  qnot_at d `controlled` e .==. 1
  
  return [a,b,c,d,e,f,g]

-- prepare the logical |0〉 state for the Steane code
zeroState :: Circ [Qubit]
zeroState = do
  -- prepare (a...g) in the state "00+0+++"
  [a,b,c,d,e,f,g] <- qinit_of_string "++0+000"

  qnot_at c `controlled` a .==. 1
  qnot_at f `controlled` d .==. 1
  qnot_at g `controlled` b .==. 1
  qnot_at e `controlled` a .==. 1
  qnot_at g `controlled` d .==. 1
  qnot_at f `controlled` b .==. 1
  qnot_at g `controlled` a .==. 1
  qnot_at c `controlled` b .==. 1
  qnot_at e `controlled` d .==. 1
  
  return [a,b,c,d,e,f,g]

preparePlus :: Circ ([Qubit], Bit)
preparePlus = do
  qs <- plusState
  vs <- plusState
  zipWithM_ (\q v -> qnot_at q `controlled` v .==. 1) qs vs
  measure <- mapM measure vs
  result <- cgate_and measure
  mapM_ cdiscard measure
  return (qs, result)

{-
-- this function operates on a 7-tuple of qubits, which are inputs and
-- outputs. The additional output Bit is 0 when the error correction
-- fails, else 1
preGateCorrection :: (Qubit,Qubit,Qubit,Qubit,Qubit,Qubit,Qubit) -> Bit
preGateCorrection q = do
  result = cinit_bit False
  (a, av, result_a) <- preparePlus []
  with_controls (result_a .==. 1) $ do {
    (b, bv, result_b) <- prepareZero
    with_controls (result_b .==. 1) $ do {
      zRecover(q, a),
      xRecover(q, b),
      cnot result
    }
    with_controls (result_b .==. 0) $ do {
      .....
-}

    
-- ======================================================================
-- main functions (ugly, don't follow an "idiom" yet)

-- this is just a main function to print the circuit
main_testcircuit :: IO()
main_testcircuit =
  print_generic Preview testcircuit (qubit,qubit)

-- this is just a main function to print the circuit
main_plusState :: IO()
main_plusState =
  print_generic Preview plusState

-- this is just a main function to print the circuit
main_zeroState :: IO()
main_zeroState =
  print_generic Preview zeroState
   
-- this is just a main function to print the circuit
main_preparePlus :: IO()
main_preparePlus =
  print_generic Preview preparePlus
   
main = main_preparePlus

  
