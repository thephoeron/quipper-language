-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- $ Test whether the quantum simulator works correctly on a global
-- phase gate.

import Quipper
import QuipperLib.Simulation

-- | This function should compute a Not gate.
testcirc :: Qubit -> Circ Qubit
testcirc a = do
  hadamard_at a
  global_phase 1.0 `controlled` a
  hadamard_at a
  return a
  
main = do
  b <- run_generic_io d testcirc False
  putStrLn ("testcirc False = " ++ show b)
  b <- run_generic_io d testcirc True
  putStrLn ("testcirc True = " ++ show b)
 where
  d :: Double
  d = undefined 
