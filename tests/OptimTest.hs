-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | A test for the 'simplify_classical' function. As an example, we use
-- a simple adder defined using the @build_circuit@ keyword. 'main1'
-- outputs the unoptimized circuit, and 'main2' outputs the optimized
-- version.

import Quipper
import QuipperLib.ClassicalOptim
import QuipperLib.ClassicalOptim.QuickCheck (myAdder)

main1 :: IO()
main1 = do
  print_generic Preview myAdder (replicate 3 qubit, replicate 3 qubit)

main2 :: IO()
main2 = do
  print_generic Preview (simplify_classical myAdder) (replicate 3 qubit, replicate 3 qubit)

main :: IO()
main = main2


