-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- Test the dynamic lifting feature. 

import Quipper

-- | A circuit in which some future gates depend on a prior measurement.
circuit :: Qubit -> Qubit -> Circ Qubit
circuit a b = do
  qnot_at a `controlled` b
  m <- measure a
  bool <- dynamic_lift m
  if bool == 0 then
      do
       hadamard_at b
       return b
    else
      do
       c <- qinit False
       qnot_at c `controlled` b
       qdiscard b
       return c

main = do
  print_simple ASCII circuit
