-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- This file illustrates how global phase gates will be rendered in
-- graphical circuit diagrams.

import Quipper

mycirc :: (Qubit, Qubit, Qubit) -> Circ ()
mycirc (a,b,c) = do
  comment "Unanchored"
  global_phase 1.0
  
  comment "Anchored at a"
  global_phase_anchored 1.0 a
  
  comment "Anchored at b"
  global_phase_anchored 1.0 b
  
  comment "Anchored at c"
  global_phase_anchored 1.0 c
  
  comment "Anchored at (a,b)"
  global_phase_anchored 1.0 (a,b)
  
test :: (Qubit, Qubit, Qubit) -> Circ ()
test (a,b,c) = do 
  label (a,b,c) ("a", "b", "c")
  mycirc (a,b,c)
  mycirc (a,b,c) `controlled` a
  mycirc (a,b,c) `controlled` b
  mycirc (a,b,c) `controlled` c
  mycirc (a,b,c) `controlled` a .==. 1 .&&. b .==. 0 .&&. c .==. 0

main = 
  print_simple Preview test
