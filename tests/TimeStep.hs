-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper
import QuipperLib.Qureg
import Algorithms.BWT.Definitions

-- | Algorithm 3. @timestep (a, b, r, dt, m)@: Apply the
-- time step /dt/ to (/a/,/b/,/r/). Here /a/ and /b/ are /m/-qubit
-- registers while /r/ is a single qubit.
timestep :: (Qureg, Qureg, Qubit, Timestep, Int) -> Circ ()
timestep (a, b, r, dt, m) = do
  comment_with_label "ENTER: timestep" (a,b,r) ("a","b","r")
  with_ancilla $ \h -> do
    for 0 (m-1) 1 $ \i -> do
      wGate (a.!(i), b.!(i))
    endfor
    for 0 (m-1) 1 $ \i -> do
      toffoliGate (a.!(i), b.!(i), h)
    endfor
    controlledExpGate (dt, r, h)
    for (m-1) 0 (-1) $ \i -> do
      toffoliGate (a.!(i), b.!(i), h)
    endfor
    for (m-1) 0 (-1) $ \i -> do
      wGateInverse (a.!(i), b.!(i))
    endfor
  comment_with_label "EXIT: timestep" (a,b,r) ("a","b","r")
  return ()

main = print_generic Preview circuit (nodeshape, nodeshape, qubit)
  where
    circuit (a, b, r) = timestep (a, b, r, dt, m)
    n = 4
    m = n+2
    dt = pi/180
    nodeshape = qureg_shape m
