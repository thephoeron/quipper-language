-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper

import QuipperLib.Qureg

-- | Algorithm 7. The arguments are of the form (/a/, /root/, /even/,
-- /n/). Precondition: /a/ is a quantum register of length at least
-- /n/+1.
parseNodeRoot :: (Qureg, Qubit, Qubit, Int) -> Circ ()
parseNodeRoot (a, root, even, n) = do
  comment_with_label "ENTER: parseNodeRoot" (a, root, even) ("a", "root", "even")
  with_ancilla_reg (n+1) $ \scratch -> do
    for n 1 (-1) $ \index -> do 
      with_controls (scratch.!(index) .==. 0 .&&. a.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index - 1))
      }
      with_controls (scratch.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index - 1))
      }
    endfor
    with_controls (scratch.!(0) .==. 0) $ do {
      qnot_at root;
      qnot_at even
    }
    for 1 n 1 $ \index -> do    
      with_controls (scratch.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index - 1))
      }
      with_controls (scratch.!(index) .==. 0 .&&. a.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index-1))
      }
    endfor
  comment_with_label "EXIT: parseNodeRoot" (a, root, even) ("a", "root", "even")
  return ()
      
main = print_generic Preview circuit (qureg_shape (n+1), qubit, qubit) 
  where
    circuit (a, root, even) = parseNodeRoot (a, root, even, n)
    n = 4
                                
