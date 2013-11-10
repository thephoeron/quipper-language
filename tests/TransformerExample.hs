-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper
  
mytransformer :: Transformer Circ Qubit Bit
mytransformer (T_QGate "swap" 2 0 _ ncf f) = f $
  \[q0, q1] [] ctrls -> do
    without_controls_if ncf $ do
      with_controls ctrls $ do
        qnot_at q0 `controlled` q1
        qnot_at q1 `controlled` q0
        qnot_at q0 `controlled` q1
        return ([q0, q1], [], ctrls)
mytransformer g = identity_transformer g

mycirc a b c d = do
  swap_at a b
  hadamard_at b
  swap_at b c `controlled` [a, d]
  hadamard_at c
  swap_at c d

mycirc2 = transform_generic mytransformer mycirc

main = print_simple Preview mycirc2
