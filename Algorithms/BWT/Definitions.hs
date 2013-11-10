-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides some convenient definitions for the Binary
-- Welded Tree algorithm implementation.

module Algorithms.BWT.Definitions where

import Quipper

-- ======================================================================
-- * Some convenient gates

-- | Apply the binary /W/-gate to a pair of qubits. The W-gate
-- diagonalizes the SWAP operation.
wGate :: (Qubit, Qubit) -> Circ ()
wGate (a,b) = do
  gate_W a b
  return ()

-- | Apply the /inverse/ of the /W/-gate. Note: since the /W/-gate is
-- self-inverse, this is really the same as 'wGate'. However, we
-- define this as a separate function for clarity. 
wGateInverse :: (Qubit, Qubit) -> Circ ()
wGateInverse = wGate

-- | Apply a doubly-controlled not gate to a triple of qubits (/a/,
-- /b/, /c/). Here the qubit /c/ is negated if /a/=1 and /b/=0.
toffoliGate :: (Qubit, Qubit, Qubit) -> Circ ()
toffoliGate (a, b, c) =
  qnot_at c `controlled` (a .==. 1 .&&. b .==. 0)

-- | @controlledExpGate(t, r, h):@
-- Apply the [exp −/iZt/] gate to the qubit /h/, provided that /r/=0. 
controlledExpGate :: (Timestep, Qubit, Qubit) -> Circ ()
controlledExpGate (t, r, h) = do
  expZt t h `controlled` (r .==. 0)
  return ()
