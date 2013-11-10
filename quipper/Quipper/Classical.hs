-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleContexts #-}

-- | This module provides some operations for low-level manipulation
-- of classical circuits. It is built directly on top of
-- "Quipper.Circuit".

module Quipper.Classical where

-- import other Quipper stuff
import Quipper.Generic
import Quipper.QData
import Quipper.Monad
import Quipper.Control
import Quipper.Transformer

-- import other stuff
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap

-- ======================================================================
-- * Manipulation of classical circuits

-- ----------------------------------------------------------------------
-- ** Eliminating CGate

-- | A 'Transformer' to eliminate all 'CGate' style gates, such as
-- \"and\", \"or\", \"not\", \"xor\", \"eq\", and \"if-then-else\"
-- gates, and replace them by equivalent 'CInit' and 'CNot' gates.
cgate_to_cnot_transformer :: Transformer Circ Qubit Bit
cgate_to_cnot_transformer (T_CGate name ncf f) = f $
  \qs -> without_controls_if ncf $ do
    q <- cinit False
    translate_cgate name q qs
    return (q, qs)
cgate_to_cnot_transformer (T_CGateInv name ncf f) = f $
  \q qs -> without_controls_if ncf $ do
    reverse_generic_imp (translate_cgate name) q qs
    cterm False q
    return qs
cgate_to_cnot_transformer gate = identity_transformer gate
  
-- | Auxiliary function: compute the reversible circuit corresponding
-- to a 'CGate' of the given name, using only controlled-not gates.
translate_cgate :: String -> Bit -> [Bit] -> Circ ()
translate_cgate "if" q [a,b,c] = do
  cnot_at q `controlled` a .==. True .&&. b .==. True
  cnot_at q `controlled` a .==. False .&&. c .==. True
translate_cgate "if" q list = do
  error ("translate_cgate: \"if\" needs 3 arguments, not " ++ show (length list))
translate_cgate "and" q list = do
  cnot_at q `controlled` list
translate_cgate "or" q list = do
  cnot_at q `controlled` [ x .==. 0 | x <- list]
  cnot_at q
translate_cgate "xor" q list = do
  sequence_ [cnot_at q `controlled` c | c <- list]
translate_cgate "eq" q [a,b] = do
  cnot_at q `controlled` a .==. True
  cnot_at q `controlled` b .==. False
translate_cgate "eq" q list = do
  error ("translate_cgate: \"eq\" needs 2 arguments, not " ++ show (length list))
translate_cgate "not" q [a] = do
  cnot_at q `controlled` a .==. False
translate_cgate "not" q list = do
  error ("translate_cgate: \"not\" needs 1 argument, not " ++ show (length list))
translate_cgate name q list = do
  error ("translate_cgate: gate \"" ++ name ++ "\" not known")
  
-- | Translate all classical gates in a circuit into equivalent
-- controlled-not gates.
-- 
-- The type of this overloaded function is difficult to read. In more
-- readable form, it has all of the following types:
-- 
-- > classical_to_cnot :: (QCData qa) => Circ qa -> Circ qa
-- > classical_to_cnot :: (QCData qa, QCData qb) => (qa -> Circ qb) -> (qa -> Circ qb)
-- > classical_to_cnot :: (QCData qa, QCData qb, QCData qc) => (qa -> qb -> Circ qc) -> (qa -> qb -> Circ qc)
-- 
-- and so forth.  
classical_to_cnot :: (QCData qa, QCData qb, QCurry qfun qa qb) => qfun -> qfun
classical_to_cnot = transform_generic cgate_to_cnot_transformer

-- ----------------------------------------------------------------------
-- ** Classical to quantum

-- | Map an endpoint to the underlying 'Qubit' in the trivial
-- case. Auxiliary function.
trivial_endpoint :: B_Endpoint Qubit Qubit -> Qubit
trivial_endpoint (Endpoint_Qubit q) = q
trivial_endpoint (Endpoint_Bit q) = q

-- | A 'Transformer' to replace all classical gates in a circuit by
-- equivalent quantum gates.
classical_to_quantum_transformer :: Transformer Circ Qubit Qubit

-- Classical gates.

classical_to_quantum_transformer (T_CNot ncf f) = f $
  \q c -> without_controls_if ncf $ do
    q' <- qnot q `controlled` c
    return (q', c)
classical_to_quantum_transformer (T_CSwap ncf f) = f $
  \w v c -> without_controls_if ncf $ do
    (w',v') <- swap w v `controlled` c
    return (w',v',c)
classical_to_quantum_transformer (T_CInit b ncf f) = f $
  without_controls_if ncf $ do
    w <- qinit b
    return w
classical_to_quantum_transformer (T_CTerm b ncf f) = f $
  \w -> without_controls_if ncf $ do
    qterm b w
    return ()
classical_to_quantum_transformer (T_CDiscard f) = f $
  \w -> do
    qdiscard w
    return ()
classical_to_quantum_transformer (T_DTerm b f) = f $
  \w -> do
    qdiscard w
    return ()
classical_to_quantum_transformer (T_CGate name ncf f) = f $
  -- This case is recursive. The well-foundedness rests on the fact
  -- that the output of classical_to_cnot contains no CGate. 
  classical_to_quantum . classical_to_cnot $
    \ws -> without_controls_if ncf $ do
      v <- cgate name ws
      return (v, ws)
classical_to_quantum_transformer (T_CGateInv name ncf f) = f $
  -- This case is recursive. The well-foundedness rests on the fact
  -- that the output of classical_to_cnot contains no CGate. 
  classical_to_quantum . classical_to_cnot $
    \v ws -> without_controls_if ncf $ do    
      cgateinv name v ws
      return ws

-- Preparation, unpreparation, and measurement. These become no-ops.

classical_to_quantum_transformer (T_QPrep ncf f) = f $
  \w -> return w
classical_to_quantum_transformer (T_QUnprep ncf f) = f $
  \w -> return w
classical_to_quantum_transformer (T_QMeas f) = f $    
  \w -> return w

-- Quantum gates. These are similar to the identity transformer.
-- However, we cannot explicitly call the identity transformer,
-- because its typing does not correctly translate 'Bit' to
-- 'Qubit'. This matters because a pure quantum gate may have
-- classical controls that need to be translated to quantum controls.
classical_to_quantum_transformer (T_QGate name _ _ inv ncf f) = f $
  \ws vs c -> without_controls_if ncf $ do
    (ws', vs') <- named_gate_qulist name inv ws vs `controlled` c
    return (ws', vs', c)
classical_to_quantum_transformer (T_QRot name _ _ inv t ncf f) = f $
  \ws vs c -> without_controls_if ncf $ do
    (ws', vs') <- named_rotation_qulist name inv t ws vs `controlled` c
    return (ws', vs', c)
classical_to_quantum_transformer (T_GPhase t ncf f) = f $
  \q c -> without_controls_if ncf $ do
    global_phase_anchored_list t (map fix_endpoint q) `controlled` c
    return c
      where
        fix_endpoint (Endpoint_Qubit q) = (Endpoint_Qubit q)
        fix_endpoint (Endpoint_Bit q) = (Endpoint_Qubit q)
classical_to_quantum_transformer (T_QInit b ncf f) = f $
  without_controls_if ncf $ do
    w <- qinit_qubit b
    return w
classical_to_quantum_transformer (T_QTerm b ncf f) = f $
  \w -> without_controls_if ncf $ do
    qterm_qubit b w
    return ()
classical_to_quantum_transformer (T_QDiscard f) = f $
  \w -> do
    qdiscard_qubit w
    return ()
classical_to_quantum_transformer (T_Subroutine n inv ncf scf ws_pat a1_pat vs_pat a2_pat repeat f) = f $
  \namespace ws c -> without_controls_if ncf $ do
    provide_subroutines namespace
    v <- subroutine n inv scf repeat ws_pat a1_pat vs_pat a2_pat (map fix_endpoint ws) `controlled` c
    return (map fix_endpoint v,c)
      where
        fix_endpoint (Endpoint_Qubit q) = Endpoint_Qubit q
        fix_endpoint (Endpoint_Bit q) = 
          error "classical_to_quantum: classical subroutine not permitted"
classical_to_quantum_transformer (T_Comment s inv f) = f $
  \ws -> do
    comment_label s inv [ (fix_endpoint e, s) | (e,s) <- ws ]
    return ()
      where
        fix_endpoint (Endpoint_Qubit q) = wire_of_qubit q
        fix_endpoint (Endpoint_Bit q) = wire_of_qubit q

-- | Replace all classical gates in a circuit by equivalent quantum gates.
classical_to_quantum_unary :: (QCData qa, QCData qb) => (qa -> Circ qb) -> (QType qa -> Circ (QType qb))
classical_to_quantum_unary f x = transform_unary_shape classical_to_quantum_transformer f shape x
  where
    shape = qcdata_makeshape (dummy :: qa) qubit qubit x

-- | Replace all classical gates in a circuit by equivalent quantum gates.
-- 
-- The type of this overloaded function is difficult to read. In more
-- readable form, it has all of the following types:
-- 
-- > classical_to_quantum :: (QCData qa) => Circ qa -> Circ (QType qa)
-- > classical_to_quantum :: (QCData qa, QCData qb) => (qa -> Circ qb) -> (QType qa -> Circ (QType qb))
-- > classical_to_quantum :: (QCData qa, QCData qb, QCData qc) => (qa -> qb -> Circ qc) -> (QType qa -> QType qb -> Circ (QType qc))
-- 
-- and so forth.  
classical_to_quantum :: (QCData qa, QCData qb, QCurry qfun qa qb, QCurry qfun' (QType qa) (QType qb)) => qfun -> qfun'
classical_to_quantum f = g where
  f1 = quncurry f
  g1 = classical_to_quantum_unary f1
  g = qcurry g1

-- ======================================================================
-- * Classical to reversible
  
-- | Generic function for turning a classical (or pseudo-classical)
-- circuit into a reversible circuit. The input is a classical boolean
-- function /x/ ↦ /f/(/x/), given as a not necessarily reversible
-- circuit (however, the circuit should be one-to-one, i.e., no
-- \"garbage\" should be explicitly erased). The output is the
-- corresponding reversible function (/x/,/y/) ↦ (/x/,/y/ ⊕
-- /f/(/x/)). /qa/ and /qb/ can be any quantum data types. The
-- function 'classical_to_reversible' does not itself change
-- classical bits to qubits; use 'classical_to_quantum' for that.

classical_to_reversible :: (QCData qa, QCData qb) => (qa -> Circ qb) -> ((qa,qb) -> Circ (qa,qb))
classical_to_reversible f (input, target) = do
  with_computed (f input) $ \output -> do
    controlled_not target output
    return (input, target)
