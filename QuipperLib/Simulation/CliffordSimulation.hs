-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | This module provides a Quipper interface to the efficient
-- simulation of Clifford group circuits, using the Stabilizer
-- formalism.
-- 
-- This module provides the internal implementation of the library,
-- and can be imported by other libraries. The public interface to
-- simulation is "QuipperLib.Simulation".

module QuipperLib.Simulation.CliffordSimulation where

import Quipper
import Quipper.Internal

-- The following is a bunch of stuff we need to import because,
-- temporarily, CliffordSimulation.hs uses low-level interfaces. It
-- should be re-implemented using only high-level interfaces, or in
-- some cases, more stuff should be exported from Quipper.hs.
import Quipper.Generic (encapsulate_generic, qc_unbind)
import Quipper.Transformer (transform_bcircuit_rec, bindings_empty)

import QuipperLib.Simulation.QuantumSimulation (gateQinv, rotQinv)
import QuipperLib.Simulation.ClassicalSimulation (simulate_cgate)

import Libraries.Auxiliary
import qualified Libraries.Stabilizers.Clifford as C

import Control.Monad.State (StateT)
import Data.Either

-- ----------------------------------------------------------------------
-- * The stabilizer transformer

-- | The stabilizer transformer. Used to transform a Quipper circuit,
-- made up of Clifford group operators, directly into the CliffordCirc
-- monad (where CliffordCirc is a type-synonym for StateT Tableau IO).
-- Note that this transformer only deals with 1 and 2-qubit operators.
stabilizer_transformer :: Transformer (StateT C.Tableau IO) C.Qubit Bool
stabilizer_transformer (T_QGate "not" 1 0 _ ncf f) = f $
  -- X and controlled-X are already provided by CliffordCirc
  \[qt] [] c -> case control_info c of
   None -> do
	C.gate_X qt
	return ([qt], [], c)
   Classical b -> do
	if b then C.gate_X qt else return ()
	return ([qt], [], c)
   OneQuantum (Signed qc negate) b -> do
	if negate then C.gate_X qc else return ()
	if b then C.controlled_X qc qt else return ()
	if negate then C.gate_X qc else return ()
	return ([qt], [], c)
   _ -> error "stabilizer_transformer: Toffoli gate not available"
stabilizer_transformer (T_QGate "multinot" _ 0 _ ncf f) = f $
  -- X and controlled-X are already provided by CliffordCirc
  -- and can be mapped over a list of qubits 
  \ws [] c -> case control_info c of
   None -> do
	mapM_ C.gate_X ws
	return (ws, [], c)
   Classical b -> do
	if b then mapM_ C.gate_X ws else return ()
	return (ws, [], c)
   OneQuantum (Signed qc negate) b -> do
	if negate then C.gate_X qc else return ()
	if b then mapM_ (C.controlled_X qc) ws else return ()
	if negate then C.gate_X qc else return ()
	return (ws, [], c)
   _ -> error "stabilizer_transformer: (Multi) Toffoli gate not available"
stabilizer_transformer (T_QGate "H" 1 0 _ ncf f) = f $
  -- Hadamard is already provided by CliffordCirc 
  \[qt] [] c -> case control_info c of
   None -> do
	C.gate_H qt
	return ([qt], [], c)
   Classical b -> do
	if b then C.gate_H qt else return ()
	return ([qt], [], c)
   -- TODO: ???
   _ -> error "stabilizer_transformer: controlled-Hadamard currently not supported"
stabilizer_transformer (T_QGate "swap" 2 0 _ ncf f) = f $
  -- (classically-controlled) swap is already provided by CliffordCirc
  \[w, v] [] c -> case control_info c of
    None -> do
          C.swap w v
          return ([w, v], [], [])
    Classical b -> do
          if b then C.swap w v else return ()
          return ([w, v], [], [])
    _ -> error "stabilizer_transformer: quantum controlled-swap not available"
stabilizer_transformer (T_QGate "W" 2 0 _ ncf f) = f $
  -- TODO: ???
  \[w, v] [] c -> error "stabilizer_transformer: W currently not supported"
stabilizer_transformer (T_QGate name _ _ inv ncf f) = f $
 \ws vs c ->
  case vs of
   [] ->
    case ws of
     [qt] -> case control_info c of
            None -> do
             C.gate_Unitary u1 qt
	     return ([qt], vs, c)
            Classical b -> do
             if b then C.gate_Unitary u1 qt else return ()
	     return ([qt], vs, c)
            OneQuantum (Signed qc negate) b -> do
             if b then C.gate_Unitary2 u2 qc qt else return ()
	     return ([qt], vs, c)
            _ -> error "stabilizer_transformer: Multiple quantum controls not supported"
      where u1 = case name of
		  "X" -> C.x
		  "Y" -> C.y
                  "Z" -> C.z
	          "S" -> C.s
	          "E" -> C.e
                  name -> C.from_matrix (gateQinv name inv)
            u2 = case name of
                  "X" -> C.cnot
                  "Z" -> C.cz
                  name -> C.from_matrix_controlled (gateQinv name inv)
     _ -> error "stabilizer_transformer: Named gates on multiple Qubits not available"
   _ -> error "stabilizer_transformer: generalised controls not currently supported"
stabilizer_transformer (T_QRot name _ _ inv t ncf f) = f $
  \ws vs c -> error "stabilizer_transformer: QRot not currently supported" --return (ws, vs, c)
stabilizer_transformer (T_GPhase t ncf f) = f $
  -- TODO: ???
  \qs c -> error "stabilizer_transformer: GPhase currently not supported"
stabilizer_transformer (T_CNot ncf f) = f $
  -- we can do a classical not depending on the controls
  \q c -> case control_info c of
           None -> return (not q,c)
           Classical b -> if b then return (not q,c) else return (q,c) 
           _ -> error "stabilizer_transformer: Quantum control on classical gate"
stabilizer_transformer (T_CGate name ncf f) = f $
  -- we can reuse the classical simulator cgate implementation
  \ws -> return (simulate_cgate name ws,ws)
stabilizer_transformer (T_CGateInv name ncf f) = f $
  -- we can check that the inverse is correct using the classical simulator cgate implementation
  \v ws -> if (simulate_cgate name ws == v) then return ws else error "stabilizer_transformer: CGateInv not inverse"
stabilizer_transformer (T_CSwap ncf f) = f $
  -- we can do a classical swap depending on the controls
  \w v c -> case control_info c of
             None -> return (w,v,c)
             Classical b -> if b then return (v,w,c) else return (w,v,c) 
             _ -> error "stabilizer_transformer: Quantum control on classical gate"
stabilizer_transformer (T_QPrep ncf f) = f $
  -- TODO: ??
  \w -> error "stabilizer_transformer: QPrep currently not supported"
stabilizer_transformer (T_QUnprep ncf f) = f $
 -- TODO: ??    
  \w -> error "stabilizer_transformer: QUnprep currently not supported"
stabilizer_transformer (T_QInit b ncf f) = f $
  -- initialization is already provided by CliffordCirc
  C.init_qubit b
stabilizer_transformer (T_CInit b ncf f) = f $
  -- initialisation of a boolean value
  return b
stabilizer_transformer (T_QTerm b ncf f) = f $
  -- we can check termination conditions at runtime, using measurement
  \w -> do
   res <- C.measure_qubit w
   if res == b then return () else error "stabilizer_transformer: QTerm condition failed"
stabilizer_transformer (T_CTerm b ncf f) = f $
  -- we can check termination conditions at runtime
  \w -> if w == b then return () else error "stabilizer_transformer: CTerm condition failed"
stabilizer_transformer (T_QMeas f) = f $
  -- measurement is already provided by CliffordCirc   
  \w -> C.measure_qubit w
stabilizer_transformer (T_QDiscard f) = f $
  -- we can ignore discards
  \w -> return ()
stabilizer_transformer (T_CDiscard f) = f $
  -- we can ignore discards
  \w -> return ()
stabilizer_transformer (T_DTerm b f) = f $
  -- TODO: ??
  \w -> error "stabilizer_transformer: DTerm currently not supported" --return ()
stabilizer_transformer (T_Subroutine n inv ncf scf ws_pat a1 vs_pat a2 rep f) = f $
  -- TODO: we can "open" subroutines
  \namespace ws c -> error "stabilizer_transformer: Subroutine currently not supported" --return (ws,c)
stabilizer_transformer (T_Comment s inv f) = f $
  -- we can ignore comments
  \ws -> return ()

-- | A datatype to represent controls that we can simulate
data ControlInfo = None | Classical Bool | OneQuantum (Signed C.Qubit) Bool | ManyQuantum

-- | Construct an element of ControlInfo from a list of Controls.
control_info :: Ctrls C.Qubit Bool -> ControlInfo
control_info cs = case split_controls cs of
  ([],[]) -> None
  ([],cs) -> Classical (all_equal cs)
  ([q],cs) -> OneQuantum q (all_equal cs)
  _ -> ManyQuantum
 where
  split_controls :: Ctrls a b -> ([Signed a],[Signed b])
  split_controls cs = partitionEithers (map either_control cs)
  either_control :: Signed (B_Endpoint a b) -> Either (Signed a) (Signed b)
  either_control (Signed (Endpoint_Qubit a) value) = Left (Signed a value)
  either_control (Signed (Endpoint_Bit b) value) = Right (Signed b value)
  all_equal :: [Signed Bool] -> Bool
  all_equal cs = and (map (\(Signed b val) -> b == val) cs) 

-- ----------------------------------------------------------------------
-- * High-level functions

-- | Use the 'stabilizer_transformer' to transform a Quipper circuit
-- into a 'CliffordCirc', ready for simulation.
toCliffordCirc :: (QCData qa, QCDataPlus qb) => (qa -> Circ qb) -> (BType qa -> C.CliffordCirc (BType qb))
toCliffordCirc (f :: qa -> Circ qb) input = do
  let ((), circuit, cb) = encapsulate_generic errmsg (\() -> qc_init input >>= \qi -> f qi >>= \qi' -> qc_measure qi') ()
  out_bind' <- transform_bcircuit_rec stabilizer_transformer circuit bindings_empty
  let out_bind = out_bind'
  let output = qc_unbind out_bind cb
  return output
    where
      errmsg x = ("simulate: " ++ x)

-- | Return the tableau resulting from simulating the given Quipper
-- circuit.
eval_unary :: (QCData qa, QCDataPlus qb) => (qa -> Circ qb) -> (BType qa -> IO C.Tableau)
eval_unary circ input = C.eval (toCliffordCirc circ input)

-- | Efficiently simulate a unary Quipper circuit that consists
-- entirely of Clifford group operators, using the stabilizer
-- formalism.
run_clifford_unary :: (QCData qa, QCDataPlus qb) => (qa -> Circ qb) -> (BType qa -> IO (BType qb))
run_clifford_unary circ input = C.sim (toCliffordCirc circ input)

-- | Efficiently simulate a Quipper circuit that consists entirely of
-- Clifford group operators, using the stabilizer formalism.  
-- 
-- Inputs a quantum circuit, and outputs a corresponding probabilistic
-- boolean function. The inputs to the quantum circuit are initialized
-- according to the given boolean arguments. The outputs of the
-- quantum circuit are measured, and the boolean measurement outcomes
-- are returned. Because the measurement outcomes are probabilistic,
-- this function takes place in the 'IO' monad.
-- 
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types (for
-- example):
-- 
-- > run_clifford_generic :: (QCData qa) => Circ qa -> IO (BType qa)
-- > run_clifford_generic :: (QCData qa, QCData qb) => (qa -> Circ qb) -> BType qa -> IO (BType qb)
-- > run_clifford_generic :: (QCData qa, QCData qb, QCData qc) => (qa -> qb -> Circ qc) -> BType qa -> BType qb -> IO (BType qc)
-- 
-- and so forth.
run_clifford_generic :: (QCData qa, QCDataPlus qb, QCurry qfun qa qb, Curry qfun' (BType qa) (IO (BType qb))) => qfun -> qfun'
run_clifford_generic f = g where
  f1 = quncurry f
  g1 = run_clifford_unary f1
  g = mcurry g1
