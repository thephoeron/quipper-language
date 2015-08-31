-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE Rank2Types #-}

-- | Functions to decompose circuits into various gate bases.  This
-- decompositions are \"legacy\". The 'Toffoli' and 'CliffordT'
-- decomposers contained here are being superseded by their
-- counterparts in "QuipperLib.Decompose.CliffordT".

module QuipperLib.Decompose.Legacy where

import Quipper
import Quipper.Internal

import QuipperLib.GateDecompositions

-- The following is a bunch of stuff we need to import because,
-- temporarily, Decompose.hs uses low-level interfaces. It should be
-- re-implemented using only high-level interfaces, or in some cases,
-- more stuff should be exported from Quipper.hs.
import Quipper.Circuit
import Quipper.Monad
import Quipper.Transformer (bindings_empty, bind_list, unbind_list, DynamicTransformer(..))
import Quipper.Generic (provide_subroutine_generic, transform_unary_dynamic)

import Control.Monad

-- ----------------------------------------------------------------------
-- * Legacy gatebase

-- | An enumeration type for the three gate bases handled by this
-- module.
data LegacyGateBase = GB_Toffoli | GB_Binary | GB_CliffordT
               deriving (Show)
-- ----------------------------------------------------------------------
-- * Helper functions

-- | Decompose quantum controls recursively until at most /n/ remain,
-- and then pass these reduced controls to the given circuit.
-- Precondition: /n/ ≥ 1.  The decomposition is done using Toffoli
-- gates, decomposed into the gate base. Classical controls are left
-- untouched.
-- 
-- For example, when /n/=2, this typically yields a circuit such as
-- the following (but with the Toffoli gates further decomposed into
-- the 'LegacyGateBase'):
-- 
-- \[image decompose2Controls.png]
--   
-- And for /n/=1, the circuit typically looks like this:
-- 
-- \[image decomposeControls.png]
with_combined_controls_gb :: LegacyGateBase -> Int -> [Signed Endpoint] -> ([Signed Qubit] -> Circ a) -> Circ a
with_combined_controls_gb GB_Toffoli = with_combined_controls toffoli_plain_at
with_combined_controls_gb GB_Binary = with_combined_controls toffoli_V_at
with_combined_controls_gb GB_CliffordT = with_combined_controls toffoli_AMMR_at

-- | Decompose a Toffoli gate into the given 'LegacyGateBase'. The controls
-- on the Toffoli gate may be positive or negative, as specified.
decomposeQToffoli :: LegacyGateBase -> Qubit -> (Signed Qubit, Signed Qubit) -> Circ ()
decomposeQToffoli GB_Toffoli q (c1, c2) = qnot_at q `controlled` [c1,c2]
decomposeQToffoli GB_Binary q (c1, c2) = do
  toffoli_V_at q c1 c2
decomposeQToffoli GB_CliffordT q3 (c1, c2) = do
  toffoli_AMMR_at q3 c1 c2

-- | The inverse of 'decomposeQToffoli'.
decomposeQToffoli_inv :: LegacyGateBase -> Qubit -> (Signed Qubit, Signed Qubit) -> Circ ()
decomposeQToffoli_inv gb = reverse_generic_imp (decomposeQToffoli gb)

-- | Implement a QMultinot gate in terms of QNot gates.
decomposeQMultinot :: [Qubit] -> Circ ()
decomposeQMultinot []  = return ()
decomposeQMultinot (q:qs)  = do
  qnot_at q
  decomposeQMultinot qs 

-- ----------------------------------------------------------------------
-- * Decomposition transformers
  
-- | A transformer to decompose a circuit into 'LegacyGateBase' gates. Note
-- that in the case of classically-controlled quantum gates, the
-- classical controls are unaffected.
decompose_transformer :: LegacyGateBase -> Transformer Circ Qubit Bit
decompose_transformer gb (T_QGate "not" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_combined_controls_gb gb 2 cs $ \qcs -> do
      case qcs of
        -- two controls
        [c1, c2] -> do
          decomposeQToffoli gb q (c1,c2)
          return ([q], [], cs)
        -- zero or one control
        qcs -> do
          qnot_at q `controlled` qcs
          return ([q], [], cs)
decompose_transformer gb (T_QGate "multinot" _ 0 _ ncf f) = f $
  \qs [] cs -> without_controls_if ncf $ do
    with_combined_controls_gb gb 1 cs $ \qcs -> do
      decomposeQMultinot qs `controlled` qcs
      return (qs, [], cs)
decompose_transformer gb (T_QGate "H" 1 0 _ ncf f) = f $ 
  \[q] [] cs -> without_controls_if ncf $ do
    with_combined_controls_gb gb 1 cs $ \qcs -> do
      hadamard q `controlled` qcs
      return ([q], [], cs)
decompose_transformer gb (T_QGate "swap" 2 0 _ ncf f) = f $
  \[q1, q2] [] cs -> without_controls_if ncf $ do
    with_combined_controls_gb gb 1 cs $ \qcs -> do
      case qcs of
        -- one control
        [c] -> do
          qnot_at q1 `controlled` q2
          decomposeQToffoli gb q2 (c,(Signed q1 True)) 
          qnot_at q1 `controlled` q2
          return ([q1, q2], [], cs)
        -- zero controls
        qcs -> do 
          swap_at q1 q2
          return ([q1, q2], [], cs)
decompose_transformer gb (T_QGate "W" 2 0 _ ncf f) = f $
  \[q1, q2] [] cs -> without_controls_if ncf $ do
    with_combined_controls_gb gb 1 cs $ \qcs -> do
      case qcs of
        -- one control
        [c] -> do 
          qnot q2 `controlled` q1
          w' <- qinit_qubit False
          decomposeQToffoli gb w' (c,(Signed q2 True))
          hadamard q1 `controlled` w'
          decomposeQToffoli_inv gb w' (c,(Signed q2 True))
          qterm_qubit False w' 
          qnot q2 `controlled` q1
          return ([q1, q2], [], cs)
        -- zero controls
        qcs -> do 
          gate_W q1 q2
          return ([q1, q2], [], cs)
decompose_transformer gb (T_QGate name _ _ inv ncf f) = f $
  \qs vs cs -> without_controls_if ncf $ do
    with_combined_controls_gb gb 1 cs $ \qcs -> do
      named_gate_qulist_at name inv qs vs `controlled` qcs
      return (qs, vs, cs)
decompose_transformer gb (T_QRot name _ _ inv theta ncf f) = f $
  \qs vs cs -> without_controls_if ncf $ do
    with_combined_controls_gb gb 1 cs $ \qcs -> do
      named_rotation_qulist_at name inv theta qs vs `controlled` qcs
      return (qs, vs, cs)
decompose_transformer gb (T_GPhase t ncf f) = f $
  \qs cs -> without_controls_if ncf $ do
    with_combined_controls_gb gb 1 cs $ \qcs -> do
      global_phase_anchored_list t qs `controlled` qcs
      return cs

-- The subroutine transformer clause is called when a subroutine gate appears, 
-- for now we decompose the controls just like for other gates. The recursive
-- decomposition of a subroutine is taken care of in the dynamic transformer.
decompose_transformer gb (T_Subroutine n inv ncf scf ws_pat a1 vs_pat a2 rep f) = f $
  \namespace ws cs -> without_controls_if ncf $ do
    let qws = [w | Endpoint_Qubit w <- ws]
    with_combined_controls_gb gb 1 cs $ \qcs -> do    
      provide_subroutines namespace
      case qcs of
        -- one control
        [c] -> if length qws /= length ws then error "Classical subroutine, used with quantum controls" else do
          vs <- subroutine n inv scf rep ws_pat a1 vs_pat a2 ws `controlled` c
          return (vs,cs)
        -- zero controls
        qcs -> do 
          vs <- subroutine n inv scf rep ws_pat a1 vs_pat a2 ws
          return (vs,cs)
-- We list catch-all cases explicitly, so that the type-checker can
-- warn about new gates that must be added to the list.
decompose_transformer gb gate@(T_CNot _ _) = identity_transformer gate
decompose_transformer gb gate@(T_CGate _ _ _) = identity_transformer gate
decompose_transformer gb gate@(T_CGateInv _ _ _) = identity_transformer gate
decompose_transformer gb gate@(T_CSwap _ _) = identity_transformer gate
decompose_transformer gb gate@(T_QPrep _ _) = identity_transformer gate
decompose_transformer gb gate@(T_QUnprep _ _) = identity_transformer gate
decompose_transformer gb gate@(T_QInit _ _ _) = identity_transformer gate
decompose_transformer gb gate@(T_CInit _ _ _) = identity_transformer gate
decompose_transformer gb gate@(T_QTerm _ _ _) = identity_transformer gate
decompose_transformer gb gate@(T_CTerm _ _ _) = identity_transformer gate
decompose_transformer gb gate@(T_QMeas _) = identity_transformer gate
decompose_transformer gb gate@(T_QDiscard _) = identity_transformer gate
decompose_transformer gb gate@(T_CDiscard _) = identity_transformer gate
decompose_transformer gb gate@(T_DTerm _ _) = identity_transformer gate
decompose_transformer gb gate@(T_Comment _ _ _) = identity_transformer gate

-- | Return a circuit producing function from a TypedSubroutine
open_subroutine :: TypedSubroutine -> [Endpoint] -> Circ [Endpoint]
open_subroutine (TypedSubroutine ocircuit _ _ scf) inputs = do
      let OCircuit (win, circuit, wout) = ocircuit
      when (length win /= length inputs) $ do
        error ("open_subroutine: subroutine has been applied to incorrect size of QCData")
      let in_bind = bind_list win inputs bindings_empty
      out_bind <- apply_circuit_with_bindings circuit in_bind
      let outputs = unbind_list out_bind wout
      return outputs

-- | Apply the decompose transformer to the given TypedSubroutine
-- Note: by default, set the classical-control flag to false.
decompose_subroutine :: LegacyGateBase -> BoxId -> TypedSubroutine -> Circ ()
decompose_subroutine gb boxid sub@(TypedSubroutine ocirc is os ctl) = do
  let circ = open_subroutine sub
  let circ' = decompose_legacy_unary gb circ
  let OCircuit (win, (arity,_,_,_), _) = ocirc
  let ein = endpoints_of_wires_in_arity arity win
  provide_subroutine_generic (\x -> "decompose_subroutine: " ++ x) boxid False circ' ein
		              
-- | A dynamic transformer variant of the decompose transformer
decompose_dynamic_transformer :: LegacyGateBase -> DynamicTransformer Circ Qubit Bit
decompose_dynamic_transformer gb = identity_dynamic_transformer {
  transformer = decompose_transformer gb,
  define_subroutine = decompose_subroutine gb}

-- ----------------------------------------------------------------------
-- * Generic decomposition

-- | Decompose a circuit into gates from the given 'LegacyGateBase'.
decompose_legacy_unary :: (QCData qa, QCData qb) => LegacyGateBase -> (qa -> Circ qb) -> (qa -> Circ qb)
decompose_legacy_unary gb circ = transform_unary_dynamic (decompose_dynamic_transformer gb) circ 
  
-- | Decompose a circuit into gates from the given 'LegacyGateBase'. Unlike
-- 'decompose_legacy_unary', this can be applied to a circuit-generating
-- function in curried form with /n/ arguments, for any /n/ ≥ 0.
-- 
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types:
-- 
-- > decompose_legacy_generic :: (QCData qa) => LegacyGateBase -> Circ qa -> Circ qa
-- > decompose_legacy_generic :: (QCData qa, QCData qb) => LegacyGateBase -> (qa -> Circ qb) -> (qa -> Circ qb)
-- > decompose_legacy_generic :: (QCData qa, QCData qb, QCData qc) => LegacyGateBase -> (qa -> qb -> Circ qc) -> (qa -> qb -> Circ qc)
-- 
-- and so forth.

decompose_legacy_generic :: (QCData qa, QCData qb, QCurry qfun qa qb) => LegacyGateBase -> qfun -> qfun
decompose_legacy_generic gatebase f = g where
  f1 = quncurry f
  g1 = decompose_legacy_unary gatebase f1
  g = qcurry g1

