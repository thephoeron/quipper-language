-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}

-- | This module provides transformers for decomposing circuits into
-- the Clifford+/T/ gate base.
-- 
-- * [bold Control trimming.] This transformer uses doubly-controlled
-- /iX/-gates to reduce the number of controls on gates. Specifically,
-- it ensures that not-gates, Pauli /X/-, /Y/-, and /Z/-gates, and
-- /iX/-gates have at most two controls; that phase gates of the form
-- Diag(1, φ) have no controls; and that all other gates have at most
-- one control.
-- 
-- * [bold Approximate Clifford+/T/ decomposition.] This decomposes
-- all rotation and phase gates into Clifford+/T/ up to a given
-- precision ε, using an approximate synthesis algorithm. Other gates
-- are unchanged.
-- 
-- * [bold Exact Clifford+/T/ decomposition.] This decomposes all
-- gates that are exactly representable in the Clifford+/T/ base into
-- single-qubit Clifford gates, /T/, /T/[sup †], and singly-controlled
-- not-gates (with positive or negative control). Rotation and phase
-- gates are left unchanged.
-- 
-- * [bold Standard gate set.] We define the standard gate set to
-- consist of the gates /X/, /Y/, /Z/, /H/, /S/, /S/[sup †], /T/,
-- /T/[sup †], and /CNOT/. This transformer decomposes all gates that
-- remain after applying both approximate and exact Clifford+/T/
-- decomposition into the standard gate set. If the transformer
-- encounters gates that are not single-qubit Clifford gates, /T/,
-- /T/[sup †], or singly-controlled not-gates (with positive or
-- negative control), then the output is still semantically correct,
-- but may not be in the standard gate set.  This transformer
-- suppresses global phases.
-- 
-- * [bold Strict gate set.] We define the strict gate set to consist
-- of the gates /H/, /S/, /T/, and /CNOT/. This transformer decomposes
-- all gates that remain after applying both approximate and exact
-- Clifford+/T/ decomposition into the strict gate set. If the
-- transformer encounters gates that are not single-qubit Clifford
-- gates, /T/, /T/[sup †], or singly-controlled not-gates (with
-- positive or negative control), then the output is still
-- semantically correct, but may not be in the strict gate set. This
-- transformer suppresses global phases.
-- 
-- These above transformers may be applied in any order. Control
-- trimming is primarily for demonstration purposes; it does not need
-- to be combined with the other transformers as they do their own
-- trimming. The exact and approximate Clifford+/T/ decompositions can
-- be applied in either order; since they each target a different set
-- of gates, they must both be performed to obtain a complete
-- decomposition into the Clifford+/T/ gate set. The standard and
-- strict transformers assume that their input has already been
-- pre-processed by the exact and approximate transformers.

module QuipperLib.Decompose.CliffordT where

import Quipper
import Quipper.Internal

-- Stuff we need to import because the Dynamic Transformer interface
-- is not yet stable.
import Quipper.Circuit (BoxId, TypedSubroutine(..), OCircuit(..))
import Quipper.Transformer
import Quipper.Generic (provide_subroutine_generic, transform_unary_dynamic)
import Quipper.Monad (endpoints_of_wires_in_arity, identity_dynamic_transformer, provide_subroutines, named_rotation_qulist_at, named_gate_qulist_at, subroutine)

import QuipperLib.Decompose.Legacy
import QuipperLib.GateDecompositions
import QuipperLib.Synthesis

import Libraries.Auxiliary (optional)
import Libraries.Synthesis.SymReal

import Control.Monad (when)
import System.Random
import Text.Printf

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | A version of 'with_combined_controls' that uses doubly-controlled
-- /iX/-gates to do the decomposition.  For example, when /n/=2, this
-- yields circuits such as the following:
-- 
-- \[image with_combined_controls2.png]
--   
-- And for /n/=1:
-- 
-- \[image with_combined_controls1.png]
with_combined_controls_iX :: Int -> [Signed Endpoint] -> ([Signed Qubit] -> Circ a) -> Circ a
with_combined_controls_iX = with_combined_controls cc_iX_plain_at

-- | A version of 'with_combined_controls_iX' that further decomposes
-- the doubly-controlled /iX/-gates into the Clifford+/T/ gate base.
with_combined_controls_CT :: Int -> [Signed Endpoint] -> ([Signed Qubit] -> Circ a) -> Circ a
with_combined_controls_CT = with_combined_controls cc_iX_at

-- | Turn a list of signed controls into a list of positive quantum
-- controls, by applying all classical controls directly, and
-- conjugating any negative quantum controls by /X/. Call the
-- inner block with those quantum controls. Usage:
-- 
-- > with_normalized_controls ctrls $ \qs -> do
-- >   <<<code using qs>>>
with_normalized_controls :: [Signed Endpoint] -> ([Qubit] -> Circ a) -> Circ a
with_normalized_controls cs f = do
  let (qcs, ccs) = partition_controls cs
  with_controls ccs $ do
    aux qcs []
    
  where
    aux [] qs = f (reverse qs)
    aux (qc:qcs) qs = do
      with_signed_qubit qc $ \q -> do
        aux qcs (q:qs)

-- | Like 'with_normalized_controls', but use /HSSH/ instead of /X/,
-- so as not to leave the /H/, /S/, /T/, /CNot/ gate base. 
with_normalized_controls_HS :: [Signed Endpoint] -> ([Qubit] -> Circ a) -> Circ a
with_normalized_controls_HS cs f = do
  let (qcs, ccs) = partition_controls cs
  with_controls ccs $ do
    aux qcs []
    
  where
    aux [] qs = f (reverse qs)
    aux (qc:qcs) qs = do
      with_signed_qubit_HS qc $ \q -> do
        aux qcs (q:qs)
    with_signed_qubit_HS (Signed q True) f = f q
    with_signed_qubit_HS (Signed q False) f = do
      hadamard_at q
      gate_S_at q
      gate_S_at q
      hadamard_at q
      b <- f q
      hadamard_at q
      gate_S_at q
      gate_S_at q
      hadamard_at q
      return b

-- | Negate the number if the boolean is true.
negate_if :: (Num r) => Bool -> r -> r
negate_if False x = x
negate_if True x = -x

-- ----------------------------------------------------------------------
-- * Transformers

-- ----------------------------------------------------------------------
-- ** Control trimming

-- | This transformer makes sure that not-gates, Pauli /X/-, /Y/-, and
-- /Z/-gates, and /iX/-gates have at most two controls; that phase
-- gates of the form Diag(1, φ) have no controls; and that all other
-- gates have at most one control.
trimcontrols_transformer :: Transformer Circ Qubit Bit
trimcontrols_transformer (T_QGate "not" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_combined_controls_iX 2 cs $ \qcs -> do
      qnot_at q `controlled` qcs
      return ([q], [], cs)
trimcontrols_transformer (T_QGate "multinot" _ 0 _ ncf f) = f $
  \qs [] cs -> without_controls_if ncf $ do
    with_combined_controls_iX 1 cs $ \qcs -> do
      qmultinot qs `controlled` qcs
      return (qs, [], cs)
trimcontrols_transformer (T_QGate "H" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_combined_controls_iX 1 cs $ \qcs -> do
      hadamard q `controlled` qcs
      return ([q], [], cs)
trimcontrols_transformer (T_QGate "swap" 2 0 _ ncf f) = f $
  \[q1, q2] [] cs -> without_controls_if ncf $ do
    with_combined_controls_iX 1 cs $ \qcs -> do
      swap_at q1 q2 `controlled` qcs
      return ([q1, q2], [], cs)
trimcontrols_transformer (T_QGate "W" 2 0 _ ncf f) = f $
  \[q1, q2] [] cs -> without_controls_if ncf $ do
    with_combined_controls_iX 1 cs $ \qcs -> do
      gate_W_at q1 q2 `controlled` qcs
      return ([q1, q2], [], cs)
trimcontrols_transformer gate@(T_QGate name _ _ inv ncf f) = f $
  \qs gctls cs -> without_controls_if ncf $ do
    let n = case (name, qs, gctls) of
          -- certain gates are allowed two controls
          ("X", [q], []) -> 2
          ("Y", [q], []) -> 2
          ("Z", [q], []) -> 2
          ("iX", [q], []) -> 2
          _ -> 1
    with_combined_controls_iX n cs $ \qcs -> do
      named_gate_qulist_at name inv qs gctls `controlled` qcs
      return (qs,gctls,cs)
trimcontrols_transformer (T_GPhase t ncf f) = f $
  \qs cs -> without_controls_if ncf $ do
    with_combined_controls_iX 1 cs $ \qcs -> do
      global_phase_anchored t qs `controlled` qcs
      return cs
trimcontrols_transformer gate@(T_QRot name _ _ inv theta ncf f) = f $
  \qs gctls cs -> without_controls_if ncf $ do
    let n = case (name, qs, gctls) of
          -- certain gates are decomposed to zero controls
          ("R(2pi/%)", [q], []) -> 0
          ("T(%)", [q], []) -> 0
          _ -> 1
    case n of
      0 -> do
        let [q] = qs
        with_combined_controls_iX 1 (Signed (Endpoint_Qubit q) True : cs) $ \qcs -> do
          let [c] = qcs
          with_signed_qubit c $ \q -> do
            named_rotation_qulist_at name inv theta [q] gctls
            return (qs,gctls,cs)
      _ -> do
        with_combined_controls_iX 1 cs $ \qcs -> do
          named_rotation_qulist_at name inv theta qs gctls `controlled` qcs
          return (qs,gctls,cs)

-- The subroutine transformer clause is called when a subroutine gate appears,
-- for now we decompose the controls just like for other gates. The recursive
-- decomposition of a subroutine is taken care of in the dynamic transformer.
trimcontrols_transformer (T_Subroutine n inv ncf scf ws_pat a1 vs_pat a2 rep f) = f $
  \namespace ws cs -> without_controls_if ncf $ do
    let qws = [w | Endpoint_Qubit w <- ws]
    provide_subroutines namespace
    with_combined_controls_iX 1 cs $ \qcs -> do
      vs <- subroutine n inv scf rep ws_pat a1 vs_pat a2 ws `controlled` qcs
      return (vs,cs)

-- We list catch-all cases explicitly, so that the type-checker can
-- warn about new gates that must be added to the list.
trimcontrols_transformer gate@(T_CNot _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_CGate _ _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_CGateInv _ _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_CSwap _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_QPrep _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_QUnprep _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_QInit _ _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_CInit _ _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_QTerm _ _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_CTerm _ _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_QMeas _) = identity_transformer gate
trimcontrols_transformer gate@(T_QDiscard _) = identity_transformer gate
trimcontrols_transformer gate@(T_CDiscard _) = identity_transformer gate
trimcontrols_transformer gate@(T_DTerm _ _) = identity_transformer gate
trimcontrols_transformer gate@(T_Comment _ _ _) = identity_transformer gate

-- ----------------------------------------------------------------------
-- ** Approximate Clifford+/T/ decomposition

-- | This transformer decomposes rotation and phase gates into the
-- Clifford+/T/ basis, using the approximate synthesis algorithm of
-- <http://arxiv.org/abs/1212.6253>. Other gates
-- are unchanged. 
-- 
-- This transformer requires a precision parameter, as well as a
-- source of randomness. The 'KeepPhase' flag indicates whether to
-- respect global phases.
approx_ct_transformer :: (RandomGen g) => KeepPhase -> Precision -> g -> Transformer Circ Qubit Bit
approx_ct_transformer kp prec g gate@(T_GPhase t ncf f) = f $
  \qs cs -> without_controls_if ncf $ do
    comment_with_label (printf "ENTER: GPhase (t=%f)" t) cs "c"
    with_combined_controls_iX 1 cs $ \qcs -> do
      case qcs of
        [] -> approximate_synthesis_phase kp prec theta g
          where
            theta = pi * to_real t
        [c] -> do
          with_signed_qubit c $ \q -> do
            approximate_synthesis_phase_ctrl kp prec theta g q
            return ()
          where
            theta = pi * to_real t
        _ -> error ("approx_ct_transformer: internal error. " ++ show gate)
      comment_with_label "EXIT: GPhase" cs "c"
      return cs
approx_ct_transformer kp prec g gate@(T_QRot name _ _ inv t ncf f) = f $
  \qs gctls cs -> without_controls_if ncf $ do
    comment_with_label (printf "ENTER: %s%s (t=%f)" name (optional inv "*") t) (qs,cs) ("q","c")
    case (name, inv, qs, gctls) of
        ("exp(-i%Z)", inv, [q], []) -> do
          with_combined_controls_iX 1 cs $ \qcs -> do
            case qcs of
              [] -> do
                approximate_synthesis_zrot prec theta g q
                return ()
                where
                  theta = negate_if inv (2 * to_real t)
              [c] -> do 
                with_signed_qubit c $ \q2 -> do
                  approximate_synthesis_zrot_ctrl prec theta g q q2
                  return ()
                where
                  theta = negate_if inv (2 * to_real t)
              _ -> error ("approx_ct_transformer: internal error. " ++ show gate)

        ("exp(% pi i)", inv, [q], []) -> do
          with_combined_controls_iX 1 cs $ \qcs -> do
            case qcs of
              [] -> do
                approximate_synthesis_phase kp prec theta g
                return ()
                where
                  theta = negate_if inv (to_real (pi*t))
              [c] -> do
                with_signed_qubit c $ \q2 -> do
                  approximate_synthesis_phase_ctrl kp prec theta g q2
                  return ()
                where
                  theta = negate_if inv (to_real (pi*t))
              _ -> error ("approx_ct_transformer: internal error. " ++ show gate)

        ("R(2pi/%)", inv, [q], []) -> do
          with_combined_controls_iX 1 (Signed (Endpoint_Qubit q) True : cs) $ \qcs -> do
            case qcs of
              [] -> do
                approximate_synthesis_phase kp prec theta g
                return ()
                where
                  theta = negate_if inv (2 * pi / to_real t)
              [c] -> do
                with_signed_qubit c $ \q1 -> do
                  approximate_synthesis_phase_ctrl kp prec theta g q1
                  return ()
                where
                  theta = negate_if inv (2 * pi / to_real t)
              _ -> error ("approx_ct_transformer: internal error. " ++ show gate)

        ("T(%)", inv, [q], []) -> do
          with_combined_controls_iX 1 (Signed (Endpoint_Qubit q) True : cs) $ \qcs -> do
            case qcs of
              [] -> do
                approximate_synthesis_phase kp prec theta g
                return ()
                where
                  theta = negate_if inv (-to_real t)
              [c] -> do
                with_signed_qubit c $ \q1 -> do
                  approximate_synthesis_phase_ctrl kp prec theta g q1
                  return ()
                where
                  theta = negate_if inv (-to_real t)
              _ -> error ("approx_ct_transformer: internal error. " ++ show gate)

        ("G(%)", inv, [q], []) -> do
          with_combined_controls_iX 1 cs $ \qcs -> do
            case qcs of
              [] -> do
                approximate_synthesis_phase kp prec theta g
                return ()
                where
                  theta = negate_if inv (-to_real t)
              [c] -> do
                with_signed_qubit c $ \q2 -> do
                  approximate_synthesis_phase_ctrl kp prec theta g q2
                  return ()
                where
                  theta = negate_if inv (-to_real t)
              _ -> error ("approx_ct_transformer: internal error. " ++ show gate)

        ("Rz(%)", inv, [q], []) -> do
          with_combined_controls_iX 1 cs $ \qcs -> do
            case qcs of
              [] -> do
                approximate_synthesis_zrot prec theta g q
                return ()
                where
                  theta = negate_if inv (to_real t)
              [c] -> do
                with_signed_qubit c $ \q2 -> do
                  approximate_synthesis_zrot_ctrl prec theta g q q2
                  return ()
                where
                  theta = negate_if inv (to_real t)
              _ -> error ("approx_ct_transformer: internal error. " ++ show gate)

        _ -> error ("approx_ct_transformer: unimplemented gate: " ++ show gate)
    comment_with_label (printf "EXIT: %s%s (t=%f)" name (optional inv "*") t) (qs,cs) ("q","c")
    return (qs, gctls, cs)
approx_ct_transformer kp prec g gate = identity_transformer gate

-- ----------------------------------------------------------------------
-- ** Exact Clifford+/T/ decomposition

-- | This transformer decomposes all gates that permit exact
-- Clifford+/T/ representations into the following concrete gate base
-- for Clifford+/T/:
-- 
-- * controlled-not (with one positive or negative control),
-- 
-- * any single-qubit Clifford gates,
-- 
-- * /T/ and /T/[sup †].
-- 
-- Classical controls and classical gates are not subject to the gate
-- base, and are left untouched.
-- 
-- Rotations and phase gates are left unchanged by this transformer,
-- but any controls on those gates will be decomposed. 
exact_ct_transformer :: Transformer Circ Qubit Bit
exact_ct_transformer gate@(T_QGate "not" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_combined_controls_CT 2 cs $ \qcs -> do
      case qcs of
        [] -> do
          gate_X_at q
        [c1,c2] -> do
          toffoli_AMMR_at q c1 c2
        qcs -> do
          qnot_at q `controlled` qcs          
    return ([q], [], cs)
exact_ct_transformer gate@(T_QGate "multinot" _ 0 _ ncf f) = f $
  \qs [] cs -> without_controls_if ncf $ do
    with_combined_controls_CT 1 cs $ \qcs -> do
      case qcs of
        [] -> do
          sequence_ [ gate_X_at q | q <- qs ]
        qcs -> do
          sequence_ [ qnot_at q | q <- qs ] `controlled` qcs
    return (qs, [], cs)
exact_ct_transformer gate@(T_QGate "H" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_combined_controls_CT 1 cs $ \qcs -> do
      case qcs of
        [c] -> do
          cH_AMMR_at q c
        qcs -> do
          hadamard_at q `controlled` qcs
    return ([q], [], cs)
exact_ct_transformer gate@(T_QGate "swap" 2 0 _ ncf f) = f $
  \[q1, q2] [] cs -> without_controls_if ncf $ do
    with_combined_controls_CT 1 cs $ \qcs -> do
      case qcs of
        [c] -> do
          fredkin_at q1 q2 c
        qcs -> do
          swap_at q1 q2 `controlled` qcs
    return ([q1, q2], [], cs)
exact_ct_transformer gate@(T_QGate "W" 2 0 _ ncf f) = f $
  \[q1, q2] [] cs -> without_controls_if ncf $ do
    with_combined_controls_CT 1 cs $ \qcs -> do
      case qcs of
        [c] -> do
          controlled_W_at q1 q2 c
        qcs -> do
          gate_W_CliffordT_at q1 q2 `controlled` qcs
      return ([q1, q2], [], cs)
exact_ct_transformer gate@(T_QGate name _ _ inv ncf f) = f $
  \qs gctls cs -> without_controls_if ncf $ do
    let n = case (name, qs, gctls) of
          -- certain gates are allowed two controls
          ("X", [q], []) -> 2
          ("Y", [q], []) -> 2
          ("Z", [q], []) -> 2
          ("iX", [q], []) -> 2
          _ -> 1
    with_combined_controls_CT n cs $ \qcs -> do
      case (name, qs, gctls, qcs) of
        
        ("X", [q], [], [c1, c2]) -> do
          toffoli_AMMR_at q c1 c2
        ("X", [q], [], [c]) -> do
          qnot_at q `controlled` c
        ("X", [q], [], []) -> do
          gate_X_at q
        
        ("Y", [q], [], [c1, c2]) -> do
          gate_S_inv_at q
          toffoli_AMMR_at q c1 c2
          gate_S_at q
        ("Y", [q], [], [c]) -> do
          gate_S_inv_at q
          qnot_at q `controlled` c
          gate_S_at q
        ("Y", [q], [], []) -> do
          gate_Y_at q
          
        ("Z", [q], [], [c1, c2]) -> do
          ccZ_AMMR_at q c1 c2
        ("Z", [q], [], [c]) -> do
          hadamard_at q
          qnot_at q `controlled` c
          hadamard_at q
        ("Z", [q], [], []) -> do
          gate_Z_at q
          
        ("iX", [q], [], [c1, c2]) -> do
          reverse_imp_if inv cc_iX_at q c1 c2
        ("iX", [q], [], [c]) -> do
          reverse_imp_if inv controlled_iX_at q c
        ("iX", [q], [], []) -> 
          reverse_imp_if inv gate_iX_at q
          
        ("S", [q], [], [c]) -> do
          reverse_imp_if inv controlled_S_at q c
        ("S", [q], [], []) -> do
          reverse_imp_if inv gate_S_at q
          
        ("T", [q], [], [c]) -> do
          reverse_imp_if inv controlled_T_at q c
        ("T", [q], [], []) -> do
          reverse_imp_if inv gate_T_at q
          
        ("V", [q], [], [c]) -> do
          reverse_imp_if inv controlled_V_at q c
        ("V", [q], [], []) -> do
          reverse_imp_if inv gate_V_at q
          
        ("E", [q], [], [c]) -> do
          reverse_imp_if inv controlled_E_at q c
        ("E", [q], [], []) -> do
          reverse_imp_if inv gate_E_at q
          
        ("YY", [q], [], [c]) -> do
          reverse_imp_if inv controlled_YY_at q c
        ("YY", [q], [], []) -> do
          reverse_imp_if inv (named_gate_at "YY") q
          
        ("omega", [q], [], [c]) -> do
          with_signed_qubit c $ \c1 -> do
            reverse_imp_if inv gate_T_at c1
        ("omega", [q], [], []) -> do
          reverse_imp_if inv gate_omega_at q
            
        _ -> error ("exact_ct_transformer: gate not implemented: " ++ show gate)
    return (qs,gctls,cs)

-- We list catch-all cases explicitly, so that the type-checker can
-- warn about new gates that must be added to the list.
exact_ct_transformer gate@(T_GPhase _ _ _) = identity_transformer gate
exact_ct_transformer gate@(T_QRot _ _ _ _ _ _ _) = identity_transformer gate
exact_ct_transformer gate@(T_Subroutine _ _ _ _ _ _ _ _ _ _) = identity_transformer gate
exact_ct_transformer gate@(T_CNot _ _) = identity_transformer gate
exact_ct_transformer gate@(T_CGate _ _ _) = identity_transformer gate
exact_ct_transformer gate@(T_CGateInv _ _ _) = identity_transformer gate
exact_ct_transformer gate@(T_CSwap _ _) = identity_transformer gate
exact_ct_transformer gate@(T_QPrep _ _) = identity_transformer gate
exact_ct_transformer gate@(T_QUnprep _ _) = identity_transformer gate
exact_ct_transformer gate@(T_QInit _ _ _) = identity_transformer gate
exact_ct_transformer gate@(T_CInit _ _ _) = identity_transformer gate
exact_ct_transformer gate@(T_QTerm _ _ _) = identity_transformer gate
exact_ct_transformer gate@(T_CTerm _ _ _) = identity_transformer gate
exact_ct_transformer gate@(T_QMeas _) = identity_transformer gate
exact_ct_transformer gate@(T_QDiscard _) = identity_transformer gate
exact_ct_transformer gate@(T_CDiscard _) = identity_transformer gate
exact_ct_transformer gate@(T_DTerm _ _) = identity_transformer gate
exact_ct_transformer gate@(T_Comment _ _ _) = identity_transformer gate


-- ----------------------------------------------------------------------
-- ** Decomposition into standard gate set

-- | This transformer decomposes a circuit into the standard gate set,
-- which we define to be:
-- 
-- * /X/, /Y/, /Z/, /H/, /S/, /S/[sup †], /T/, /T/[sup †], and /CNOT/.
-- 
-- As a precondition, the input circuit must only contain the
-- following gates:
-- 
-- * controlled-not (with one positive or negative control),
-- 
-- * any single-qubit Clifford gates,
-- 
-- * /T/ and /T/[sup †].
-- 
-- Global phases are suppressed. Classical controls and classical
-- gates are not subject to the gate base, and are left untouched.
-- 
-- Any gates that are not among the input gates listed above will be
-- transformed to a semantically correct circuit which may, however,
-- contain gates that are not in the standard gate set. The best way
-- to avoid this is to apply exact and approximate Clifford+/T/
-- decomposition first.
standard_transformer :: Transformer Circ Qubit Bit
standard_transformer gate@(T_QGate "H" 1 0 _ _ _) = identity_transformer gate
standard_transformer gate@(T_QGate "Y" 1 0 _ ncf f) = identity_transformer gate
standard_transformer gate@(T_QGate "Z" 1 0 _ ncf f) = identity_transformer gate
standard_transformer gate@(T_QGate "S" 1 0 _ ncf f) = identity_transformer gate
standard_transformer gate@(T_QGate "T" 1 0 _ ncf f) = identity_transformer gate
standard_transformer gate@(T_QGate "multinot" _ _ _ _ _) = identity_transformer gate
standard_transformer gate@(T_QGate "swap" 2 0 _ _ _) = identity_transformer gate
standard_transformer gate@(T_QGate "W" 2 0 _ _ _) = identity_transformer gate

standard_transformer gate@(T_QGate "not" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_normalized_controls cs $ \qs -> do
      case qs of
        [] -> do
          gate_X_at q
        qs -> qnot_at q `controlled` qs
    return ([q], [], cs)

standard_transformer gate@(T_QGate "X" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_normalized_controls cs $ \qcs -> do
      case qcs of
        [] -> do
          gate_X_at q
        qcs -> do
          qnot_at q `controlled` qcs
    return ([q],[],cs)

standard_transformer gate@(T_QGate "iX" 1 0 inv ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_normalized_controls cs $ \qcs -> do
      case qcs of
        [] -> do
          gate_X_at q
        qcs -> do
          reverse_imp_if inv gate_iX_at q `controlled` qcs
    return ([q],[],cs)

standard_transformer gate@(T_QGate "V" 1 0 inv ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      hadamard_at q
      reverse_imp_if inv gate_S_inv_at q
      hadamard_at q
    return ([q],[],cs)

standard_transformer gate@(T_QGate "E" 1 0 False ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      hadamard_at q
      gate_S_inv_at q
    return ([q],[],cs)
standard_transformer gate@(T_QGate "E" 1 0 True ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      gate_S_at q
      hadamard_at q
    return ([q],[],cs)

standard_transformer gate@(T_QGate "YY" 1 0 inv ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      reverse_imp_if inv gate_S_at q
      hadamard_at q
      reverse_imp_if inv gate_S_at q
    return ([q],[],cs)

standard_transformer gate@(T_QGate "omega" 1 0 _ ncf f) = f $
  \[q] [] cs -> 
    return ([q],[],cs)

standard_transformer gate@(T_QGate name _ _ inv ncf f) =     
  error ("standard_transformer: gate not implemented: " ++ show gate)

-- We list catch-all cases explicitly, so that the type-checker can
-- warn about new gates that must be added to the list.
standard_transformer gate@(T_QRot _ _ _ _ _ _ _) = identity_transformer gate
standard_transformer gate@(T_GPhase _ _ _) = identity_transformer gate
standard_transformer gate@(T_Subroutine _ _ _ _ _ _ _ _ _ _) = identity_transformer gate
standard_transformer gate@(T_CNot _ _) = identity_transformer gate
standard_transformer gate@(T_CGate _ _ _) = identity_transformer gate
standard_transformer gate@(T_CGateInv _ _ _) = identity_transformer gate
standard_transformer gate@(T_CSwap _ _) = identity_transformer gate
standard_transformer gate@(T_QPrep _ _) = identity_transformer gate
standard_transformer gate@(T_QUnprep _ _) = identity_transformer gate
standard_transformer gate@(T_QInit _ _ _) = identity_transformer gate
standard_transformer gate@(T_CInit _ _ _) = identity_transformer gate
standard_transformer gate@(T_QTerm _ _ _) = identity_transformer gate
standard_transformer gate@(T_CTerm _ _ _) = identity_transformer gate
standard_transformer gate@(T_QMeas _) = identity_transformer gate
standard_transformer gate@(T_QDiscard _) = identity_transformer gate
standard_transformer gate@(T_CDiscard _) = identity_transformer gate
standard_transformer gate@(T_DTerm _ _) = identity_transformer gate
standard_transformer gate@(T_Comment _ _ _) = identity_transformer gate

-- ----------------------------------------------------------------------
-- ** Decomposition into strict gate set

-- | This transformer decomposes a circuit into the strict gate set,
-- which we define to be:
-- 
-- * /H/, /S/, /T/, and /CNOT/.
-- 
-- As a precondition, the input circuit must only contain the
-- following gates:
-- 
-- * controlled-not (with one positive or negative control),
-- 
-- * any single-qubit Clifford gates,
-- 
-- * /T/ and /T/[sup †].
-- 
-- Global phases are suppressed. Classical controls and classical
-- gates are not subject to the gate base, and are left untouched.
-- 
-- Any gates that are not among the input gates listed above will be
-- transformed to a semantically correct circuit which may, however,
-- contain gates that are not in the strict gate set. The best way to
-- avoid this is to apply exact and approximate Clifford+/T/
-- decomposition first.
strict_transformer :: Transformer Circ Qubit Bit
strict_transformer gate@(T_QGate "H" 1 0 _ _ _) = identity_transformer gate
strict_transformer gate@(T_QGate "multinot" _ _ _ _ _) = identity_transformer gate
strict_transformer gate@(T_QGate "swap" 2 0 _ _ _) = identity_transformer gate
strict_transformer gate@(T_QGate "W" 2 0 _ _ _) = identity_transformer gate

strict_transformer gate@(T_QGate "not" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_normalized_controls_HS cs $ \qs -> do
      case qs of
        [] -> do
          hadamard_at q
          gate_S_at q
          gate_S_at q
          hadamard_at q
        qs -> qnot_at q `controlled` qs
    return ([q], [], cs)

strict_transformer gate@(T_QGate "X" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_normalized_controls_HS cs $ \qcs -> do
      case qcs of
        [] -> do
          hadamard_at q
          gate_S_at q
          gate_S_at q
          hadamard_at q
        qcs -> do
          qnot_at q `controlled` qcs
    return ([q],[],cs)

strict_transformer gate@(T_QGate "Y" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      gate_S_at q
      hadamard_at q
      gate_S_at q
      gate_S_at q
      hadamard_at q
      gate_S_at q
      gate_S_at q
      gate_S_at q
    return ([q],[],cs)

strict_transformer gate@(T_QGate "Z" 1 0 _ ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      gate_S_at q
      gate_S_at q
    return ([q],[],cs)

strict_transformer gate@(T_QGate "iX" 1 0 inv ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_normalized_controls_HS cs $ \qcs -> do
      case qcs of
        [] -> do
          hadamard_at q
          gate_S_at q
          gate_S_at q
          hadamard_at q
        qcs -> do
          reverse_imp_if inv gate_iX_at q `controlled` qcs
    return ([q],[],cs)

strict_transformer gate@(T_QGate "S" 1 0 False ncf f) = 
  identity_transformer gate
strict_transformer gate@(T_QGate "S" 1 0 True ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      gate_S_at q
      gate_S_at q
      gate_S_at q
    return ([q],[],cs)

strict_transformer gate@(T_QGate "T" 1 0 False ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      gate_T_at q
    return ([q],[],cs)
strict_transformer gate@(T_QGate "T" 1 0 True ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      gate_T_at q
      gate_S_at q
      gate_S_at q
      gate_S_at q
    return ([q],[],cs)

strict_transformer gate@(T_QGate "V" 1 0 False ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      hadamard_at q
      gate_S_at q
      gate_S_at q
      gate_S_at q
      hadamard_at q
    return ([q],[],cs)
strict_transformer gate@(T_QGate "V" 1 0 True ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      hadamard_at q
      gate_S_at q
      hadamard_at q
    return ([q],[],cs)

strict_transformer gate@(T_QGate "E" 1 0 False ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      hadamard_at q
      gate_S_at q
      gate_S_at q
      gate_S_at q
    return ([q],[],cs)
strict_transformer gate@(T_QGate "E" 1 0 True ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      gate_S_at q
      hadamard_at q
    return ([q],[],cs)

strict_transformer gate@(T_QGate "YY" 1 0 inv ncf f) = f $
  \[q] [] cs -> without_controls_if ncf $ do
    with_controls cs $ do
      when (inv) $ do
        gate_S_at q
        gate_S_at q
      gate_S_at q
      hadamard_at q
      gate_S_at q
      when (inv) $ do
        gate_S_at q
        gate_S_at q
    return ([q],[],cs)

strict_transformer gate@(T_QGate "omega" 1 0 _ ncf f) = f $
  \[q] [] cs -> 
    return ([q],[],cs)

strict_transformer gate@(T_QGate name _ _ inv ncf f) =     
  error ("strict_transformer: gate not implemented: " ++ show gate)

-- We list catch-all cases explicitly, so that the type-checker can
-- warn about new gates that must be added to the list.
strict_transformer gate@(T_QRot _ _ _ _ _ _ _) = identity_transformer gate
strict_transformer gate@(T_GPhase _ _ _) = identity_transformer gate
strict_transformer gate@(T_Subroutine _ _ _ _ _ _ _ _ _ _) = identity_transformer gate
strict_transformer gate@(T_CNot _ _) = identity_transformer gate
strict_transformer gate@(T_CGate _ _ _) = identity_transformer gate
strict_transformer gate@(T_CGateInv _ _ _) = identity_transformer gate
strict_transformer gate@(T_CSwap _ _) = identity_transformer gate
strict_transformer gate@(T_QPrep _ _) = identity_transformer gate
strict_transformer gate@(T_QUnprep _ _) = identity_transformer gate
strict_transformer gate@(T_QInit _ _ _) = identity_transformer gate
strict_transformer gate@(T_CInit _ _ _) = identity_transformer gate
strict_transformer gate@(T_QTerm _ _ _) = identity_transformer gate
strict_transformer gate@(T_CTerm _ _ _) = identity_transformer gate
strict_transformer gate@(T_QMeas _) = identity_transformer gate
strict_transformer gate@(T_QDiscard _) = identity_transformer gate
strict_transformer gate@(T_CDiscard _) = identity_transformer gate
strict_transformer gate@(T_DTerm _ _) = identity_transformer gate
strict_transformer gate@(T_Comment _ _ _) = identity_transformer gate


-- ----------------------------------------------------------------------
-- * Glue code for subroutines

-- $ The following is stuff we have to do because subroutines are not
-- yet handled very abstractly. It is untested whether subroutines
-- work at all.

-- | Handle subroutines for the 'trimcontrols_transformer'.
trimcontrols_subroutine :: BoxId -> TypedSubroutine -> Circ ()
trimcontrols_subroutine boxid sub@(TypedSubroutine ocirc is os ctl) = do
  let circ = open_subroutine sub
  let circ' = trimcontrols_unary circ
  let OCircuit (win, (arity,_,_,_), _) = ocirc
  let ein = endpoints_of_wires_in_arity arity win
  provide_subroutine_generic (\x -> "trimcontrols_subroutine: " ++ x) boxid False circ' ein

-- | Dynamic transformer for the 'trimcontrols_transformer'.
trimcontrols_dtransformer :: DynamicTransformer Circ Qubit Bit
trimcontrols_dtransformer = identity_dynamic_transformer {
  transformer = trimcontrols_transformer,
  define_subroutine = trimcontrols_subroutine}

-- | Unary transformer for the 'trimcontrols_transformer'.
trimcontrols_unary :: (QCData qa, QCData qb) => (qa -> Circ qb) -> (qa -> Circ qb)
trimcontrols_unary = transform_unary_dynamic trimcontrols_dtransformer

-- | Handle subroutines for the 'approx_ct_transformer'.
approx_ct_subroutine :: (RandomGen g) => KeepPhase -> Precision -> g -> BoxId -> TypedSubroutine -> Circ ()
approx_ct_subroutine kp prec g boxid sub@(TypedSubroutine ocirc is os ctl) = do
  let circ = open_subroutine sub
  let circ' = approx_ct_unary kp prec g circ
  let OCircuit (win, (arity,_,_,_), _) = ocirc
  let ein = endpoints_of_wires_in_arity arity win
  provide_subroutine_generic (\x -> "approx_ct_subroutine: " ++ x) boxid False circ' ein

-- | Dynamic transformer for the 'approx_ct_transformer'.
approx_ct_dtransformer :: (RandomGen g) => KeepPhase -> Precision -> g -> DynamicTransformer Circ Qubit Bit
approx_ct_dtransformer kp prec g = identity_dynamic_transformer {
  transformer = approx_ct_transformer kp prec g,
  define_subroutine = approx_ct_subroutine kp prec g}

-- | Unary transformer for the 'approx_ct_transformer'.
approx_ct_unary :: (RandomGen g, QCData qa, QCData qb) => KeepPhase -> Precision -> g -> (qa -> Circ qb) -> (qa -> Circ qb)
approx_ct_unary kp prec g = transform_unary_dynamic (approx_ct_dtransformer kp prec g)

-- | Handle subroutines for the 'exact_ct_transformer'.
exact_ct_subroutine :: BoxId -> TypedSubroutine -> Circ ()
exact_ct_subroutine boxid sub@(TypedSubroutine ocirc is os ctl) = do
  let circ = open_subroutine sub
  let circ' = exact_ct_unary circ
  let OCircuit (win, (arity,_,_,_), _) = ocirc
  let ein = endpoints_of_wires_in_arity arity win
  provide_subroutine_generic (\x -> "exact_ct_subroutine: " ++ x) boxid False circ' ein

-- | Dynamic transformer for the 'exact_ct_transformer'.
exact_ct_dtransformer :: DynamicTransformer Circ Qubit Bit
exact_ct_dtransformer = identity_dynamic_transformer {
  transformer = exact_ct_transformer,
  define_subroutine = exact_ct_subroutine}

-- | Unary transformer for the 'exact_ct_transformer'.
exact_ct_unary :: (QCData qa, QCData qb) => (qa -> Circ qb) -> (qa -> Circ qb)
exact_ct_unary = transform_unary_dynamic exact_ct_dtransformer

-- | Handle subroutines for the 'standard_transformer'.
standard_subroutine :: BoxId -> TypedSubroutine -> Circ ()
standard_subroutine boxid sub@(TypedSubroutine ocirc is os ctl) = do
  let circ = open_subroutine sub
  let circ' = standard_unary circ
  let OCircuit (win, (arity,_,_,_), _) = ocirc
  let ein = endpoints_of_wires_in_arity arity win
  provide_subroutine_generic (\x -> "standard_subroutine: " ++ x) boxid False circ' ein

-- | Dynamic transformer for the 'standard_transformer'.
standard_dtransformer :: DynamicTransformer Circ Qubit Bit
standard_dtransformer = identity_dynamic_transformer {
  transformer = standard_transformer,
  define_subroutine = standard_subroutine}

-- | Unary transformer for the 'standard_transformer'.
standard_unary :: (QCData qa, QCData qb) => (qa -> Circ qb) -> (qa -> Circ qb)
standard_unary = transform_unary_dynamic standard_dtransformer

-- | Handle subroutines for the 'strict_transformer'.
strict_subroutine :: BoxId -> TypedSubroutine -> Circ ()
strict_subroutine boxid sub@(TypedSubroutine ocirc is os ctl) = do
  let circ = open_subroutine sub
  let circ' = strict_unary circ
  let OCircuit (win, (arity,_,_,_), _) = ocirc
  let ein = endpoints_of_wires_in_arity arity win
  provide_subroutine_generic (\x -> "strict_subroutine: " ++ x) boxid False circ' ein

-- | Dynamic transformer for the 'strict_transformer'.
strict_dtransformer :: DynamicTransformer Circ Qubit Bit
strict_dtransformer = identity_dynamic_transformer {
  transformer = strict_transformer,
  define_subroutine = strict_subroutine}

-- | Unary transformer for the 'strict_transformer'.
strict_unary :: (QCData qa, QCData qb) => (qa -> Circ qb) -> (qa -> Circ qb)
strict_unary = transform_unary_dynamic strict_dtransformer

-- ----------------------------------------------------------------------
-- * Generic transformers

-- $ The following generic functions form the high-level interface to
-- these decomposition transformers. This is how the transformers
-- should be accessed by user code.

-- | This transformer makes sure that not-gates, Pauli /X/-, /Y/-, and
-- /Z/-gates, and /iX/-gates have at most two controls; that phase
-- gates of the form Diag(1, φ) have no controls; and that all other
-- gates have at most one control.
trimcontrols_generic :: (QCData qa, QCData qb, QCurry qfun qa qb) => qfun -> qfun
trimcontrols_generic f = h where
  f1 = quncurry f
  h1 = trimcontrols_unary f1
  h = qcurry h1

-- | This transformer decomposes rotation and phase gates into the
-- Clifford+/T/ basis, using the approximate synthesis algorithm of
-- <http://arxiv.org/abs/1212.6253>.  It requires a precision
-- parameter, as well as a source of randomness. Other gates
-- are unchanged.
approx_ct_generic :: (RandomGen g, QCData qa, QCData qb, QCurry qfun qa qb) => KeepPhase -> Precision -> g -> qfun -> qfun
approx_ct_generic kp prec g f = h where
  f1 = quncurry f
  h1 = approx_ct_unary kp prec g f1
  h = qcurry h1

-- | This transformer decomposes all gates that permit exact
-- Clifford+/T/ representations into the following concrete gate base
-- for Clifford+/T/:
-- 
-- * controlled-not (with one positive or negative control),
-- 
-- * any single-qubit Clifford gates,
-- 
-- * /T/ and /T/[sup †].
-- 
-- Classical controls and classical gates are not subject to the gate
-- base, and are left untouched.
-- 
-- Rotations and phase gates are left unchanged by this transformer,
-- but any controls on those gates will be decomposed. 
exact_ct_generic :: (QCData qa, QCData qb, QCurry qfun qa qb) => qfun -> qfun
exact_ct_generic f = h where
  f1 = quncurry f
  h1 = exact_ct_unary f1
  h = qcurry h1

-- | This transformer decomposes a circuit into the standard gate set,
-- which we define to be:
-- 
-- * /X/, /Y/, /Z/, /H/, /S/, /S/[sup †], /T/, /T/[sup †], and /CNOT/.
-- 
-- As a precondition, the input circuit must only contain the
-- following gates:
-- 
-- * controlled-not (with one positive or negative control),
-- 
-- * any single-qubit Clifford gates,
-- 
-- * /T/ and /T/[sup †].
-- 
-- Global phases are suppressed. Classical controls and classical
-- gates are not subject to the gate base, and are left untouched.
-- 
-- Any gates that are not among the input gates listed above will be
-- transformed to a semantically correct circuit which may, however,
-- contain gates that are not in the standard gate set. The best way
-- to avoid this is to apply exact and approximate Clifford+/T/
-- decomposition first.
standard_generic :: (QCData qa, QCData qb, QCurry qfun qa qb) => qfun -> qfun
standard_generic f = h where
  f1 = quncurry f
  h1 = standard_unary f1
  h = qcurry h1

-- | This transformer decomposes a circuit into the strict gate set,
-- which we define to be:
-- 
-- * /H/, /S/, /T/, and /CNOT/.
-- 
-- As a precondition, the input circuit must only contain the
-- following gates:
-- 
-- * controlled-not (with one positive or negative control),
-- 
-- * any single-qubit Clifford gates,
-- 
-- * /T/ and /T/[sup †].
-- 
-- Global phases are suppressed. Classical controls and classical
-- gates are not subject to the gate base, and are left untouched.
-- 
-- Any gates that are not among the input gates listed above will be
-- transformed to a semantically correct circuit which may, however,
-- contain gates that are not in the strict gate set. The best way to
-- avoid this is to apply exact and approximate Clifford+/T/
-- decomposition first.
strict_generic :: (QCData qa, QCData qb, QCurry qfun qa qb) => qfun -> qfun
strict_generic f = h where
  f1 = quncurry f
  h1 = strict_unary f1
  h = qcurry h1
