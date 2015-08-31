-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This library contains special decompositions of particular gates
-- into particular gate bases. It also contains functions for
-- decomposing multiple controls.
-- 
-- For example, we provide particular decompositions of the Toffoli,
-- Fredkin, doubly-controlled /iX/-gate, and certain other controlled
-- Clifford gates, into the Clifford+/T/ base. In some cases, we
-- provide more than one decomposition.
-- 
-- Many of these decompositions are taken or adapted from the
-- literature, for example, from:
-- 
-- * M. A. Nielsen and I. L. Chuang, 
-- /Quantum Computation and Quantum Information/,
-- Cambridge University Press, 2002.
-- 
-- * M. Amy, D. Maslov, M. Mosca, and M. Roetteler,
-- A meet-in-the-middle algorithm for fast synthesis 
-- of depth-optimal quantum circuits,
-- /IEEE Transactions on Computer-Aided Design of/ 
-- /Integrated Circuits and Systems/ 32(6):818-830.
-- Also available from <http://arxiv.org/abs/1206.0758>.
-- 
-- * A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo,
-- N. Margolus, P. Shor, T. Sleator, J. A. Smolin, and H. Weinfurter,
-- Elementary gates for quantum computation,
-- /Physical Review A/ 52(5):3457-3467, 1995. 
-- Also available from <http://arxiv.org/abs/quantph/9503016>.
-- 
-- * P. Selinger, Quantum circuits of T-depth one,
-- /Physical Review A/ 87, 042302 (4 pages), 2013.
-- Also available from <http://arxiv.org/abs/1210.0974>.
-- 
-- * B. Giles and P. Selinger, Exact synthesis of multiqubit
-- Clifford+T circuits, /Physical Review A/ 87, 032332 (7 pages),
-- 2013.  Also available from <http://arxiv.org/abs/1212.0506>.

module QuipperLib.GateDecompositions where

import Quipper

import Control.Monad

-- ----------------------------------------------------------------------
-- * Decomposition of gates

-- | Decomposition of the Toffoli gate into the Clifford+/T/ base,
-- from Nielsen and Chuang (Figure 4.9). The first argument is the
-- target, and the other two are the controls. The controls can be
-- positive or negative.
-- 
-- \[image toffoli_NC.png]
toffoli_NC_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
toffoli_NC_at q c1 c2 = do
  comment_with_label "ENTER: toffoli_NC" (q,c1,c2) ("q","c1","c2")
  let x = get_sign c1
      y = get_sign c2
      w1 = from_signed c1
      w2 = from_signed c2
  hadamard_at q
  qnot_at q `controlled` w1
  reverse_imp_if (not x) gate_T_inv_at q
  qnot_at q `controlled` w2
  reverse_imp_if (x `xor` y) gate_T_at q
  qnot_at q `controlled` w1
  reverse_imp_if (not y) gate_T_inv_at q
  qnot_at q `controlled` w2
  gate_T_at q
  reverse_imp_if (not x) gate_T_inv_at w1
  hadamard_at q
  qnot_at w1 `controlled` w2
  reverse_imp_if (x `xor` y) gate_T_inv_at w1
  qnot_at w1 `controlled` w2
  reverse_imp_if (not x) gate_S_at w1
  reverse_imp_if (not y) gate_T_at w2
  comment_with_label "EXIT: toffoli_NC" (q,c1,c2) ("q","c1","c2")
  where
    xor = (/=)

-- | Decomposition of the Toffoli gate into the Clifford+/T/ base,
-- from Amy et al. (<http://arxiv.org/abs/1206.0758v3>, Figure
-- 13). The first argument is the target, and the other two are the
-- controls. The controls can be positive or negative.
--   
-- \[image toffoli_AMMR.png]
toffoli_AMMR_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
toffoli_AMMR_at q c1 c2 = do
  comment_with_label "ENTER: toffoli_AMMR" (q,c1,c2) ("q","c1","c2")
  without_comments $ do
    hadamard_at q
    ccZ_AMMR_at q c1 c2
    hadamard_at q
  comment_with_label "EXIT: toffoli_AMMR" (q,c1,c2) ("q","c1","c2")

-- | Decomposition of the Toffoli gate using controlled Clifford
-- operators, from Nielsen and Chuang (Figure 4.8). The controls can be
-- positive or negative.
-- 
-- \[image toffoli_V.png]
toffoli_V_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
toffoli_V_at q c1 c2 = do
  comment_with_label "ENTER: toffoli_V" (q,c1,c2) ("q","c1","c2")
  let q1 = from_signed c1
  let q2 = from_signed c2
  gate_V_at q `controlled` c1
  qnot_at q1 `controlled` c2
  gate_V_inv_at q `controlled` c1
  qnot_at q1 `controlled` c2
  gate_V_at q `controlled` c2
  comment_with_label "EXIT: toffoli_V" (q,c1,c2) ("q","c1","c2")
  
-- | Decomposition of the Toffoli gate into the Clifford+/T/ base,
-- using /T/-depth 1 and four ancillas. From
-- <http://arxiv.org/abs/1210.0974> (Figure 1). The first argument is
-- the target, and the other two are the controls. The controls can be
-- positive or negative.
-- 
-- \[image toffoli_S.png]
toffoli_S_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
toffoli_S_at q c1 c2 = do
  comment_with_label "ENTER: toffoli_S" (q,c1,c2) ("q","c1","c2")
  without_comments $ do
    hadamard_at q
    ccZ_S_at q c1 c2
    hadamard_at q
  comment_with_label "EXIT: toffoli_S" (q,c1,c2) ("q","c1","c2")
  
-- | Decomposition of the doubly-controlled /iX/-gate into the
-- Clifford+/T/ base, using /T/-count 4 and /T/-depth 2. Adapted from
-- (<http://arxiv.org/abs/1210.0974>, Figure 10). The first argument
-- is the target, and the other two are the controls. The controls can
-- be positive or negative.
-- 
-- \[image cc_iX.png]
cc_iX_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
cc_iX_at q c1 c2 = do
  comment_with_label "ENTER: cc_iX" (q,c1,c2) ("q","c1","c2")
  let x = get_sign c1
      y = get_sign c2
      w1 = from_signed c1
      w2 = from_signed c2
  hadamard_at q  
  qnot_at w1 `controlled` q
  qnot_at w2 `controlled` w1
  reverse_imp_if (not x) gate_T_at w1
  reverse_imp_if (x `xor` y) gate_T_inv_at w2
  qnot_at w1 `controlled` q
  qnot_at w2 `controlled` w1
  gate_T_inv_at q
  reverse_imp_if (not y) gate_T_at w2
  qnot_at w2 `controlled` q
  hadamard_at q  
  when (not x && not y) $ do  -- need a phase correction
    gate_omega_at w1
    gate_omega_at w2
  comment_with_label "EXIT: cc_iX" (q,c1,c2) ("q","c1","c2")
  where
    xor = (/=)
    
-- | Decomposition of the doubly-controlled /iX/-gate into the
-- Clifford+/T/ base, using /T/-count 4, and using the control qubits
-- only as controls. Derived from Nielsen and Chuang (Figure 4.9). The
-- controls can be positive or negative.
-- 
-- \[image cc_iX_simple.png]
cc_iX_simple_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
cc_iX_simple_at q c1 c2 = do
  comment_with_label "ENTER: cc_iX_simple" (q,c1,c2) ("q","c1","c2")
  hadamard_at q
  qnot_at q `controlled` c1
  gate_T_at q
  qnot_at q `controlled` c2
  gate_T_inv_at q
  qnot_at q `controlled` c1
  gate_T_at q
  qnot_at q `controlled` c2
  gate_T_inv_at q
  hadamard_at q
  comment_with_label "EXIT: cc_iX_simple" (q,c1,c2) ("q","c1","c2")
  
-- | Decomposition of the doubly-controlled /iX/-gate into the
-- Clifford+/T/ base, using /T/-depth 1 and one ancilla. Adapted from
-- (<http://arxiv.org/abs/1210.0974>, Figure 9). The first argument
-- is the target, and the other two are the controls. The controls can
-- be positive or negative.
-- 
-- \[image cc_iX_S.png]
cc_iX_S_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
cc_iX_S_at q c1 c2 = do
  comment_with_label "ENTER: cc_iX_S" (q,c1,c2) ("q","c1","c2")
  let sx = get_sign c1
      sy = get_sign c2
      x = from_signed c1
      y = from_signed c2
      z = q
  hadamard_at z
  with_ancilla $ \w -> do
    qnot y `controlled` z
    qnot w `controlled` x
    qnot x `controlled` z
    qnot w `controlled` y
    reverse_imp_if (not sx) gate_T_at x
    reverse_imp_if (not sy) gate_T_at y
    gate_T_inv_at z
    reverse_imp_if (sx `xor` sy) gate_T_inv_at w
    qnot w `controlled` y
    qnot x `controlled` z
    qnot w `controlled` x
    qnot y `controlled` z
  when (not sx && not sy) $ do  -- need a phase correction
    gate_omega_at x
    gate_omega_at y
  hadamard_at z
  comment_with_label "EXIT: cc_iX_S" (q,c1,c2) ("q","c1","c2")
  where
    xor = (/=)
    
-- | Decomposition of the doubly-controlled /Z/-gate into the
-- Clifford+/T/ base. Adapted from Amy et
-- al. (<http://arxiv.org/abs/1206.0758v3>, Figure 13). The controls can
-- be positive or negative.
-- 
-- \[image ccZ_AMMR.png]
ccZ_AMMR_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
ccZ_AMMR_at q c1 c2 = do
  comment_with_label "ENTER: ccZ_AMMR" (q,c1,c2) ("q","c1","c2")
  let x = get_sign c1
      y = get_sign c2
      w1 = from_signed c1
      w2 = from_signed c2
  gate_T_at q
  reverse_imp_if (not x) gate_T_at w1
  reverse_imp_if (not y) gate_T_at w2
  qnot_at w2 `controlled` w1
  qnot_at w1 `controlled` q
  qnot_at q `controlled` w2
  reverse_imp_if (not x) gate_T_inv_at w1
  reverse_imp_if (x `xor` y) gate_T_at q
  qnot_at w1 `controlled` w2
  reverse_imp_if (not y) gate_T_inv_at w1
  reverse_imp_if (x `xor` y) gate_T_inv_at w2
  qnot_at w1 `controlled` q
  qnot_at q `controlled` w2
  qnot_at w2 `controlled` w1
  comment_with_label "EXIT: ccZ_AMMR" (q,c1,c2) ("q","c1","c2")
  where
    xor = (/=)

-- | Decomposition of the doubly-controlled /Z/-gate into the
-- Clifford+/T/ base, using /T/-depth 1 and four ancillas. From
-- Selinger (<http://arxiv.org/abs/1210.0974>, Figure 1). The controls
-- can be positive or negative.
-- 
-- \[image ccZ_S.png]
ccZ_S_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
ccZ_S_at q c1 c2 = do
  comment_with_label "ENTER: ccZ_S" (q,c1,c2) ("q","c1","c2")
  let sx = get_sign c1
      sy = get_sign c2
      x = from_signed c1
      y = from_signed c2
      z = q
  with_ancilla_init (0,0,0,0) $ \(xyz, xy, yz, xz) -> do
    qnot yz `controlled` y
    qnot xyz `controlled` x
    qnot xy `controlled` y
    qnot yz `controlled` z
    qnot xz `controlled` xyz
    qnot xy `controlled` x
    qnot xz `controlled` z
    qnot xyz `controlled` yz
    reverse_imp_if (not sx) gate_T_at x
    reverse_imp_if (not sy) gate_T_at y
    gate_T_at z
    reverse_imp_if (sx `xor` sy) gate_T_at xyz
    reverse_imp_if (sx `xor` sy) gate_T_inv_at xy
    reverse_imp_if (not sy) gate_T_inv_at yz
    reverse_imp_if (not sx) gate_T_inv_at xz
    qnot xyz `controlled` yz
    qnot xz `controlled` z
    qnot xy `controlled` x
    qnot xz `controlled` xyz
    qnot yz `controlled` z
    qnot xy `controlled` y
    qnot xyz `controlled` x
    qnot yz `controlled` y
  comment_with_label "EXIT: ccZ_S" (q,c1,c2) ("q","c1","c2")
  where
    xor = (/=)

-- | Decomposition of the Fredkin (controlled-Swap) gate into the
-- Clifford+/T/ base. The first two arguments are the targets, and the
-- last one the control. The controls can be positive or negative.
-- 
-- \[image fredkin.png]
fredkin_at :: Qubit -> Qubit -> Signed Qubit -> Circ ()
fredkin_at q1 q2 c = do
  comment_with_label "ENTER: fredkin" (q1,q2,c) ("q1","q2","c")
  without_controls $ do
    qnot_at q2 `controlled` q1
    toffoli_AMMR_at q1 (Signed q2 True) c
    qnot_at q2 `controlled` q1
  comment_with_label "EXIT: fredkin" (q1,q2,c) ("q1","q2","c")

-- | Decomposition of a controlled /H/-gate into the Clifford+/T/
-- base. From Amy et al. (<http://arxiv.org/abs/1206.0758v3>, Figure
-- 5(a)). The first argument is the target and the second one the
-- control. The control can be positive or negative.
-- 
-- \[image cH_AMMR.png]
cH_AMMR_at :: Qubit -> Signed Qubit -> Circ ()
cH_AMMR_at q c = do
  comment_with_label "ENTER: cH_AMMR" (q,c) ("q","c")
  gate_S_inv_at q
  hadamard_at q
  gate_T_inv_at q
  qnot_at q `controlled` c
  gate_T_at q
  hadamard_at q
  gate_S_at q
  comment_with_label "EXIT: cH_AMMR" (q,c) ("q","c")

-- | Decomposition of a controlled /W/-gate into the Clifford+/T/
-- base. The first two arguments are the targets, and the last
-- argument is the control. The control can be positive or negative.
-- 
-- \[image controlled_W.png]
controlled_W_at :: Qubit -> Qubit -> Signed Qubit -> Circ ()
controlled_W_at q1 q2 c = do
  comment_with_label "ENTER: controlled_W" (q1,q2,c) ("W1","W2","c")
  without_comments $ do
    qnot_at q2 `controlled` q1
    gate_S_inv_at q1
    hadamard_at q1
    gate_T_inv_at q1
    toffoli_AMMR_at q1 (Signed q2 True) c
    gate_T_at q1
    hadamard_at q1
    gate_S_at q1
    qnot_at q2 `controlled` q1
  comment_with_label "EXIT: controlled_W" (q1,q2,c) ("W1","W2","c")

-- | Decomposition of a /W/-gate into the Clifford+/T/ base.
-- 
-- \[image gate_W_CliffordT.png]
gate_W_CliffordT_at :: Qubit -> Qubit -> Circ ()
gate_W_CliffordT_at q1 q2 = do
  comment_with_label "ENTER: gate_W_CliffordT" (q1,q2) ("W1","W2")
  without_comments $ do
    qnot_at q2 `controlled` q1
    cH_AMMR_at q1 (Signed q2 True)
    qnot_at q2 `controlled` q1
  comment_with_label "EXIT: gate_W_CliffordT" (q1,q2) ("W1","W2")

-- | Decomposition of a controlled /iX/-gate into the Clifford+/T/
-- base. The first argument is the target, and the second one is the
-- control. The control can be positive or negative.
-- 
-- \[image controlled_iX.png]
controlled_iX_at :: Qubit -> Signed Qubit -> Circ ()
controlled_iX_at q c = do
  comment_with_label "ENTER: controlled_iX" (q,c) ("q","c")
  let x = get_sign c
      w = from_signed c
  qnot_at q `controlled` c
  reverse_imp_if (not x) gate_S_at w
  when (not x) $ do  -- need a phase correction
    gate_omega_at q
    gate_omega_at w
  comment_with_label "EXIT: controlled_iX" (q,c) ("q","c")

-- | Decomposition of a controlled /S/-gate into the Clifford+/T/
-- base. From Amy et al. (<http://arxiv.org/abs/1206.0758v3>, Figure
-- 5(b)). The first argument is the target, and the second one is the
-- control. The control can be positive or negative.
-- 
-- \[image controlled_S.png]
controlled_S_at :: Qubit -> Signed Qubit -> Circ ()
controlled_S_at q c = do
  comment_with_label "ENTER: controlled_S" (q,c) ("q","c")
  let x = get_sign c  
      w = from_signed c
  qnot w `controlled` q
  reverse_imp_if (not x) gate_T_inv_at w
  qnot w `controlled` q
  reverse_imp_if (not x) gate_T_at w
  gate_T_at q
  comment_with_label "EXIT: controlled_S" (q,c) ("q","c")

-- | Decomposition of a controlled /T/-gate into the Clifford+/T/
-- base. The first argument is the target, and the second one is the
-- control. The control can be positive or negative.
-- 
-- \[image controlled_T.png]
controlled_T_at :: Qubit -> Signed Qubit -> Circ ()
controlled_T_at q c = do
  comment_with_label "ENTER: controlled_T" (q,c) ("q","c")
  without_comments $ do
    with_ancilla_init False $ \r -> do
      cc_iX_at r (Signed q True) c
      gate_T_at r
      reverse_generic_imp cc_iX_at r (Signed q True) c
  comment_with_label "EXIT: controlled_T" (q,c) ("q","c")

-- | Decomposition of a controlled /V/-gate into the Clifford+/T/
-- base. Adapted from Amy et al. (<http://arxiv.org/abs/1206.0758v3>,
-- Figure 5(c)). Our /V/-gate is /H//S/[sup †]/H/ as in Nielsen and
-- Chuang. The first argument is the target, and the second one is the
-- control. The control can be positive or negative.
-- 
-- \[image controlled_V.png]
controlled_V_at :: Qubit -> Signed Qubit -> Circ ()
controlled_V_at q c = do
  comment_with_label "ENTER: controlled_V" (q,c) ("q","c")
  let x = get_sign c
      w = from_signed c
  hadamard_at q
  reverse_imp_if (not x) gate_T_inv_at w
  qnot w `controlled` q
  reverse_imp_if (not x) gate_T_at w
  gate_T_inv_at q
  qnot w `controlled` q
  hadamard_at q
  comment_with_label "EXIT: controlled_V" (q,c) ("q","c")

-- | Decomposition of a controlled /E/-gate into the Clifford+/T/
-- base. The first argument is the target, and the second one is the
-- control. The control can be positive or negative.
-- 
-- \[image controlled_E.png]
controlled_E_at :: Qubit -> Signed Qubit -> Circ ()
controlled_E_at q c = do
  comment_with_label "ENTER: controlled_E" (q,c) ("q","c")
  with_signed_qubit c $ \r -> do
    gate_H_at q
    gate_S_at r
    gate_T_at q
    qnot_at q `controlled` r
    gate_T_inv_at q
    gate_H_at q
    qnot_at r `controlled` q
    gate_T_at r
    gate_T_inv_at q
    qnot_at r `controlled` q
  comment_with_label "EXIT: controlled_E" (q,c) ("q","c")

-- | Decomposition of a controlled [bold Y]-gate into the Clifford+/T/
-- base. The gate is from the Ground State Estimation algorithm and is
-- defined as [bold Y] = /SHS/, or equivalently,
-- 
-- \[image Y.png]
-- 
-- It should not be confused with the Pauli /Y/ gate.
-- The first argument is the target, and the second one is the
-- control. The control can be positive or negative.
-- 
-- \[image controlled_YY.png]
controlled_YY_at :: Qubit -> Signed Qubit -> Circ ()
controlled_YY_at q c = do
  comment_with_label "ENTER: controlled_YY" (q,c) ("q","c")
  gate_S_at q
  qnot_at q `controlled` c
  gate_S_inv_at q
  hadamard_at q
  gate_T_inv_at q
  qnot_at q `controlled` c
  gate_T_at q
  hadamard_at q
  comment_with_label "EXIT: controlled_YY" (q,c) ("q","c")

-- | A \"plain\" Toffoli gate, not decomposed. This is provided for
-- convenience, for example to use with 'with_combined_controls'.
toffoli_plain_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
toffoli_plain_at q c1 c2 = do
  qnot_at q `controlled` (c1,c2)
  
-- | A \"plain\" doubly-controlled /iX/-gate, not decomposed. This is
-- provided for convenience, for example to use with
-- 'with_combined_controls'.
cc_iX_plain_at :: Qubit -> Signed Qubit -> Signed Qubit -> Circ ()
cc_iX_plain_at q c1 c2 = do
  gate_iX_at q `controlled` (c1,c2)

-- | Decomposition of an /m/-times controlled not-gate, using /m/−2
-- ancillas that do not need be initialized in a particular
-- state. Adapted from Barenco et al.
-- (<http://arxiv.org/abs/quantph/9503016>, Lemma 7.2).
-- 
-- In addition to what is shown in Barenco et al., this function
-- permits some Toffoli gates to be replaced by doubly-controlled
-- /iX/-gates. This may be beneficial in gate bases, such as
-- Clifford+/T/, where a doubly-controlled /iX/-gate has a simpler
-- representation than a Toffoli gate.
-- 
-- The first argument is a Toffoli gate to use in the
-- decomposition. The second argument may be either a Toffoli gate or
-- a doubly-controlled /iX/ gate. The third argument is the target,
-- the fourth argument is a list of qubits to be used as ancillas, and
-- the fifth argument is a list of signed controls. The ancillas need
-- not be initialized, and are returned in their original state.
-- 
-- The size of this circuit is linear in the number of controls; the
-- decomposition uses 4/m/−8 doubly-controlled gates for /m/ ≥ 3.
-- 
-- \[image multi_cnot_barenco.png]
multi_cnot_barenco_at :: (Qubit -> Signed Qubit -> Signed Qubit -> Circ ()) -> (Qubit -> Signed Qubit -> Signed Qubit -> Circ ()) -> Qubit -> [Qubit] -> [Signed Qubit] -> Circ ()
multi_cnot_barenco_at my_toffoli_at my_ciX_at q as cs =
  case cs of
    [] -> do
      qnot_at q
    [c] -> do
      qnot_at q `controlled` c
    [c1,c2] -> do
      my_toffoli_at q c1 c2
    c:cs -> do
      case as of
        [] -> error "multi_cnot_barenco_at: too few ancillas"
        a:as -> do
          my_toffoli_at q (Signed a True) c
          aux cs (a:as)
          my_toffoli_at q (Signed a True) c
          reverse_generic_imp aux cs (a:as)
  where
    aux :: [Signed Qubit] -> [Qubit] -> Circ ()
    aux [] as = return ()
    aux [c] as = return ()
    aux [c1,c2] (a:as) = do
      my_ciX_at a c1 c2
    aux (c:cs) (a1:a2:as) = do
      my_ciX_at a1 (Signed a2 True) c
      aux cs (a2:as)
      my_ciX_at a1 (Signed a2 True) c
    aux _ _ = error "multi_cnot_barenco_at: too few ancillas"

-- | Decomposition of a multiply-controlled /iX/-gate, using no
-- ancillas. Adapted from Giles and Selinger
-- (<http://arxiv.org/abs/1212.0506>, Section 5.2).
-- 
-- The first argument is a Toffoli gate or a doubly-controlled
-- /iX/-gate. The third argument is the target, and the fourth
-- argument is a list of signed controls.
-- 
-- The size of this circuit is linear in the number of controls; the
-- decomposition uses 8/m/−32 doubly-controlled gates, 4 /T/-gates,
-- and 2 /H/-gates, for /m/ ≥ 6.
-- 
-- \[image multi_ciX_noancilla.png]
multi_ciX_noancilla_at :: (Qubit -> Signed Qubit -> Signed Qubit -> Circ ()) -> Qubit -> [Signed Qubit] -> Circ ()
multi_ciX_noancilla_at my_ciX_at q [] = gate_iX_at q
multi_ciX_noancilla_at my_ciX_at q [c] = gate_iX_at q `controlled` c
multi_ciX_noancilla_at my_ciX_at q [c1,c2] = gate_iX_at q `controlled` [c1,c2]
multi_ciX_noancilla_at my_ciX_at q cs = do
  hadamard_at q
  gate_T_inv_at q
  multi_cnot_barenco_at my_ciX_at my_ciX_at q as1 cs2
  gate_T_at q
  multi_cnot_barenco_at my_ciX_at my_ciX_at q as2 cs1
  gate_T_inv_at q
  reverse_generic_imp (multi_cnot_barenco_at my_ciX_at my_ciX_at) q as1 cs2
  gate_T_at q
  reverse_generic_imp (multi_cnot_barenco_at my_ciX_at my_ciX_at) q as2 cs1
  hadamard_at q
  where
    n = length cs
    (cs1, cs2) = splitAt (n `div` 2) cs
    as1 = map from_signed cs1
    as2 = map from_signed cs2
    
-- ----------------------------------------------------------------------
-- * Decomposition of controls

-- | Partition a list of controls into quantum and classical.
partition_controls :: [Signed Endpoint] -> ([Signed Qubit], [Signed Bit])
partition_controls cs = (qcs, ccs) where
  qcs = [ Signed q b | Signed (Endpoint_Qubit q) b <- cs ]
  ccs = [ Signed c b | Signed (Endpoint_Bit c) b <- cs ]

-- | Given a function that expects a qubit (typically as a control),
-- turn it into a function that can handle a /signed/ (positive or
-- negative) qubit. This is done by conjugating the circuit with
-- negations on both sides, if the sign is negative. Usage:
-- 
-- > with_signed_qubit c $ \q -> do
-- >   <<<code using q>>>
-- 
-- \[image with_signed_qubit.png]
with_signed_qubit :: Signed Qubit -> (Qubit -> Circ b) -> Circ b
with_signed_qubit (Signed q True) f = f q
with_signed_qubit (Signed q False) f = do
  gate_X_at q
  b <- f q
  gate_X_at q
  return b

-- | Decompose quantum controls recursively until at most /n/ remain,
-- and then pass these reduced controls to the given circuit.
-- Precondition: /n/ ≥ 1.  
-- 
-- The decomposition is done using a Toffoli-like gate that is given
-- as the first argument. This should be either a Toffoli gate, a
-- doubly-controlled /iX/-gate, a decomposition thereof, or any other
-- reversible ternary gate with the behavior
-- 
-- * |000〉 ↦ |0〉|φ[sub 0]〉
-- 
-- * |001〉 ↦ |0〉|φ[sub 1]〉
-- 
-- * |010〉 ↦ |0〉|φ[sub 2]〉
-- 
-- * |011〉 ↦ |1〉|φ[sub 3]〉,
-- 
-- where the states |φ[sub 0]〉, …, |φ[sub 3]〉 are arbitrary.
-- 
-- For example, when /n/=2, this typically yields a circuit such as
-- the following (here shown using the doubly-controlled /iX/-gate):
-- 
-- \[image with_combined_controls2.png]
--   
-- And for /n/=1, the circuit typically looks like this:
-- 
-- \[image with_combined_controls1.png]
-- 
-- Classical controls are not decomposed, but are applied to the
-- resulting circuit directly.
with_combined_controls :: (Qubit -> Signed Qubit -> Signed Qubit -> Circ ()) -> Int -> [Signed Endpoint] -> ([Signed Qubit] -> Circ a) -> Circ a
with_combined_controls my_toffoli_at n cs code = circ where
  (qcs, ccs) = partition_controls cs
  len = length qcs
  -- m is the number of qcs to remove.
  m = if len <= n then 0 else len - n
  circ = with_controls ccs $ do
    aux m qcs code

  aux 0 qcs code = code qcs
  aux n [] code = code []
  aux n [c] code = code [c]
  aux n (c1:c2:qcs) code = do
    with_computed (quantum_and c1 c2) $ \c -> do
      aux (n-1) (qcs ++ [Signed c True]) code

  quantum_and :: Signed Qubit -> Signed Qubit -> Circ Qubit
  quantum_and c1 c2 = do
    q <- qinit 0
    my_toffoli_at q c1 c2
    return q
