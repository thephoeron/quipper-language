-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | A Quipper library for synthesizing Clifford+/T/ circuits directly
-- from a matrix description or Euler angle description of a unitary
-- operator. This library provides both exact and approximate
-- synthesis.

module QuipperLib.Synthesis where

import Quipper

import Quipper.Internal

import Libraries.Synthesis.CliffordT
import Libraries.Synthesis.MultiQubitSynthesis
import Libraries.Synthesis.Ring
import Libraries.Synthesis.Matrix
import Libraries.Synthesis.Newsynth
import Libraries.Synthesis.SymReal
import Libraries.Synthesis.EulerAngles

import Libraries.Auxiliary (boollist_of_int_bh)

import Control.Monad (when)
import Data.Bits (xor, (.&.))
import System.Random
import Text.Printf

-- ----------------------------------------------------------------------
-- * Precision

-- | A type to measure precision. Precision is expressed as a number
-- /b/ of bits, i.e., binary digits, so that ε = 2[sup −/b/].
type Precision = Double

-- | Binary digits, as a unit of precision. For example, the following
-- specifies a precision of 20 binary digits:
-- 
-- > prec = 20 * bits
bits :: Precision
bits = 1

-- | Decimal digits, as a unit of precision. For example, the
-- following specifies a precision of 30 decimal digits:
-- 
-- > prec = 30 * digits
digits :: Precision
digits = logBase 2 10

-- ----------------------------------------------------------------------
-- * Phase

-- | A boolean flag indicating whether to respect global phases
-- during circuit synthesis ('True') or disregard them ('False').
type KeepPhase = Bool
    
-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | Apply a gate (from the type 'Gate' of Clifford+/T/ operators) to
-- the given 'Qubit'.
apply_gate_at :: Gate -> Qubit -> Circ ()
apply_gate_at X q = do
  gate_X_at q
apply_gate_at Y q = do
  gate_Y_at q
apply_gate_at Z q = do
  gate_Z_at q
apply_gate_at H q = do
  hadamard_at q
apply_gate_at S q = do
  gate_S_at q
apply_gate_at T q = do
  gate_T_at q
apply_gate_at E q = do
  gate_E_at q
apply_gate_at W q = do
  gate_omega_at q

-- | Apply a gate list (from the type 'Gate' of Clifford+/T/
-- operators) to the given 'Qubit'. 
-- 
-- Note: the operators in the list are applied right-to-left, i.e.,
-- the gate list is assumed given in matrix multiplication order, but
-- are applied in circuit order.
apply_gates_at :: [Gate] -> Qubit -> Circ ()
apply_gates_at gates q = do
  sequence_ [ apply_gate_at g q | g <- reverse gates ]

-- | Like 'apply_gates_at', but apply the same list of gates to two
-- qubits in parallel.
apply_gates2_at :: [Gate] -> Qubit -> Qubit -> Circ ()
apply_gates2_at gates q1 q2 = do
  sequence_ [ do
                 apply_gate_at g q1
                 apply_gate_at g q2
            | g <- reverse gates ]

-- | Input two indices /i/ and /j/, a list of qubits /qlist/, and an
-- imperative-style single-qubit gate /U/. Apply the two-level
-- operator /U/[sub /i/,/j/] to /qlist/. Intended usage:
-- 
-- > twolevel i j qlist gate_U_at
-- 
-- The qubits in /qlist/ are ordered lexicographically left-to-right,
-- e.g., [|00〉, |01〉, |10〉, |11〉].
-- 
-- This function implements an improved version of Gray codes.
twolevel :: Index -> Index -> [Qubit] -> (Qubit -> Circ ()) -> Circ ()
twolevel i j qlist body = aux l1 l2 qlist where
  n = length qlist
  l1 = boollist_of_int_bh n i
  l2 = boollist_of_int_bh n j

  aux [] [] [] = error "twolevel: i=j"
  aux (h1:t1) (h2:t2) (q:qs)
    | h1 == h2 =
      with_controls (q .==. h1) $ do
        aux t1 t2 qs
    | h1 == True =
      with_basis_change (qnot_at q) $ do
        aux2 t1 t2 q qs
    | otherwise =
      aux2 t1 t2 q qs
  aux _ _ _ = error "twolevel: internal error 1" -- not reached

  aux2 [] [] q [] =
    body q
  aux2 (h1:t1) (h2:t2) q0 (q:qs)
    | h1 == h2 =
      with_controls (q .==. h1) $ do
        aux2 t1 t2 q0 qs
    | otherwise =
      with_basis_change (qnot_at q `controlled` q0) $ do
        with_controls (q .==. h1) $ do
          aux2 t1 t2 q0 qs
  aux2 _ _ _ _ = error "twolevel: internal error 2" -- not reached

-- | Apply a 'TwoLevel' gate to the given list of qubits. 
-- The qubits in /qlist/ are ordered lexicographically left-to-right,
-- e.g., [|00〉, |01〉, |10〉, |11〉].
apply_twolevel_at :: TwoLevel -> [Qubit] -> Circ ()
apply_twolevel_at (TL_X i j) qlist =
  twolevel i j qlist $ \q -> do
    gate_X_at q
apply_twolevel_at (TL_H i j) qlist =
  twolevel i j qlist $ \q -> do
    hadamard_at q
apply_twolevel_at (TL_T m i j) qlist
  | m `mod` 8 == 0 = return ()
  | otherwise =
    twolevel i j qlist $ \q -> do
      when (m .&. 4 /= 0) $ do
        gate_Z_at q
      when (m .&. 2 /= 0) $ do
        gate_S_at q
      when (m .&. 1 /= 0) $ do
        gate_T_at q
apply_twolevel_at (TL_omega m i) [] =
  global_phase (fromIntegral (m `mod` 8) * 0.25)
apply_twolevel_at (TL_omega m i) qlist =
  apply_twolevel_at (TL_T m j i) qlist
  where
    j = if i == 0 then 1 else i .&. (i-1)

-- | Apply a list of 'TwoLevel' gates to the given list of
-- qubits. 
-- 
-- The qubits in /qlist/ are ordered lexicographically left-to-right,
-- e.g., [|00〉, |01〉, |10〉, |11〉].
-- 
-- Note: the operators in the list are applied right-to-left, i.e.,
-- the gate list is assumed given in matrix multiplication order, but
-- are applied in circuit order.

-- Implementation note: this could be improved by combining
-- consecutive two-level gates if they share the same i and j
apply_twolevels_at :: [TwoLevel] -> [Qubit] -> Circ ()
apply_twolevels_at ops qlist =
  sequence_ [ apply_twolevel_at g qlist | g <- reverse ops ]

-- ----------------------------------------------------------------------
-- * Single-qubit exact synthesis

-- | Decompose the given operator exactly into a single-qubit
-- Clifford+/T/ circuit. The operator must be given in one of the
-- available exact formats, i.e., any instance of the 'ToGates' class.
-- Typical instances are:
-- 
-- * 'U2' 'DComplex': a 2×2 unitary operator with entries from the
-- ring ℤ[1\/√2, /i/];
-- 
-- * 'U2' 'DOmega': a 2×2 unitary operator with entries from the ring
-- [bold D][ω];
-- 
-- * 'SO3' 'DReal': a 3×3 Bloch sphere operator with entries from the
-- ring ℤ[1\/√2]. In this last case, the operator will be synthesized
-- up to an unspecified global phase.
exact_synthesis1 :: (ToGates a) => a -> Qubit -> Circ Qubit
exact_synthesis1 op q = do
  comment_with_label "ENTER: exact_synthesis1" q "q"
  apply_gates_at gates q
  comment_with_label "EXIT: exact_synthesis1" q "q"
  return q
  where
    gates = convert (normalize op) :: [Gate]

-- ----------------------------------------------------------------------
-- * Multi-qubit exact synthesis

-- | Decompose the given operator exactly into a Clifford+/T/ circuit.
-- The operator must be given as an /n/×/n/-matrix with coefficients
-- in a ring that is an instance of the 'ToEComplex' class. Typical
-- examples of such rings are 'DComplex', 'DOmega', and 'EComplex'.
-- 
-- If this function is applied to a list of /m/ qubits, then we must
-- have /n/ ≤ 2[sup /m/].
-- 
-- The generated circuit may contain ancillas.
exact_synthesis :: (ToEComplex a, Nat n) => Matrix n n a -> [Qubit] -> Circ [Qubit]
exact_synthesis op qlist = do
  comment_with_label "ENTER: exact_synthesis" qlist "q"
  apply_twolevels_at twolevels qlist
  comment_with_label "EXIT: exact_synthesis" qlist "q"
  return qlist
  where
    op_DComplex = matrix_map (fromDComplex . to_dyadic . toEComplex) op
    twolevels = synthesis_nqubit op_DComplex

-- ----------------------------------------------------------------------
-- * Single-qubit approximate synthesis

-- ----------------------------------------------------------------------
-- ** /z/-Rotations

-- | Decompose an /R/[sub /z/](θ) = [exp −/i/θ/Z/\/2] gate into a
-- single-qubit Clifford+/T/ circuit up to the given precision. 
-- 
-- \[image Rz.png]
-- 
-- The parameters are:
-- 
-- * a precision /b/ ≥ 0;
-- 
-- * an angle θ, given as a 'SymReal' value;
-- 
-- * a source of randomness /g/.
approximate_synthesis_zrot :: (RandomGen g) => Precision -> SymReal -> g -> Qubit -> Circ Qubit
approximate_synthesis_zrot b theta g q = do
  comment_with_label (printf "ENTER: approximate_synthesis_zrot (b=%.2f, theta=%s)" b (show theta)) q "q"
  q <- without_comments $ do
    exact_synthesis1 op q 
  comment_with_label "EXIT: approximate_synthesis_zrot" q "q"
  return q  
  where
    op = newsynth b theta g

-- ----------------------------------------------------------------------
-- ** Global phase gates

-- | Construct a Clifford+/T/ circuit (with no inputs and outputs)
-- that approximates a scalar global phase gate [exp /i/θ] up to the
-- given precision. The parameters are:
-- 
-- * a flag /keepphase/ to indicate whether global phase should be
-- respected. (Note that if this is set to 'False', then this function
-- is just a no-op);
-- 
-- * a precision /b/ ≥ 0;
-- 
-- * an angle θ, given as a 'SymReal' value;
-- 
-- * a source of randomness /g/.
-- 
-- We use the following decomposition:
-- 
-- \[image phase.png]
approximate_synthesis_phase :: (RandomGen g) => KeepPhase -> Precision -> SymReal -> g -> Circ ()
approximate_synthesis_phase False b theta g = do
  return ()
approximate_synthesis_phase True b theta g = do
  comment (printf "ENTER: approximate_synthesis_phase (b=%.2f, theta=%s)" b (show theta))
  when (gates /= []) $ do
    q <- qinit 0
    apply_gates_at gates q
    qterm 0 q
  comment "EXIT: approximate_synthesis_phase"
  where
    op = newsynth b (-2*theta) g
    gates = convert (normalize op) :: [Gate]

-- ----------------------------------------------------------------------
-- ** /U/(2) from Euler angles

-- | Decompose the operator
-- 
-- * /U/ = [exp /i/α] R[sub /z/](β) R[sub /x/](γ) R[sub /z/](δ)
-- 
-- into the Clifford+/T/ gate base, up to the given precision.
-- The parameters are:
-- 
-- * a flag /keepphase/ to indicate whether global phase should be
--   respected. If this is 'False', the angle α is disregarded;
-- 
-- * a precision /b/ ≥ 0;
-- 
-- * a tuple of Euler angles (α, β, γ, δ), given as 'SymReal' values;
-- 
-- * a source of randomness /g/.
approximate_synthesis_euler :: (RandomGen g) => KeepPhase -> Precision -> (SymReal, SymReal, SymReal, SymReal) -> g -> Qubit -> Circ Qubit
approximate_synthesis_euler keepphase b (alpha, beta, gamma, delta) g q = do
  comment_with_label (printf "ENTER: approximate_synthesis_euler (b=%.2f, alpha=%s, beta=%s, gamma=%s, delta=%s, keepphase=%s)" b (show alpha) (show beta) (show gamma) (show delta) (show keepphase)) q "q"
  without_comments $ do
    exact_synthesis1 (op_beta * u2_H * op_gamma * u2_H * op_delta) q
    approximate_synthesis_phase keepphase b' alpha g1
  comment_with_label "EXIT: approximate_synthesis_euler" q "q"
  return q
  where
    op_beta = newsynth b' beta g2
    op_gamma = newsynth b' gamma g3
    op_delta = newsynth b' delta g4
    (g', g'') = split g
    (g1, g2) = split g'
    (g3, g4) = split g''
    b' = b + 2    -- ε' = ε / 4

-- ----------------------------------------------------------------------
-- ** /U/(2) from matrix

-- | Decompose a single-qubit unitary gate /U/ into the Clifford+/T/
-- gate base, up to the given precision, provided that det /U/ = 1.
-- The parameters are:
-- 
-- * a flag /keepphase/ to indicate whether global phase should be
-- respected;
-- 
-- * a precision /b/ ≥ 0;
-- 
-- * a 2×2 complex matrix, with entries expressed as 'Cplx' 'SymReal' values;
-- 
-- * a source of randomness /g/.
approximate_synthesis_u2 :: (RandomGen g) => KeepPhase -> Precision -> U2 (Cplx SymReal) -> g -> Qubit -> Circ Qubit
approximate_synthesis_u2 keepphase b op g q = do
  comment_with_label (printf "ENTER: approximate_synthesis_u2 (b=%.2f, op=%s, keepphase=%s)" b (show op) (show keepphase)) q "q"
  q <- without_comments $ do
    approximate_synthesis_euler keepphase b (alpha, beta, gamma, delta) g q
  comment_with_label "EXIT: approximate_synthesis_u2" q "q"
  return q
  where
    (alpha, beta, gamma, delta) = euler_angles op

-- ----------------------------------------------------------------------
-- ** Controlled gates

-- | Decompose a controlled /R/[sub /z/](θ) = [exp −/i/θ/Z/\/2] gate
-- into a single-qubit Clifford+/T/ circuit up to the given
-- precision. The parameters are as for 'approximate_synthesis_phase'.
-- The first input is the target qubit, and the second input the
-- control.
-- 
-- We use the following decomposition. It has lower /T/-count than the
-- alternatives and makes good use of parallelism. Since it uses the
-- same rotation twice, only a single run of the synthesis algorithm
-- is required.
-- 
-- \[image controlled-zrot.png]
approximate_synthesis_zrot_ctrl :: (RandomGen g) => Precision -> SymReal -> g -> Qubit -> Qubit -> Circ Qubit
approximate_synthesis_zrot_ctrl b theta g q1 c2 = do
  comment_with_label (printf "ENTER: approximate_synthesis_zrot_ctrl (b=%.2f, theta=%s)" b (show theta)) (q1,c2) ("q", "c")
  qnot_at c2 `controlled` q1 .==. False
  apply_gates2_at gates q1 c2
  qnot_at c2 `controlled` q1 .==. False
  comment_with_label "EXIT: approximate_synthesis_zrot_ctrl" (q1,c2) ("q", "c")
  return q1
  where
    gates = convert (normalize op) :: [Gate]
    op = newsynth (b+1) (theta/2) g

-- | Decompose a controlled phase gate
-- 
-- \[image controlled_phase.png]
-- 
-- into the Clifford+/T/ gate base. The parameters are as for
-- 'approximate_synthesis_phase'.
-- 
-- We use the following decomposition. It has lower /T/-count than the
-- alternatives and makes good use of parallelism. Since it uses the
-- same rotation twice, only a single run of the synthesis algorithm
-- is required.
-- 
-- \[image controlled-phase-decomp.png]
-- 
-- If the 'KeepPhase' flag is set, respect global phase; otherwise,
-- disregard it.
approximate_synthesis_phase_ctrl :: (RandomGen g) => KeepPhase -> Precision -> SymReal -> g -> Qubit -> Circ Qubit
approximate_synthesis_phase_ctrl keepphase b theta g q1 = do
  comment_with_label (printf "ENTER: approximate_synthesis_phase_ctrl (b=%.2f, theta=%s keepphase=%s)" b (show theta) (show keepphase)) q1 "q"
  if keepphase then do
    q2 <- qinit True
    apply_gates2_at gates q2 q1
    qterm True q2
  else do
    approximate_synthesis_zrot b theta g q1
    return ()
  comment_with_label "EXIT: approximate_synthesis_phase_ctrl" q1 "q"
  return q1
  where
    gates = convert (normalize op) :: [Gate]
    op = newsynth (b+1) theta g
