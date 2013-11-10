-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides the main circuit for the GSE algorithm.
-- This circuit consists of a state preparation, followed by a large
-- number of Hamiltonian simulation terms for small time steps,
-- followed by an inverse Quantum Fourier Transform and a final
-- measurement. 

module Algorithms.GSE.GSE where

import Quipper
import QuipperLib.QFT
import Algorithms.GSE.GSEData
import Algorithms.GSE.JordanWigner

import Control.Monad
import Text.Printf

-- ----------------------------------------------------------------------
-- * Basic time step

-- $ These functions provide one- and two-electron operators for an
-- individual Trotter time step θ. Each operator consists of a large
-- number of individual Hamiltonian terms.

-- | Apply the one-electron operator [exp -/i/θ/H/], where
-- /H/ = /h/[sub /pq/] /a/[sub /p/][sup †]/a/[sub /q/] if /p/ = /q/ and
-- /H/ = /h/[sub /pq/] (/a/[sub /p/][sup †]/a/[sub /q/]
-- + /a/[sub /q/][sup †]/a/[sub /p/]) otherwise, to every pair of
-- qubits /p/≥/q/ in a register |ψ〉. The inputs are Hamiltonian data
-- /h/, the angle θ, the register |ψ〉, and a control qubit. 
exp_pq :: ((Int,Int) -> Double) -> Double -> [Qubit] -> Qubit -> Circ()
exp_pq h theta psi ctl = do
  comment_with_label (printf "ENTER: exp_pq (theta=%.3e)" theta) (psi, ctl) ("psi", "ctl")

  for 0 (m-1) 1 $ \p -> do
    for 0 (m-1) 1 $ \q -> do
      when (p >= q) $ do
        one_electron_circuit (theta * h (p,q)) p q psi [ctl]
  comment_with_label "EXIT: exp_pq" (psi, ctl) ("psi", "ctl")
  where
    m = length psi

-- | Apply the two-electron operator [exp -/i/θ/H/], where
-- /H/ = /h/[sub /pqrs/] 
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /r/]/a/[sub /s/] if
-- (/p/,/q/) = (/s/,/r/) and /H/ =
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /r/]/a/[sub /s/] +
-- /a/[sub /s/][sup †]/a/[sub /r/][sup †]/a/[sub /q/]/a/[sub /p/]
-- otherwise, to every quadruple (/p/, /q/, /r/, /s/) of qubits in a 
-- register |ψ〉. To ensure that terms are enumerated exactly once, we
-- only consider indices where (/p/, /q/) ≥ (/s/, /r/) in the
-- lexicographic order (i.e., /p/>/s/ or (/p/=/s/ and /q/≥/r/).  The
-- inputs are Hamiltonian data /h/, the angle θ, the register |ψ〉,
-- and a control qubit.
exp_pqrs :: ((Int,Int,Int,Int) -> Double) -> Double -> [Qubit] -> Qubit -> Circ()
exp_pqrs h theta psi ctl = do
  comment_with_label (printf "ENTER: exp_pqrs (theta=%.3e)" theta) (psi, ctl) ("psi", "ctl")

  for 0 (m-1) 1 $ \p -> do
    for 0 p 1 $ \s -> do  -- constraint p >= s built into the loop for efficiency
      for 0 (m-1) 1 $ \q -> do
        for 0 (m-1) 1 $ \r -> do
          when (p > s || (p == s && q >= r)) $ do
            two_electron_circuit (0.5 * theta * h(p,q,r,s)) p q r s psi [ctl]
  comment_with_label "EXIT: exp_pqrs" (psi, ctl) ("psi", "ctl")
  where
    m = length psi

-- | Like 'exp_pqrs', but use the \"orthodox\" circuit template for
-- the Coulomb operator.
exp_pqrs_orthodox :: ((Int,Int,Int,Int) -> Double) -> Double -> [Qubit] -> Qubit -> Circ()
exp_pqrs_orthodox h theta psi ctl = do
  comment_with_label (printf "ENTER: exp_pqrs_orthodox (theta=%.3e)" theta) (psi, ctl) ("psi", "ctl")

  for 0 (m-1) 1 $ \p -> do
    for 0 p 1 $ \s -> do  -- constraint p >= s built into the loop for efficiency
      for 0 (m-1) 1 $ \q -> do
        for 0 (m-1) 1 $ \r -> do
          when (p > s || (p == s && q >= r)) $ do
            two_electron_circuit_orthodox (0.5 * theta * h(p,q,r,s)) p q r s psi [ctl]
  comment_with_label "EXIT: exp_pqrs_orthodox" (psi, ctl) ("psi", "ctl")
  where
    m = length psi

-- ----------------------------------------------------------------------
-- * Iteration
    
-- $ The following function iterates the basic Trotter timestep
-- /N/[sub /k/] times, and also normalizes the maximum energy 
-- /E/[sub max].

-- | Apply the operator Û[sub k] ≈
-- [exp /iE/[sub max]τ2[sup /k/]][exp -/iH/τ2[sup /k/]] to |ψ〉.
unitary_hat_at :: GSEData    -- ^ The integral data /h/[sub pq] and /h/[sub pqrs].
                  -> Int     -- ^ The Trotter iteration count /N/[sub /k/].
                  -> Double  -- ^ The Hamiltonian scaling parameter τ.
                  -> Double  -- ^ The maximum energy /E/[sub max].
                  -> Bool    -- ^ Use the \"orthodox\" Coulomb operator?
                  -> Int     -- ^ The control qubit index /k/.
                  -> [Qubit] -- ^ The state |ψ〉.
                  -> Qubit   -- ^ The control qubit /b/[sub /k/].
                  -> Circ()
unitary_hat_at gse_data nk tau e_max orth k psi ctl = do
  comment_with_label (printf "ENTER: unitary_hat_at (k=%d, nk=%d)" k nk) (psi, ctl) ("psi", "ctl")
  -- abbreviate tau 2^k:
  let tau2k = tau * 2**(fromIntegral k)

  -- multiply by exp(i E_max tau 2^k)
  gse_T_at (-e_max * tau2k) ctl

  let theta = tau2k / (fromIntegral nk)
  for 1 nk 1 $ \j -> do
    exp_pq h1 theta psi ctl
    if orth 
      then exp_pqrs_orthodox h2 theta psi ctl
      else exp_pqrs h2 theta psi ctl
  
  comment_with_label "EXIT: unitary_hat_at" (psi, ctl) ("psi", "ctl")

  where
    h1 = gse_data_h1 gse_data
    h2 = gse_data_h2 gse_data

-- ----------------------------------------------------------------------
-- * Main circuit

-- $ The main circuit for the GSE Algorithm. This consists of the
-- initial state preparation, the Trotterized phase estimation
-- circuit, the Quantum Fourier Transform, and the final measurement.

-- | The main circuit for the GSE Algorithm.
gse :: Int         -- ^ The number of precision qubits /b/.
       -> Int      -- ^ The number of basis functions /M/.
       -> Int      -- ^ The number of occupied orbitals /N/.
       -> GSEData  -- ^ The integral data /h/[sub pq] and /h/[sub pqrs].
       -> Double   -- ^ The Hamiltonian scaling parameter τ.
       -> Double   -- ^ The maximum energy /E/[sub max].
       -> (Int -> Int) -- ^ The function /k/ ↦ /N/[sub /k/].
       -> Bool     -- ^ Use the \"orthodox\" Coulomb operator?
       -> Circ([Bit])
gse b m o gse_data tau e_max nfun orth = do
    comment "ENTER: gse"
    
    -- set up the state for b and psi
    bstate <- qinit (take b (repeat False))
    psi    <- qinit (take m (repeat False))

    -- apply X gate to the first o 'occupied' qubits of psi
    sequence_ [ gate_X_at q | q <- take o psi ]

    -- put the b register into superposition
    bstate <- mapUnary hadamard bstate

    -- add the U-hat controlled on b
    for 0 (b-1) 1 $ \k -> do
      let nk = nfun k
      unitary_hat_at gse_data nk tau e_max orth k psi (bstate !! k)

    -- apply inverse QFT
    bstate <- (reverse_generic_endo qft_little_endian) bstate

    -- perform measurement
    mk <- measure bstate
    qdiscard psi

    comment_with_label "EXIT: gse" mk "mk"
    return mk
