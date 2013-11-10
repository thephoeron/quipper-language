-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides functions for converting between matrices in
-- /U/(2) and their Euler angle representation.

module Libraries.Synthesis.EulerAngles where

import Libraries.Synthesis.Ring
import Libraries.Synthesis.Matrix
import Libraries.Synthesis.ArcTan2

-- ----------------------------------------------------------------------
-- * Documentation

-- | Decompose a unitary operator /U/ into Euler angles (α, β, γ, δ).
-- These angles are computed so that
-- 
-- * /U/ = [exp /i/α] R[sub /z/](β) R[sub /x/](γ) R[sub /z/](δ).
euler_angles :: (Floating a, ArcTan2 a) => Matrix Two Two (Cplx a) -> (a, a, a, a)
euler_angles op = (alpha, beta, gamma, delta) where
  ((a, b), (c, d)) = from_matrix2x2 op
  beta_plus_delta_over_2 = phase d - alpha
  beta_minus_delta_over_2 = phase c - alpha + pi/2
  alpha = phase (a*d - b*c) / 2
  gamma = 2 * arctan2 (mag b) (mag a)
  delta = phase (b * d * i * adj (a*d - b*c))
  beta = 2 * phase (d * cis (-alpha - delta/2) + c * cis (-alpha+delta/2) * i)

  mag (Cplx a b) = sqrt (a^2 + b^2)
  phase (Cplx a b) = arctan2 b a

  cis x = Cplx (cos x) (sin x)

  adj (Cplx x y) = Cplx x (-y)

-- | Compute the operator
-- 
-- * /U/ = [exp /i/α] R[sub /z/](β) R[sub /x/](γ) R[sub /z/](δ).
-- 
-- from the given Euler angles.
matrix_of_euler_angles :: (Floating a) => (a, a, a, a) -> Matrix Two Two (Cplx a)  
matrix_of_euler_angles (alpha, beta, gamma, delta) = op where
  op = opa * opb * opc * opd
  opa = cplx_cis alpha `scalarmult` 1
  opb = zrot beta
  opc = hadamard * zrot gamma * hadamard
  opd = zrot delta
  
  cplx_cis theta = Cplx (cos theta) (sin theta)
  hadamard = Cplx (sqrt 0.5) 0 `scalarmult` matrix2x2 (1, 1) (1, -1)
  zrot gamma = matrix2x2 (cplx_cis (-gamma/2), 0) (0, cplx_cis (gamma/2))

  
