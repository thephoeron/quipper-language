-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides functions for decomposing a unitary /n/×/n/
-- operator into one- and two-level unitaries. 
-- 
-- The algorithm is adapted from Section 4.5.1 of Nielsen and
-- Chuang. In addition to what is described in Nielsen and Chuang, our
-- algorithm produces two-level operators that can be decomposed using
-- only two Euler angles. The algorithm produces at most /n/(/n/−1)\/2
-- two-level operators of type /R/[sub /z/](δ)/R/[sub /x/](γ), as well
-- as /n/ one-level operators of type [exp /i/θ]. Therefore, the
-- decomposition of a unitary /n/×/n/ operator yields /n/[sup 2] real
-- parameters, which is optimal.

module Libraries.Synthesis.RotationDecomposition where

import Libraries.Synthesis.Matrix
import Libraries.Synthesis.MultiQubitSynthesis
import Libraries.Synthesis.Ring
import Libraries.Synthesis.EulerAngles
import Libraries.Synthesis.ArcTan2

import Data.List
import System.Random

-- ----------------------------------------------------------------------
-- * Elementary rotations

-- | An elementary rotation is either a combined /x/- and
-- /z/-rotation, applied at indices /j/ and /k/, or a phase change
-- applied at index /j/.
-- 
-- * 'ERot_zx' δ γ /j/ /k/ represents the operator 
-- /R/[sub /z/](δ)/R/[sub /x/](γ), applied to levels /j/ and /k/.
-- 
-- \[image ERot_zx.png]
-- 
-- * 'ERot_phase' θ /j/ represents the operator [exp /i/θ] applied to level
-- /j/.
-- 
-- \[image ERot_phase.png]
-- 
-- Note: when we use a list of 'ElementaryRot's to express a sequence of
-- operators, the operators are meant to be applied right-to-left,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
data ElementaryRot a = 
  ERot_zx a a Index Index
  | ERot_phase a Index
    deriving (Show)

-- | Convert a symbolic elementary rotation to a concrete matrix.
matrix_of_elementary :: (Ring a, Floating a, Nat n) => ElementaryRot a -> Matrix n n (Cplx a)
matrix_of_elementary (ERot_zx delta gamma j k) = 
  twolevel_matrix (a, b) (c, d) j k where
  a = ed' * cg
  b = -i * ed' * sg
  c = -i * ed * sg
  d = ed * cg
  cg = Cplx (cos (gamma/2)) 0
  sg = Cplx (sin (gamma/2)) 0
  ed = Cplx cd sd
  ed' = Cplx cd (-sd)
  cd = cos (delta/2) 
  sd = sin (delta/2)
matrix_of_elementary (ERot_phase theta j) = 
  onelevel_matrix (Cplx c s) j where
    c = cos theta
    s = sin theta

-- | Convert a sequence of elementary rotations to an /n/×/n/-matrix.
matrix_of_elementaries :: (Ring a, Floating a, Nat n) => [ElementaryRot a] -> Matrix n n (Cplx a)
matrix_of_elementaries ops =
  foldl' (*) 1 [ matrix_of_elementary op | op <- ops ]

-- ----------------------------------------------------------------------
-- * Decomposition into elementary rotations

-- | Convert an /n/×/n/-matrix to a sequence of elementary rotations.
-- 
-- Note: the list of elementary rotations will be returned in
-- right-to-left order, i.e., as in the mathematical notation for
-- matrix multiplication.  This is the opposite of the quantum circuit
-- notation.
rotation_decomposition :: (Eq a, Fractional a, Floating a, Adjoint a, ArcTan2 a, Nat n) => Matrix n n (Cplx a) -> [ElementaryRot a]
rotation_decomposition op = concat gates ++ reverse gates' where
  (op', gates) = mapAccumL rowop op [ (i,j) | j <- [0..n-2], i <- [j+1..n-1] ]
  gates' = [ get_phase op' i | i <- [0..n-1] ]
  (n', _) = matrix_size op
  n = fromInteger n'

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | Construct a two-level /n/×/n/-matrix from a given 2×2-matrix and
-- indices /j/ and /k/.
twolevel_matrix_of_matrix :: (Ring a, Nat n) => Matrix Two Two a -> Index -> Index -> Matrix n n a
twolevel_matrix_of_matrix u j k = op where
  op = twolevel_matrix (a,b) (c,d) j k
  ((a,b), (c,d)) = from_matrix2x2 u
  
-- | Extract the phase of the /j/th diagonal entry of the given
-- matrix.
get_phase :: (ArcTan2 a) => Matrix n n (Cplx a) -> Index -> ElementaryRot a
get_phase op j = ERot_phase theta j where
  a = matrix_index op j j
  theta = arctan2 y x
  Cplx x y = a
             
-- | Perform a two-level operation on rows /j/ and /k/ of a matrix /U/,
-- such that the resulting matrix has a 0 in the (/j/,/k/)-position.
-- Return the inverse of the two-level operation used, as well as the
-- updated matrix.
rowop :: (Eq a, Fractional a, Floating a, Adjoint a, ArcTan2 a, Nat n) => Matrix n n (Cplx a) -> (Index, Index) -> (Matrix n n (Cplx a), [ElementaryRot a])
rowop op (j,k) 
  | b == 0 = (op, [])
  | otherwise = (op', gates) 
  where
    a = matrix_index op k k
    b = matrix_index op j k
    matrix = 1/Cplx (sqrt(real (a * adj a + b * adj b))) 0 `scalarmult` matrix2x2 (adj a, adj b) (b, -a)
    (alpha, beta, gamma, delta) = euler_angles matrix
    matrix2 = matrix_of_euler_angles (0, 0, gamma, delta)
    op' = twolevel_matrix_of_matrix matrix2 k j .*. op
    gates = [ ERot_zx (-delta) (-gamma) k j ]

-- ----------------------------------------------------------------------
-- * Testing

-- | Return a \"random\" unitary /n/×/n/-matrix. These matrices will
-- not quite be uniformly distributed; this function is primarily
-- meant to generate test cases. 
random_unitary :: (RandomGen g, Nat n, Floating a, Random a) => g -> Matrix n n (Cplx a)
random_unitary g = op where
  op = matrix_of_elementaries gates
  gates = random_gates g (20*n^2)
  random_gates g 0 = []
  random_gates g m = h:t where
    (gamma, g1) = randomR (0, 2*pi) g
    (delta, g1') = randomR (0, 2*pi) g1
    (c, g2) = randomR (0, 1) g1'
    (j, g3) = randomR (0, n-2) g2
    (k, g4) = randomR (j+1, n-1) g3
    h = case c :: Int of
      0 -> ERot_zx delta gamma j k
      _ -> ERot_phase delta j
    t = random_gates g4 (m-1)
  (n', _) = matrix_size op
  n = fromInteger n'

-- | Generate a random matrix, decompose it, and then re-calculate the
-- matrix from the decomposition.
test :: IO ()
test = do
  g <- newStdGen
  let m = random_unitary g :: Matrix Four Four CDouble
  let gates = rotation_decomposition m
  let m' = matrix_of_elementaries gates :: Matrix Four Four CDouble
  putStrLn $ "m = " ++ show m
  putStrLn $ "gates = " ++ show gates
  putStrLn $ "m' = " ++ show m'
  
