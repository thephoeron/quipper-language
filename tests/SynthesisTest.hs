-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | Some demos for "QuipperLib.Synthesis".

import Quipper
import QuipperLib.Synthesis

import Quantum.Synthesis.Ring
import Quantum.Synthesis.Matrix
import Quantum.Synthesis.MultiQubitSynthesis

import System.Random

-- ----------------------------------------------------------------------
-- * Some demos for QuipperLib.Synthesis

-- | Import a compressed Clifford+/T/ operator as a Quipper circuit.
main1 :: IO ()
main1 = do
  print_simple Preview (exact_synthesis1 (0x1d00d27a0188b095b8cdd4ead9a244198d8b22e :: Integer))
  
-- | Exact synthesis of a Clifford+/T/ circuit from an exact matrix
-- representation.
main2 :: IO ()
main2 = do
  print_simple Preview (exact_synthesis1 op)
  where
    op :: Matrix Two Two DOmega
    op = roothalf^4 * matrix2x2 ( 1 - 2*roottwo,    2 + roottwo - i )
                                ( -2 - roottwo - i, 1 - 2*roottwo   )

-- | Exact synthesis of a multi-qubit Clifford+/T/ circuit from an
-- exact matrix representation.
main3 :: IO ()
main3 = do
  print_generic Preview (exact_synthesis_alt op) [qubit, qubit]
  where
    op :: Matrix Four Four DOmega
    op = matrix4x4 ( 1,  0,  0, 0 )
                   ( 0, -s,  s, 0 )
                   ( 0,  0,  0, 1 )
                   ( 0,  s,  s, 0 ) 
    s = roothalf
    
-- | Exact synthesis of a multi-qubit Clifford+/T/ circuit from an
-- exact matrix representation.
main3a :: IO ()
main3a = do
  print_generic Preview (exact_synthesis_alt op) [qubit, qubit, qubit]
  where
    op :: Matrix Eight Eight DOmega
    op = matrix [[ 1, 0,  0, 0, 0, 0, 0, 0 ],
                 [ 0, s, -s, 0, 0, 0, 0, 0 ],
                 [ 0, 0,  0, 1, 0, 0, 0, 0 ],
                 [ 0, s,  s, 0, 0, 0, 0, 0 ],
                 [ 0, 0,  0, 0, 1, 0, 0, 0 ],
                 [ 0, 0,  0, 0, 0, 1, 0, 0 ],
                 [ 0, 0,  0, 0, 0, 0, 0, 1 ],
                 [ 0, 0,  0, 0, 0, 0, 1, 0 ]] 
    s = roothalf
    
-- | Approximate synthesis of a /z/-rotation as a Clifford+/T/ circuit.
-- Angle θ = π\/128, precision ε = 10[sup −30].
main4 :: IO ()
main4 = do
  g <- newStdGen  -- a source of randomness
  print_simple Preview (approximate_synthesis_zrot prec (pi/128) g)
  where
    prec = 30 * digits

-- | Approximate synthesis of a global phase. 
-- Angle α = π\/128, precision ε = 10[sup −30].
main5 :: IO ()
main5 = do
  g <- newStdGen  -- a source of randomness
  print_simple Preview (approximate_synthesis_phase True prec (pi/128) g)
  where  
    prec = 30 * digits

-- | Approximate synthesis of an arbitrary single-qubit operator,
-- given by Euler angles. Precision ε = 2[sup −50].
main6 :: IO ()
main6 = do
  g <- newStdGen  -- a source of randomness
  let circ = approximate_synthesis_euler True prec (alpha, beta, gamma, delta) g
  print_simple Preview circ
  where
    prec = 50 * bits
    alpha = 0.1 * pi
    beta = 0.2 * pi
    gamma = 0.5 * pi
    delta = -0.6 * pi
    
-- | Approximate synthesis of an arbitrary single-qubit operator,
-- given as a matrix. The matrix is given in an exact notation.
-- Precision ε = 10[sup −10].
main7 :: IO ()
main7 = do
  g <- newStdGen  -- a source of randomness
  let circ = approximate_synthesis_u2 True prec op g
  print_simple Preview circ
  where
    prec = 10 * digits
    op = matrix2x2 ( 0.6, 0.8*i )
                   (-0.8, 0.6*i )

-- | Run any of the above main functions:
main = main3a
