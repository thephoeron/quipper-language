-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE BangPatterns #-}

-- | This module implements a variant of Fowler's algorithm for
-- optimally approximating any single-qubit gate by Clifford + /T/
-- gates with precision δ [Fowler 2010,
-- <http://arxiv.org/abs/quant-ph/0411206v2>].
-- 
-- This is experimental.

module Programs.Synthesis.Fowler where

import Data.Complex
import Data.List
import System.Random
import System.Environment
import System.IO

-- * Overview 

-- $ We use an exhaustive enumeration of all shortest circuits of a
-- certain length. We use the result by [Matsumoto and Amano 2008,
-- <http://arxiv.org/abs/0806.3834v1>] (rather than the older Fowler
-- method) to avoid duplicate enumeration. By Matsumoto and Amano's
-- result, each operator can be uniquely written in the form
--
-- > BTATATA...TATC,
--
-- where:
--
-- * /A/ is /H/ or /SH/,
--
-- * /B/ is /I/ or /H/ or /SH/,
--
-- * /C/ is any Clifford gate, or more precisely: /C = BDEF/,
--
-- * /D/ is /I/ or /X/,
--
-- * /E/ is /I/ or /S/ or /S/[sup 2] or /S/[sup 3], and
--
-- * /F/ is a global phase in {1, /z/, /z/[sup 2], /z/[sup 3], /z/[sup 4], /z/[sup 5],
-- /z/[sup 6], /z/[sup 7]}, where /z/ = [exp /i/π\/4].
--
-- Since a global phase doesn't matter, we only need to consider the
-- 24 Clifford gates of the form /BDE/, and this way each operator has
-- a unique representation up to global phase.

-- * Scalars

-- | A type to represent complex numbers.
type Complexnumber = Complex Double

-- | A type to represent real numbers.
type Realnumber = Double

-- | The imaginary unit.
i :: Complexnumber
i = 0 :+ 1

-- | The square root of 2.
s :: Complexnumber
s = 1 / sqrt 2

-- | The square root of i.
sqrti :: Complexnumber
sqrti = (1 :+ 1) / sqrt 2

-- * Basic matrix operations

-- | The type of 2×2-matrices of complex numbers. The elements are
-- listed by rows.
type Matrix = (Complexnumber, Complexnumber, Complexnumber, Complexnumber)

-- | Multiply two matrices.
mult :: Matrix -> Matrix -> Matrix
mult (a00, a01, a10, a11) (b00, b01, b10, b11) =
  (c00, c01, c10, c11) where
    !c00 = a00 * b00 + a01 * b10
    !c01 = a00 * b01 + a01 * b11
    !c10 = a10 * b00 + a11 * b10
    !c11 = a10 * b01 + a11 * b11

-- | Take the adjoint of a matrix.
adjoint :: Matrix -> Matrix
adjoint (a00, a01, a10, a11) = (c00, c01, c10, c11) where
  c00 = conjugate a00
  c01 = conjugate a10
  c10 = conjugate a01
  c11 = conjugate a11

-- | Take the trace of a matrix.
trace :: Matrix -> Complexnumber
trace (a00, a01, a10, a11) = a00 + a11

-- * Specific matrices

-- | The identity matrix.
identity :: Matrix
identity = (1, 0, 0, 1)

-- | The Pauli /X/ operator (not-gate).
not_gate :: Matrix
not_gate = (0, 1, 1, 0)

-- | The Hadamard gate /H/.
hadamard :: Matrix
hadamard = (s, s, s, -s) 

-- | The Phase gate /S/.
s_gate :: Matrix
s_gate = (1, 0, 0, i) 
    
-- | The /T/-gate.    
t_gate :: Matrix
t_gate = (1, 0, 0, sqrti) 

-- | Faster version of @mult s_gate@.
s_mult :: Matrix -> Matrix
s_mult (b00, b01, b10 :+ b10i, b11 :+ b11i) = 
  (b00, b01, (-b10i) :+ b10, (-b11i) :+ b11)

-- | Faster version of @mult t_gate@.
t_mult :: Matrix -> Matrix
t_mult (b00, b01, b10, b11) =
  (b00, b01, sqrti * b10, sqrti * b11) 
    
-- * Norms and distance

-- | Calculate the square of the magnitude of a complex number.
magnitude_squared :: Complexnumber -> Realnumber
magnitude_squared (a :+ b) = a*a + b*b

-- | Calculate the Fowler-norm of a unitary matrix /A/, defined as
-- 
-- > norm(A) = sqrt(1 - |tr A| / n),
-- 
-- where /n/ is the dimension.  Note: this norm is with respect to the
-- group structure, i.e., it satisfies norm(/I/) = 0, and the triangle
-- inequality norm(/AB/) ≤ norm(/A/) + norm(/B/), and norm(/A/⁻¹) =
-- norm(/A/). It is invariant under global phase, i.e.,
-- norm(/A/)=norm(/kA/) if /k/ is a complex unit. It is also invariant
-- under basis change.
-- 
-- In case /n/=2, the Fowler norm is actually the same as the operator
-- norm (up to a factor of √2), although this is not mentioned in
-- Fowler's paper. More precisely, recall that the operator norm of a
-- diagonalizable matrix /A/ is given by the magnitude of the largest
-- eigenvalue. For a matrix /A/ and phase /k/, consider the operator
-- norm of /kA-I/, and minimize this over all possible /k/. The
-- result, for diagonalizable /A/, is:
-- 
-- > min {operator-norm(kA-I) | |k|=1} = sqrt(2 - |tr A|),
-- 
-- which is exactly the same as the Fowler norm multiplied by √2.
-- This is important because presumably the \"relevant\" notion of
-- distance in quantum computing is distance in the operator norm up
-- to a global phase.
fowler_norm :: Matrix -> Realnumber
fowler_norm a = sqrt(1 - sqrt(t)/2) where
  t = magnitude_squared(trace(a))

-- | Note that minimizing the Fowler-norm is the same as minimizing
-- −|tr /A/|[sup 2]; the latter requires two fewer square roots to be
-- computed. Therefore, we provide this function for efficiency
-- reasons.
fowler_metric :: Matrix -> Realnumber
fowler_metric a = -magnitude_squared(trace(a))

-- | Convert the Fowler metric to the Fowler norm.
fowler_norm_of_metric :: Realnumber -> Realnumber
fowler_norm_of_metric t = sqrt(1 - sqrt(-t)/2)

-- | Calculate the Euclidean norm of a 2×2 unitary matrix /A/, modulo
-- global phase, defined to be the minimum of |/A/−/kI/|, where /k/ is a
-- unit scalar. It can be defined by:
-- 
-- > norm(A) = sqrt(2 + tr AA[sup +] - 2 |tr A|)
-- 
-- Note: this norm is with respect to the group
-- structure, i.e., it satisfies norm(/I/) = 0, and the triangle
-- inequality norm(/AB/) ≤ norm(/A/) + norm(/B/), and norm(/A/⁻¹) =
-- norm(/A/). It is invariant under global phase, i.e.,
-- norm(/A/)=norm(/kA/) if /k/ is a complex unit. It is also invariant
-- under basis change.
euclid_norm :: Matrix -> Realnumber
euclid_norm a = sqrt(2 + n - 2*t) where
  n = realPart(trace(mult a (adjoint a)))
  t = magnitude(trace a)
  
{- minimize: F = (x-x0)^2 + (y-y0)^2 + (x-x1)^2 + (y-y1)^2, subject to
   x^2 + y^2 = 1.

   dF/dx = 2(x-x0) + 2(x-x1) = 4x - 2(x0+x1) 
   dF/dy = 2(y-y0) + 2(y-y1) = 4y - 2(y0+y1)
   solve: (dF/dx, dF/dy) || (x, y)
   This happens when: (x0+x1, y0+y1) || (x,y)
   I.e.: (x,y) = (x0+x1, y0+y1) / ||(x0+x1, y0+y1)||
   x = (x0+x1) / sqrt ( (x0+x1)^2 + (y0+y1)^2 )
   y = (y0+y1) / sqrt ( (x0+x1)^2 + (y0+y1)^2 )

   In this case, F = (x-x0)^2 + (y-y0)^2 + (x-x1)^2 + (y-y1)^2
   = 2x^2 - 2x(x0+x1) +x0^2 + x1^2 + .....
   = 2(x0+x1)^2 / (x0+x1)^2 + (y0+y1)^2 ) 
     - 2x(x0+x1) + x0^2 + x1^2
   + 2(y0+y1)^2 / (x0+x1)^2 + (y0+y1)^2 )
     - 2y(y0+y1) + y0^2 + y1^2  
   = 2 - 2x(x0+x1) - 2y(y0+y1) + x0^2 + x1^2 + y0^2 + y1^2
   = 2 - 2 (x0+x1)^2 / sqrt ( (x0+x1)^2 + (y0+y1)^2 )
       - 2 (y0+y1)^2 / sqrt ( (x0+x1)^2 + (y0+y1)^2 )
     + x0^2 + x1^2 + y0^2 + y1^2
   = 2 - 2 ((x0+x1)^2 + (y0+y1)^2 ) / sqrt (...) 
     + x0^2 + x1^2 + y0^2 + y1^2 
   = 2 - 2 sqrt((x0+x1)^2 + (y0+y1)^2 ) + x0^2 + x1^2 + y0^2 + y1^2 
-}

-- | Turn a norm into a distance function, defined by
-- 
-- > dist(A,B) = norm(A B[sup +])
dist_of_norm :: (Matrix -> Realnumber) -> (Matrix -> Matrix -> Realnumber)
dist_of_norm norm a b =
  norm (mult a (adjoint b))

-- | Calculate the Fowler distance.
fowler_dist :: Matrix -> Matrix -> Realnumber
fowler_dist = dist_of_norm fowler_norm

-- | Calculate the Euclidean distance.
euclid_dist :: Matrix -> Matrix -> Realnumber
euclid_dist = dist_of_norm euclid_norm

-- * Representation of {/X/, /H/, /S/, /T/} circuits

-- | A type to represent symbolic basis gates (X, H, S, T).
data Gate = X | H | S | T 
          deriving Show

-- * Representation of normal forms

-- | An axis: /I/, /H/, or /SH/. 
data Axis = R_I | R_H | R_SH

-- | A flip: /I/ or /X/.
data Flip = F_I | F_X

-- | A turn: /I/, /S/, /SS/, /SSS/.
data Turn = T_I | T_S | T_SS | T_SSS

-- | Each of the 24 Clifford gates (modulo global phase) can be
-- uniquely specified as a turn followed by a flip and an axis. 
type Clifford = (Axis, Flip, Turn)

-- | The identity Clifford gate.
clifford_id :: Clifford
clifford_id = (R_I, F_I, T_I)

-- | An axis change: /H/ or /SH/.
data CAxis = N_H | N_SH

-- | An element of the Clifford + /T/ group whose normal form does not
-- end in /T/. It consists of a clifford circuit, followed by 0 or more
-- gates of the form /HT/ or /SHT/.
data CliffordT = Clifford Clifford | AppT CAxis CliffordT

-- | An element of the Clifford + /T/ group in normal form. This
-- consists of a 'CliffordT', followed by an optional /T/.
data NormalForm = NF_T CliffordT | NF CliffordT

-- | Class of things that can be converted to a gate list.
class Gatelist a where
  to_gates :: a -> [Gate]

instance Gatelist Axis where
  to_gates R_I = []
  to_gates R_H = [H]
  to_gates R_SH = [S, H]
  
instance Gatelist Flip where
  to_gates F_I = []
  to_gates F_X = [X]

instance Gatelist Turn where
  to_gates T_I = []
  to_gates T_S = [S]
  to_gates T_SS = [S, S]
  to_gates T_SSS = [S, S, S]
  
instance Gatelist CAxis where
  to_gates N_H = [H]
  to_gates N_SH = [S, H]

instance Gatelist CliffordT where
  to_gates (Clifford (x,y,z)) = to_gates x ++ to_gates y ++ to_gates z
  to_gates (AppT x y) = to_gates x ++ (T : to_gates y)
  
instance Gatelist NormalForm where
  to_gates (NF_T x) = T : to_gates x
  to_gates (NF x) = to_gates x

instance Gatelist Gate where
  to_gates x = [x]

instance Show NormalForm where
  show x = concat $ map show (to_gates x)
  
-- | Compute the length of a normal form.
nf_len :: NormalForm -> Int
nf_len (NF_T x) = 1 + ct_len x
nf_len (NF x) = ct_len x

-- | Compute the length of a normal form not ending in /T/.
ct_len :: CliffordT -> Int
ct_len (Clifford (R_I, F_I, T_I)) = 0
ct_len (Clifford x) = 1
ct_len (AppT x y) = 2 + ct_len y

-- * Mapping circuits to unitary matrices

-- | Assign a unitary matrix to a gate.
matrix_of_gate :: Gate -> Matrix
matrix_of_gate X = not_gate
matrix_of_gate H = hadamard
matrix_of_gate S = s_gate
matrix_of_gate T = t_gate
  
-- | Assign a unitary matrix to a gate list.
matrix_of_gatelist :: [Gate] -> Matrix
matrix_of_gatelist [] = identity
matrix_of_gatelist [h] = matrix_of_gate h
matrix_of_gatelist (h:t) = mult (matrix_of_gate h) (matrix_of_gatelist t)
                           
-- | Convert a circuit representation to a matrix
to_matrix :: Gatelist a => a -> Matrix
to_matrix = matrix_of_gatelist . to_gates

-- * More memory-efficient enumeration
    
-- | Uniquely enumerate all normal forms. Return an infinite list of
-- triples (/nf/, /m/, /n/), where /nf/ is a normal form, /m/ is the
-- product of the normal form's matrix and /m0/, and /n/ is the size
-- of the normal form. The list is ordered by increasing /n/. We use
-- an iterated depth-first enumeration with logarithmic memory usage.

nf_matrix_gen :: Matrix -> [(NormalForm, Matrix, Int)]
nf_matrix_gen m0 = aux 0 where
  aux n = nf_length m0 n (aux (n+1))
  
-- | Enumerate all normal forms of size /len/, followed by /tail/.
-- This function is productive, i.e., the resulting list is lazy with
-- no storage.
nf_length :: Matrix -> Int -> [(NormalForm, Matrix, Int)] -> [(NormalForm, Matrix, Int)]
nf_length m0 len tail =  -- enumerate all nf's of size n, followed by tail
  foldr enumerate_under tail base_cases
  where
    base_cases = map (\x -> (x, to_matrix x `mult` m0, ct_len x)) clifford
    clifford = [ Clifford (x,y,z) | x <- [ R_I, R_H, R_SH ],
                                  y <- [ F_I, F_X ],
                                  z <- [ T_I, T_S, T_SS, T_SSS ]]
    -- the enumerate_under function enumerates all 'NormalForm's of
    -- length /len/ under the given 'CliffordT'.
    ht_gate = hadamard `mult` t_gate
    enumerate_under (nf, m, n) tail 
      | n>len = tail
      | n==len = (NF nf, m, n) : tail
      | n==len-1 = (NF_T nf, t_mult m, n+1) : tail
      | otherwise = tail1
        where
          m1 = ht_gate `mult` m
          --m1 = h_mult $ t_mult m
          m2 = s_mult m1
          tail1 = enumerate_under (AppT N_H nf, m1, n+2) tail2
          tail2 = enumerate_under (AppT N_SH nf, m2, n+2) tail

-- * Finding best approximations

-- | Given a norm and a matrix, find the successively best
-- approximation for each length. Return an infinite list of
-- quadruples (/m/, /nf/, /len/, /n/, δ). Here /nf/ is the normal
-- form, /m/ is its matrix, /len/ is the actual length of the normal
-- form, /n/ is the length for which the normal form is optimal, and δ
-- is the distance.
approximate :: (Matrix -> Realnumber) -> Matrix -> [(Matrix, NormalForm, Int, Int, Realnumber)]
approximate norm m0 =
  aux t (m, nf, n, n, norm m)
    where 
      (nf,m,n) : t = nf_matrix_gen m0
      aux ((nf',m',n') : t) (m, nf, len, n, delta) =
        if n' > n then (m, nf, len, n, delta) : remainder else remainder
          where
            delta' = norm m'
            remainder = aux t best
            best = if delta' < delta then (m', nf', n', n', delta') else (m, nf, len, n', delta)
      aux [] _ = undefined   -- not reached, because nf_matrix_gen returns an infinite list

-- * Some gates to approximate
         
-- | Some arbitrary unitary matrix for testing.         
some_gate :: Matrix
some_gate = (0.6, 0.8, 0.8, -0.6)

-- | Return a random unitary matrix (Haar measure).

-- We approximate the Haar measure by repeating some non-uniformly
-- distributed random unitary a large number of times. The matrix is
-- computed of the form HRHRHRHRHR, where H is Hadamard and R is a
-- random Z-rotation.
random_gate :: IO Matrix
random_gate = do 
  list <- sequence (take 100 $ repeat random_Hrot)
  return (foldl1' mult list)
    where
      random_Hrot = do
        alpha <- randomIO :: IO Double
        return $ mult hadamard (zrot_gate (2*pi * alpha))

-- | Return a /Z/-rotation by angle alpha.    
zrot_gate :: Realnumber -> Matrix
zrot_gate alpha =
  (1, 0, 0, cis alpha)

-- | Return a phase rotation gate with phase [exp /i/π \/ 2[sup /d/]].
phase_gate :: Int -> Matrix
phase_gate d = zrot_gate alpha
  where
    alpha = pi / (2 ** (fromIntegral d))

-- * User interface

-- | A convenience function for printing a list, one element per line.
print_list :: (a -> String) -> [a] -> IO()
print_list show_elt [] = return ()
print_list show_elt (h:t) = do
  putStr (show_elt h)
  putStr "\n"
  hFlush stdout
  print_list show_elt t

-- | The main function.
main :: IO()
main = do
    args <- getArgs
    parsed <- parse_args args
    putStrLn $ show parsed
    print_list show_parts $ approximate fowler_metric parsed
    return ()
    where
      show_parts (m, nf, len, n, delta) = show (n, fowler_norm_of_metric delta, len, nf)
    

-- | Parse the command line arguments. Possible arguments are:
-- 
-- * @random_gate@ - approximate a random gate.
-- 
-- * @zrot_gate <double>@ - approximate a /Z/-rotation by angle alpha.  
-- 
-- * @phase_gate <int>@ - approximate a /Z/-rotation gate with angle
-- [exp /i/π \/ 2[sup /d/]].

parse_args :: [String] -> IO Matrix
parse_args args = 
    if (length args < 1) 
    then error "No command line arguments given. Possible arguments are: random_gate, zrot_gate <theta>, phase_gate <n>"
    else let (gate_type:gate_rest) = args
          in case (gate_type) of
            "random_gate" -> random_gate
            "zrot_gate"   -> return $ zrot_gate  (read (gate_rest !! 0) :: Double)
            "phase_gate"  -> return $ phase_gate (read (gate_rest !! 0) :: Int)
            _ -> error $ "Unknown gate type " ++ gate_type

