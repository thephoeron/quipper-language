-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides global definitions for 
-- the Unique Shortest Vector algorithm.

module Algorithms.USV.Definitions where

import Quipper
import QuipperLib.Arith

import Control.Monad (foldM, zipWithM, replicateM)
import qualified Math.Lattices.LLL 
import Data.Array
import Data.List (mapAccumL)
import Data.Numbers.Primes
import System.Random
import qualified Data.Map as Map
import Data.Map (Map)


-- ==============================================================
-- * Types for the Unique Shortest Vector algorithm 

-- | An input to 'tPP': a pair of a 'Qubit' and a list
-- of 'QDInt's. Holds a superposition of two vectors with an
-- unknown fixed difference.
type TwoPoint = (Qubit, [QDInt])

-- | An input to 'dCP': a pair of a 'Qubit' and a
-- 'QDInt'. Holds a superposition of two numbers with an
-- unknown fixed difference.
type CosetState = (Qubit, QDInt)

-- | An input to 'sieving': a pair of a 'Qubit' and an 
-- integer. Holds a state of the form:
--
-- \[image CosetState.png] 
--
-- together with the integer /k/.
type Psi_k = (Qubit, Int)


-- ==============================================================
-- * General purpose functions

-- | Concatenate two pairs of lists componentwise. 
concat_pair :: ([a],[b]) -> ([a],[b]) -> ([a],[b])
concat_pair (i,j) (k,l) = (i ++ k, j ++ l)

-- | Construct a list of random number generators.
multi_split :: StdGen -> [StdGen]
multi_split gen = gen1 : multi_split gen2 where
  (gen1, gen2) = split gen

-- | Given a list /l/, a predicate /p/ and an error message /msg/, 
-- return a pair (/a/,/l'/) where /a/ is the first element 
-- of /l/ satisfying /p/ and /l'/ is the remaining list. 
-- If no such element exists, raise an error and display /msg/.
find :: [a] -> (a -> Bool) -> String -> (a, [a])
find [] condition msg = error msg
find (a:as) condition msg =
  if (condition a) then (a,as)
  else (b,(a:bs))
    where 
      (b,bs) = find as condition msg

-- | Given a list /l/ and a predicate /p/, return a pair
-- (/l1/, /l2/) where /l1/ contains the elements of /l/ 
-- satisfying /p/ and /l2/ the others.
separate :: [a] -> (a -> Bool) -> ([a], [a])
separate [] condition = ([],[])
separate (h:t) condition =
  if (condition h) then concat_pair ([h],[]) (separate t condition)
  else concat_pair ([],[h]) (separate t condition)

-- | Given integers /m/ and /n/, compute the 
-- big-endian expansion of /m/ in base /n/.
expand :: Integer -> Integer -> [Integer]
expand _ n | n <= 1 = error ("Cannot expand a number in base " ++ show n ++ ".")
expand 0 n = [0]
expand m n = reverse $ expand_aux m n [] 
  where
    expand_aux 0 n l = l
    expand_aux m n l = (m-s) : expand_aux r n l where
      r = m `div` n
      s = n*r

-- | Discard a list of 'Psi_k's
qdiscard_psi_ks :: [Psi_k] -> Circ ()
qdiscard_psi_ks l = do
  mapM (\(q,n) -> do
    qdiscard q
    return ()) l
  return ()

-- | Given a list of people, and a function assigning a religion to
-- each person, divide the people into couples of the same religion.
-- Some people will remain single if there isn't a suitable
-- partner. Return a list of couples and a list of single people.
-- 
-- The algorithm proceeds as follows. We have a room for each
-- religion. Initially the rooms are empty. As each person arrives,
-- they go to their room. If the room is empty, they stay there. If
-- the room is occupied, they marry the occupant and join the list
-- of couples. At the end, all single people are retrieved from
-- their rooms.
-- 
-- This function is lazy, i.e., couples are formed as they are
-- found. Only the singles have to wait until the end of the list.
-- 
-- Running time is O(/n/ log /n/).
find_partners :: (Ord b) => (a -> b) -> [a] -> ([(a,a)], [a])
find_partners f = find_partners_in_rooms Map.empty
  where
    --find_partners_in_rooms :: Map b a -> [a] -> ([(a,a)], [a])
    find_partners_in_rooms rooms [] = ([], Map.elems rooms)
    find_partners_in_rooms rooms (a:as) =
      case Map.lookup (f a) rooms of
        Just c -> ((a,c):pairs, singles)
          where (pairs, singles) = find_partners_in_rooms rooms' as
                rooms' = Map.delete (f a) rooms
        Nothing -> find_partners_in_rooms rooms' as
          where rooms' = Map.insert (f a) a rooms 


-- ==============================================================
-- * Linear algebra

-- | Compute the Euclidean norm of a vector.
norm :: [Integer] -> Float
norm v = sqrt $ fromIntegral $ foldl (+) 0 $ map (\x -> x^2) v

-- | Compute the sum of two vectors.
vector_add :: Num a => [a] -> [a] -> [a] 
vector_add u v = zipWith (+) u v

-- | Quantum version of 'vector_add'.
q_vector_add :: [QDInt] -> [QDInt] -> Circ [QDInt]
q_vector_add u v = do
  w <- zipWithM q_add u v
  return (map (\(_,_,z) -> z) w)

-- | Compute the multiplication of a scalar with a vector.
scalar_mult :: Num a => a -> [a] -> [a]
scalar_mult n v = map (\x -> n*x) v

-- | Quantum version of 'scalar_mult'.
q_scalar_mult :: QDInt -> [QDInt] -> Circ [QDInt]
q_scalar_mult a v = do
  v' <- mapM (\u -> do
    (_,_,z) <- q_mult a u
    return z) v
  return v'

-- | Multiply an /n/×/m/-matrix by an /m/-dimensional column 
-- vector to obtain an /n/-dimensional column vector. The 
-- matrix is represented as a list of /m/ columns. 
-- 
-- Precondition: /m/ > 0.
-- 
-- Example:
-- 
-- > matrix_mult [[1,2,3],[1,0,0]] [1,1] = [2,2,3]
matrix_mult :: [[Integer]] -> [Integer] -> [Integer]
matrix_mult m a = foldl vector_add zero $ zipWith scalar_mult a m
  where
    zero = replicate (length (head m)) 0

-- | Quantum version of 'matrix_mult'.
q_matrix_mult :: [[QDInt]] -> [QDInt] -> Circ [QDInt]
q_matrix_mult m a = do
  let l1 = length (head m)
      l2 = qdint_length (head a)
  zero <- qinit (replicate l1 (intm l2 0))
  m <- zipWithM q_scalar_mult a m
  result <- foldM q_vector_add zero m
  return result

-- | Check whether a vector is 0.
is_zero_vector :: [Integer] -> Bool
is_zero_vector = all (== 0)


-- ==============================================================
-- * Euclid's algorithm

-- | The extended Euclidean algorithm. 'ext_euclid' /a/ /b/ returns
-- (/x/, /y/, /z/, /w/, /d/) such that:
-- 
-- * 0 ≤ /d/ = gcd(/a/, /b/), the greatest common divisor of /a/ and
-- /b/;
-- 
-- * /ax/ + /by/ = /d/;
-- 
-- * /az/ + /bw/ = 0;
-- 
-- * the determinant /xw/ - /yz/ = 1.
ext_euclid :: Integer -> Integer -> (Integer, Integer, Integer, Integer, Integer)
ext_euclid a b = ext_euclid_rec 1 0 0 1 a b 1 where
  
  -- the invariants for ext_euclid_rec are:
  -- 
  -- [ x y ] [ a ]  =  [ r ]
  -- [ z w ] [ b ]     [ s ]
  -- 
  -- and det [[x y] [z w]] = t = ±1.
  
  ext_euclid_rec x y z w r s t | r < 0 =
    ext_euclid_rec (-x) (-y) z w (-r) s (-t)
  ext_euclid_rec x y z w r s t | s < 0 = 
    ext_euclid_rec x y (-z) (-w) r (-s) (-t)
  ext_euclid_rec x y z w r s t | r < s = 
    ext_euclid_rec z w x y s r (-t)
  ext_euclid_rec x y z w r s t | 0 < s =
    ext_euclid_rec z w (x-q*z) (y-q*w) s (r-q*s) (-t)
    where q = r `div` s
  ext_euclid_rec x y z w r s t = -- Note: s = 0, r ≥ 0.
    (x, y, t*z, t*w, r)


-- ==============================================================
-- * Classical subroutines 

-- | Reduce a basis using the Lenstra-Lenstra-Lováscz algorithm.
--
-- Uses the corresponding Haskell library. 
lll :: [[Integer]] -> [[Integer]]
lll bb = bb_reduced_integral
  where
    bb_rational = map (\v -> map toRational v) bb
    bb_reduced = Math.Lattices.LLL.lll bb_rational
    bb_reduced_integral = map (\v -> map ceiling v) (elems bb_reduced)

-- | Given an integer /m/, find the smallest prime /p/ such that /m/ ≤
-- /p/ ≤ 2/m/.
-- 
-- Uses preexisting 'isPrime' algorithm. 
find_prime :: Int -> Int
find_prime m = head $ filter isPrime [(m)..(2*m)]

-- | Given a vector /u/ and a basis /bb/ = [/b/[sub 0], …, 
-- /b/[sub /n/-1]], determine whether /u/ belongs to the lattice
-- generated by /bb/, i.e., whether there exist integers /a/[sub 0],
-- …, /a/[sub /n/-1] such that /u/ = /a/[sub 0]/b/[sub 0] + … +
-- /a/[sub /n/-1]/b/[sub /n/-1]. 
-- 
-- Precondition: /u/ and /b/[sub 0], …, /b/[sub /n/-1] must all be
-- of the same dimension.
-- 
-- The algorithm proceeds as follows: first, do invertible integer
-- column operations on /b/[sub 0], …, /b/[sub /n/-1] until the top
-- entries of /b/[sub 1], …, /b/[sub /n/-1] are 0. This can be done
-- efficiently by using the extended Euclidean algorithm for two
-- columns at a time. Then check whether the top entry of /b/[sub 0]
-- divides the top entry of /u/. If no, output 'False'. Otherwise, if
-- the top entry of /b/[sub 0] is 0, drop the top row and continue
-- recursively. Otherwise, subtract an appropriate multiple of 
-- /b/[sub 0] from /u/, drop /b/[sub 0], drop the top row, and
-- continue recursively. Trivial base cases occur when the number of
-- rows or columns reaches 0.
is_in_lattice :: [Integer] -> [[Integer]] -> Bool
is_in_lattice [] bb = True
is_in_lattice u [] = is_zero_vector u
is_in_lattice (u0:us) (b0:bs) =
  let (c00:c0s, cs) = mapAccumL column_op b0 bs in
  if c00 == 0 
  then if u0 /= 0 
       then False 
       else is_in_lattice us (c0s:cs)
  else if u0 `mod` c00 /= 0
       then False
       else 
         let q = u0 `div` c00    
             us' = us `vector_add` ((-q) `scalar_mult` c0s)
         in is_in_lattice us' cs

-- | Given a basis /bb/ = [/b/[sub 0], …, /b/[sub /n/-1]], find
-- another equivalent basis whose elements are linearly independent.
reduce_lattice :: [[Integer]] -> [[Integer]]
reduce_lattice [] = []
reduce_lattice ([]:bs) = []
reduce_lattice (b0:bs) =
  let (c0, cs) = mapAccumL column_op b0 bs in
  case c0 of
    0 : c0s -> [ 0:x | x <- reduce_lattice (c0s:cs) ]
    _  -> c0 : [ 0:x | x <- reduce_lattice cs ]
  
-- | Perform a reversible column operation on two integer vectors,
-- creating (and then dropping) a leading zero in the second vector.
column_op :: [Integer] -> [Integer] -> ([Integer], [Integer])
column_op (m:ms) (n:ns) = (m':ms', ns') where
  (x, y, z, w, d) = ext_euclid m n
  m' = x*m + y*n  -- m' == d by extended Euclid's algorithm
  n' = z*m + w*n  -- n' == 0 by extended Euclid's algorithm
  ms' = (x `scalar_mult` ms) `vector_add` (y `scalar_mult` ns)
  ns' = (z `scalar_mult` ms) `vector_add` (w `scalar_mult` ns)
column_op _ _ = error "is_in_lattice: dimension mismatch"

