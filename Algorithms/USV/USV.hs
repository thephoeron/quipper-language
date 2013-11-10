-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides an implementation of the 
-- main Unique Shortest Vector algorithm.

module Algorithms.USV.USV where

import Quipper
import QuipperLib.QFT
import QuipperLib.Arith
import Libraries.Sampling

import Algorithms.USV.Definitions

import Control.Monad (foldM, zipWithM, replicateM)
import Data.Maybe
import System.Random
import Text.Printf

import Libraries.Auxiliary


-- ==============================================================
-- * Coherent arithmetic

-- $ Some arithmetic functions used in the reductions of the /USV/ to 
-- the /TPP/ and of the /TPP/ to the /DCP/.

-- | Compute the function /f/, that selects a subset
-- of lattice points. It is defined as:
-- 
-- \[image def_f.png]
-- 
-- The arguments are: 
-- 
-- * /bb_bar/, an /n/-dimensional matrix;
-- 
-- * /p/, a prime such that /n/ ≤ /p/ ≤ 2/n/;
--
-- * /m/, an integer such that /1/ ≤ /m/ ≤ /p-1/;
--
-- * /i0/, an integer index such that /0/ ≤ /i0/ ≤ /n-1/;
-- 
-- * /t/, an integer (either /0/ or /1/);
--
-- * /a/=(/a/[sub 1],...,/a/[sub /n/]), an integer vector.
f_classical :: [[Integer]] -> Int -> Int -> Int -> (Int,[Int]) -> [Integer]
f_classical bb p m i0 (t,a) = matrix_mult bb a' 
  where
    a' = map toInteger $ applyAt i0 (\x -> x*p + t*m) a

-- | Quantum version of 'f_classical'. 
f_quantum :: [[Integer]] -> Int -> Int -> Int -> TwoPoint -> Circ [QDInt]
f_quantum bb p m i0 = box "f" $ \(t,a) -> do
  comment_with_label "ENTER: f_quantum" (t,a) ("t","a")
  let n = (length . head) bb
      b = maximum (map maximum bb)
      s = ceiling (logBase 2 (fromIntegral b)) + 5*n

  qp <- qinit (intm s (toInteger p))
  qm <- qinit (intm s (toInteger m))
  qbb <- qinit (map (\vs -> (map (\v -> (intm s v)) vs)) bb)
  a <- mapM (\x -> qdint_extend_signed s x) a

  let ai0 = a !! i0
  (_,_,x) <- q_mult ai0 qp
  q_add_in_place x qm `controlled` t
  let a' = overwriteAt i0 x a

  result <- q_matrix_mult qbb a'
  comment_with_label "EXIT: f_quantum" (qp,qm,qbb,t,a) ("qp","qm","qbb","t","a")
  return result


-- | Compute the function /g/ defined as:
-- 
-- \[image def_g1.png]
-- 
-- The arguments are: 
-- 
-- * /l/, an integer (in principle, a real number, but the 
-- GFI only uses integer values);
-- 
-- * /w/, a real number in the interval [0,1);
-- 
-- * /v/, an integer.
-- 
-- We note that in the quantum version of this function, /l/
-- and /w/ will be parameters, and /v/ will be a quantum 
-- input. We implement this operation using only integer
-- division, using the following property: for all integers
-- /v/, /m/ and real numbers /w/, 
-- 
-- \[image floor2.png]
g1_classical :: Integer -> Double -> Integer -> Integer
g1_classical l w v = 
  let m = 128 * l
      c = ceiling (fromIntegral m * w) 
  in
   (v - c) `div` m

-- | Compute the function /g/. The function /g/ 
-- partitions the space into hypercubes of size
-- 128/l/ at a random offset /w/. It is defined as:
-- 
-- \[image def_g.png]
-- 
-- This is just the componentwise application of 'g1_classical'.
g_classical :: Integer -> [Double] -> [Integer] -> [Integer]
g_classical l w v = zipWith (g1_classical l) w v

-- | Quantum version of 'g1_classical'.
g1_quantum :: Integer -> Double -> QDInt -> Circ QDInt
g1_quantum l w = box "g_1" $ \v -> do
  comment_with_label "ENTER: g1_quantum" v "v"
  let m = fromIntegral (128 * l)
      c = ceiling (fromIntegral m * w)
      l' = qdint_length v
  c' <- qinit (intm l' c)
  (_, _, n) <- q_sub v c'
  m' <- qinit (intm l' m)
  (_, _, q) <- q_div n m'
  comment_with_label "EXIT: g1_quantum" (v,c',m',n,q) ("v","c'","m'","n","q") 
  return q

-- | Quantum version of 'g_classical'.
g_quantum :: Integer -> [Double] -> [QDInt] -> Circ [QDInt]
g_quantum l w = box "g" $ \v -> do 
  zipWithM (g1_quantum l) w v


-- | Compute the function /h/, defined as:
-- 
-- \[image def_h.png]
-- 
-- The function /h/ transforms a vector /a/=(/a/[sub 1],...,/a/[sub n]) 
-- of 4/n/-bit integers into a 4/n/[super 2]+/n/-bit integer by 
-- inserting a 0 between each component of /a/. 
h_classical :: [IntM] -> IntM
h_classical v = (intm (4*n^2+n) w)
  where
    n = length v 
    m = 4*n + 1
    mm = 2^m 
    v' = map integer_of_intm_unsigned v
    w = foldl (+) 0 $ zipWith (*) v' [mm^k | k <- [0..(n-1)]]

-- | Quantum version of 'h_classical'. 
h_quantum :: [QDInt] -> Circ QDInt
h_quantum a = do
  comment_with_label "ENTER: h_quantum" a "a"
  a <- mapM (extend . qulist_of_qdint_bh) (reverse a)
  comment_with_label "EXIT: h_quantum" a "a"
  return (qdint_of_qulist_bh (concat a))
  where
    -- | Prepend a qubit in state |0> to a list of qubits.
    extend :: [Qubit] -> Circ [Qubit]
    extend x = do
      z <- qinit False
      return (z : x)


-- ==============================================================
-- * Algorithm 1: \"uSVP\"

-- | Find the shortest vector. The argument, /bb/, is an 
-- /n/-dimensional integer matrix. The algorithm first uses
-- /bb/ to generate a list of parameter tuples and then 
-- recursively goes through this list by calling 'algorithm_Q'
-- on each tuple until it either finds the shortest vector
-- or exhausts the list and fails by returning 0.
-- 
-- Remark: 
-- 
-- * Argument /n/ is redundant, it can be inferred from /bb/.
uSVP :: [[Integer]] -> Circ [Integer]
uSVP bb = do

  -----------------------------------------------------------------
  -- Prepare the list of parameter values,
  -- and a random number generator.
  ----------------------------------------------------------------- 
  comment "ENTER: algorithm_uSVP"
  let n = length bb
      randomgen = mkStdGen n
      p = find_prime (n^3)
      bb_bar = (lll . reduce_lattice) bb
      b1 = head bb_bar
      l1 = norm b1
      k = ceiling $ fromIntegral $ (n - 1) `div` 2
      ls = [ceiling (l1 / (2^s)) | s <- [0..k] ]
      parameters = [(l, m, i0, p) | l <- ls, 
                                     m <- [1..(p-1)], 
                                     i0 <- [0..(n-1)]]

  -----------------------------------------------------------------
  -- Conditional recursion over the list of parameters
  -- using the function 'usvp_aux'.
  ----------------------------------------------------------------- 
  v <- usvp_aux n bb_bar parameters randomgen
  comment "EXIT: algorithm_uSVP"
  return v

-----------------------------------------------------------------
-- | For each tuple of parameters, call 'algorithm_Q' and 
-- then test whether the returned vector is the shortest vector 
-- in the lattice. If it is, return it. If not, move on to 
-- the next tuple. If the end of the list is reached, return 0.
--
-- Remark:
-- 
-- * The algorithm takes as additional argument a random number 
-- generator. At each iteration, a new seed is extracted and used
-- by the next iteration's generator.
----------------------------------------------------------------- 
usvp_aux :: Int -> [[Integer]] -> [(Int, Int, Int, Int)] -> StdGen -> Circ [Integer]
usvp_aux n b [] randomgen = return (replicate n 0)
usvp_aux n b (h:t) randomgen = do
  let (g1,g2) = split randomgen
  u <- algorithm_Q b h g1
  if (is_in_lattice u b) then return u
                         else usvp_aux n b t g2


-- ==============================================================
-- * Algorithm 2: \"Q\"

-- | Compute 'algorithm_Q'. The arguments are:
-- 
-- * /bb_bar/, an /n/-dimensional LLL-reduced basis;
-- 
-- * (/l/,/m/,/i0/,/p/), a 4-tuple of integer parameters;
-- 
-- * /randomgen/, a random number generator.
-- 
-- The algorithm first calls algorithm 'algorithm_R' to prepare
-- a list of 'TwoPoint's parameterized on (/l/,/m/,/i0/,/p/) and 
-- then calls 'tPP' on this list. With high probability, the 
-- returned vector is the shortest vector in the lattice up to 
-- one component. 
--
-- Remark: 
-- 
-- * Argument /n/ is redundant, it can be inferred 
-- from /bb_bar/.
algorithm_Q :: [[Integer]] -> (Int, Int, Int, Int) -> StdGen -> Circ [Integer]
algorithm_Q bb_bar (l, m, i0, p) randomgen = do
  -----------------------------------------------------------------
  -- Extract (4*n^2+n) random number generators
  ----------------------------------------------------------------- 
  comment "ENTER: algorithm_Q"
  let n = length bb_bar
      generators = take (4*n^2+n) $ multi_split randomgen

  -----------------------------------------------------------------
  -- Call algorithm 'r' to prepare a list of 'TwoPoint's
  -- using the given parameters and a random number generator.
  ----------------------------------------------------------------- 
  states <- sequence [algorithm_R bb_bar l m i0 p g | g <- generators]

  -----------------------------------------------------------------
  -- Run tpp to get the shortest vector up to i0-th component.
  ----------------------------------------------------------------- 
  u <- tPP n states

  -----------------------------------------------------------------
  -- Adjust i0-th component and return the vector.
  ----------------------------------------------------------------- 
  comment "EXIT: algorithm_Q"
  return $ applyAt i0 (\x -> x*(toInteger p) + (toInteger m)) u


-- ==============================================================
-- * Algorithm 3: \"R\"

-- | Compute 'algorithm_R'. The arguments are: 
-- 
-- * /bb_bar/, an /n/-dimensional LLL-reduced basis,
-- 
-- * /l/, an integer approximation of the length of the 
-- shortest vector,
-- 
-- * /p/, a prime such that /n/ ≤ /n/ ≤ 2/n/,
-- 
-- * /m/, an integer such that /1/ ≤ /m/ ≤ /p-1/,
-- 
-- * /i0/, an integer index such that /0/ ≤ /i0/ ≤ /n-1/ and
-- 
-- * /randomgen/, a random number generator.
-- 
-- The algorithm first calls the functions 'f_quantum' and 
-- 'g_quantum' to prepare a superposition of hypercubes 
-- containing at most two lattice points, whose difference 
-- is the shortest vector. It then measures the output to 
-- collapses the state to a 'TwoPoint'.
algorithm_R :: [[Integer]] -> Int -> Int -> Int -> Int -> StdGen -> Circ TwoPoint
algorithm_R bb_bar l m i0 p randomgen = do
  comment "ENTER: algorithm_R"
  let n = length bb_bar
      b = maximum (map maximum bb_bar)
      s = ceiling (logBase 2 (fromIntegral b)) + 5*n
      ws = take n $ sample_random randomgen 0 1

  -----------------------------------------------------------------
  -- Use functions 'f_quantum' and 'g_quantum' to partition 
  -- the space into hypercubes containing two points whose 
  -- difference is the shortest vector.
  ----------------------------------------------------------------- 
  t <- qinit False 
  a <- qinit $ replicate n (intm (4*n) 0)
  r <- qinit $ replicate n (intm s 0)
  (t,a) <- map_hadamard (t,a)

  ((t,a),r) <- classical_to_reversible (\(t,a) -> do
    result <- f_quantum bb_bar p m i0 (t,a)
    result <- g_quantum (toInteger l) ws r
    return result) ((t,a),r)

  -----------------------------------------------------------------
  -- Collapse the space onto one such cube to create a 'TwoPoint'.
  ----------------------------------------------------------------- 
  r_measured <- measure r 	
  cdiscard r_measured

  comment "EXIT: algorithm_R"
  return (t,a)


-- ==============================================================
-- * Algorithm 4: \"TPP\"
	
-- | Perform Regev's reduction of the /TPP/ to the /DCP/ and then
-- call 'dCP'. The arguments are: 
-- 
-- * /n/, an integer and
-- 
-- * /states/, a list of 'TwoPoint's.
--
-- The algorithm transforms the 'TwoPoint's in /states/ into 
-- 'CosetState's using the function 'h_quantum', then calls 
-- 'dCP' on this modified list to find the shortest vector.
tPP :: Int -> [TwoPoint] -> Circ [Integer]
tPP n states = do
  comment_with_label "ENTER: algorithm_TPP" states "states"
  let m = 2^(4*n)
      ms = foldl (+) 0 [m*(2*m)^k | k <- [0..(n-1)]]

  -----------------------------------------------------------------
  -- Use the function h to transform 'TPP' inputs (i.e. 'TwoPoint's) 
  -- into 'DCP' inputs (i.e. 'CosetState's). 
  ----------------------------------------------------------------- 
  states <- mapM (\(t,a) -> do
    a <- h_quantum a
    return (t,a)) states

  -----------------------------------------------------------------
  -- Call 'DCP' to find the difference between.
  ----------------------------------------------------------------- 
  d <- dCP n 0 0 states

  -----------------------------------------------------------------
  -- Convert the integer output of 'dcp' back to a vector.
  ----------------------------------------------------------------- 
  comment "EXIT: algorithm_TPP"
  return $ map (\x -> x-m) $ expand (d + ms) (2*m)


-- ==============================================================
-- * Algorithm 5: \"DCP\"

-- | Given integers /m/ and /n/ and a 'Psi_k' /(q,k)/
-- compute the last /n/ bits of the binary expansion
-- of /k/ on /m/ bits.
n_low_bits :: Int -> Int -> Psi_k -> [Bool]
n_low_bits m n p  = take n $ boollist_of_int_lh m (toInteger(snd p))

-- | Given integers /m/ and /n/ and a list /l/ of 'Psi_k's, group the 
-- elements  of /l/ into pairs /(psi_p, psi_q)/ where 
-- /p/ and /q/ share /n/ low bits. Return the list of all such 
-- pairs together with the list of unpaired elements of /l/.
pairing :: Int -> Int -> [Psi_k] -> ([(Psi_k, Psi_k)], [Psi_k])
pairing m n l = find_partners (\p -> n_low_bits m n p) l

-- | Perform Kuperberg's sieve. The arguments are:
--
-- * /n/, an integer,
--
-- * /m/, an integer and
--
-- * /l/, a list of 'Psi_k's.
--
-- The algorithm recursively combines and sieves the 
-- elements of /l/ until it reaches a list whose
-- elements have /m/[sup 2] trailing zeros.
-- At each step, the list of remaining 'Psi_k's are
-- paired and each pair 
-- ((/q/[sub 1], /k/[sub 1]), (/q/[sub 2], /k/[sub 2]))
-- is combined into a new 'Psi_k' /(q, k)/ with
-- /k/= /k/[sub 1] ± /k/[sub 2]. 
-- If /k/= /k/[sub 1] - /k/[sub 2], the 'Psi_k' is preserved,
-- otherwise it is discarded.
--
-- Remark:
--
-- * Uses 'dynamic_lift' to determine whether 
-- to keep a discard a 'Psi_k'.
sieving :: Int -> Int -> [Psi_k] -> Circ [Psi_k]
sieving n m l = do
  comment "ENTER: sieving"
  l <- loop_with_indexM m l (\j l -> do
    -- Pair the states sharing m+m*j low bits.
    comment "ENTER: Pairing"
    let mmj = m + m*j
        (pairs, unpaired) = pairing n mmj l 
    -- Discard the states that haven't been paired.
    qdiscard_psi_ks unpaired
    comment "EXIT: Pairing"
    -- Combine pairs (Psi_k, Psi_l) to get Psi_k±l.
    -- If the measurement outcome ('sign') is 0, then the 
    -- associated state is of the form Psi_k-l. 
    combined_states <- mapM (\((q,k),(q',l)) -> do 
      comment "ENTER: Combining"
      q <- qnot q `controlled` q'
      q <- measure q	
      sign <- dynamic_lift q
      comment "EXIT: Combining"
      return (sign, (q', (k-l)))) pairs
    -- Separate the states according to the value of 'sign'.
    -- Discard the states of the form Psi_k+l and 
    -- return the ones of the form Psi_k-l.
    let (plus, minus) = separate combined_states fst
    qdiscard_psi_ks $ map snd plus
    return $ map snd minus)
  comment "EXIT: sieving"
  return l

-- | Perform Kuperberg's algorithm solving the Dihedral
-- Coset problem. The arguments are: 
-- 
-- * /n/, an integer measuring the length of the output,
-- 
-- * /d/, an integer to hold the output initially set to 0,
-- 
-- * /s/, an integer counter initially set to 0 and
-- 
-- * /states/, a list of 'CosetState's.
--
-- The algorithm proceeds recursively. At each iteration it  
-- uses Kuperberg's sieve on the first /n/ elements of /states/ 
-- to compute the /s/-th bit of the output and updates /d/ with
-- the result. Then it increments /s/ and repeats until /states/ is 
-- exhausted. 
--
-- Remark: 
--
-- * The function 'dynamic_lift' used in this algorithm is presumably
-- very expensive in terms of resources. In this implementation
-- it is used profusely but there is room for optimization.
dCP :: Int -> Integer -> Int -> [CosetState] -> Circ Integer
dCP n d s states = if s == n then return d else do
  comment (printf "ENTER algorithm_DCP: n=%d d=%d s=%d" n d s)
  let nn = 2^n
      r = exp $ -( 2*pi*(fromIntegral d / fromIntegral(nn)) )
      m = ceiling $ sqrt $ fromIntegral $ n-s-1
      (l1, l2) = splitAt n states

  -----------------------------------------------------------------
  -- Transform the first n coset states  
  -- into states of the form Psi_k. 
  ----------------------------------------------------------------- 
  comment "ENTER: TO_Psi_k"
  l <- mapM (\(t,a) -> do
    a <- qft_int a
    ca <- measure a
    k <- mmap fromIntegral $ dynamic_lift ca
    t  <- named_rotation "R" (r*(fromIntegral k)) t
    return (t, k)) l1
  comment "EXIT: To_Psi_k"

  -----------------------------------------------------------------
  -- Sieve the Psi_k's to get Psi_2^{n-s-1}.
  -----------------------------------------------------------------
  l <- sieving n m l
  -----------------------------------------------------------------
  -- Extract the s-th bit of d by finding in l a state of the 
  -- form Psi_2^{n-s-1} and measuring it in the +/- basis. The 
  -- remaining states in l are discarded.
  -----------------------------------------------------------------
  let ((q,k),psis) = find l (\x -> ((snd x) == 2^(n-s-1))) "The sieving process failed to produce a state of the form 2^k." 
  --let ((q,k),psis) = ((head l),(tail l))
  q <- map_hadamard q
  q <- measure q
  q <- dynamic_lift q
  qdiscard_psi_ks psis
  let d_lsb = int_of_boollist_unsigned_bh [q]

  -----------------------------------------------------------------
  -- Update d_low and iterate on the remaining list.
  -----------------------------------------------------------------
  comment "EXIT: algorithm_DCP"
  dCP n (d + (2^s)*d_lsb) (s+1) l2
