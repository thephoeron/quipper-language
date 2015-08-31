-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | An implementation of the quantum algorithms, based on the works of Hallgren, to compute the class number of a real quadratic number field.

module Algorithms.CL.CL where

import Quipper

import QuipperLib.QFT
import QuipperLib.Arith
import QuipperLib.FPReal
import QuipperLib.Simulation

import Algorithms.CL.Auxiliary
import Algorithms.CL.Types
import Algorithms.CL.RegulatorClassical
import Algorithms.CL.RegulatorQuantum
import Algorithms.CL.SmithReduction

import Data.Ratio
import Data.Maybe
import Data.List
import System.Random

-- ======================================================================
-- * Stage 1 (quantum): Approximate regulator to low precision
-- ======================================================================

-- | Quantum part of the procedure to approximate the regulator /R/.
--
-- Follows the procedure described in [Jozsa 2003], Sec. 10. An adapted
-- version of the Hidden Subgroup Problem (HSP) Algorithm is used to
-- estimate the (irrational) period of the function /f/ [sub /N/]
-- ('fN', 'q_fN'); this is the function /h/ of [Jozsa 2003], Sec. 9,
-- discretized with precision /N/ = 2 [super −/n/], and so has weak
-- period /S/ = /NR/.  The precision /n/ is determined by 'n_of_bigD'.
--
-- Inputs: Δ; /i/, an assumed bound such that /S/ ≤ 2[sup /i/]; 
-- and a random “jitter” parameter.
approximate_regulator_circuit :: CLIntP -> Int -> CLIntP -> (Circ CInt)
approximate_regulator_circuit bigD i jitter = do
    let n = n_of_bigD bigD
        nn = 2^n
        s_bound = 2^i
    -- q is the register length, and Q = 2^q (qq in Haskell code) the number of states.
        q = 2 + 2 * i   -- So 2^q = 4 * (s_bound^2), the first power of 2 assumed to  
        qq = 2^q        -- be above 3 S^2.
        l = 4 + q + n   -- Chosen to give:
        ll = 2^l        -- L = 16 Q N.
        t = i + 2 * (ceiling $ logBase 2 $ sqrt $ fromIntegral bigD)
        j_p = intm (4+q) jitter

    -- Step 1 - apply Hadamard transform to register 1
    reg1 <- qinit $ qc_false $ qshape $ intm q 0
      -- Note: the [qc_false $ qshape] is currently redundant, since 0 is encoded as |00…00>.
      -- However, that is dependent on the specific representation of integers;
      -- using qc_false specifies the all-0 state independently of the
      -- representation of integers.
    reg1 <- mapUnary hadamard reg1

    -- Step 2 - Apply unitary transformation corresponding to f_N.  (This automatically initialises reg2.)
    (reg1,reg2) <- q_fN bigD n l reg1 j_p

    -- Step 3 - Discard contents of reg2. 
    reg2_c <- measure reg2
    cdiscard reg2_c

    -- Step 4 - apply QFT
    reg1 <- qft_int reg1

    -- Step 5 - measure register 1, and return the measurement.
    reg1_c <- measure reg1
    return reg1_c

-- | Attempt to approximate the regulator /R/, given an assumed 
-- bound /i/ such that /S/ ≤ 2[sup /i/], using the probabilistic 
-- quantum computation @approximate_regulator_circuit@ twice as
-- described in [Jozsa 2003], Sec. 10.
-- 
-- Check the result for success; if it fails, return 'Nothing'.
--
-- (The 'IO' monad is slight overkill here: it is just to make a
-- source of randomness available. A tighter approach could use e.g. a
-- monad transformer such as 'RandT', applied to the 'Circ' monad.)
try_approximate_regulator :: CLIntP -> Int -> IO (Maybe CLReal)
try_approximate_regulator bigD i = do
    let n = n_of_bigD bigD
        q = 2 + 2 * i   -- So 2^q = 4 * (s_bound^2), the first power of 2 assumed to  
        qq = 2^q        -- be above 3 S^2.

    c_jitter <- getStdRandom $ randomR (0, 16*qq - 1)
    c <- run_generic_io (undefined :: Double) $ approximate_regulator_circuit bigD i c_jitter
    d_jitter <- getStdRandom $ randomR (0, 16*qq - 1)
    d <- run_generic_io (undefined :: Double) $ approximate_regulator_circuit bigD i d_jitter

    -- Find the (possibly empty) list of m's that pass the verification
    -- criteria. The candidate m's are constructed from the convergents of c/d
    let candidate_ms = filter (verify_period_multiple bigD n) $
                       map (\c_n -> round $ c_n * (fromIntegral qq) / (fromIntegral c)) $
                       convergents $ continued_list (fromIntegral c) (fromIntegral d)

    return $ if (null candidate_ms)
             then Nothing
             else (Just (fprealx (-n) (head $ sort $ candidate_ms)))

-- | @'verify_period_multiple' Δ /n/ /m/@: 
-- check whether /m/ is within 1 of a multiple of the period /S/ of /f/[sub /N/].
--
-- Since for any ideal /I/, ρ(ρ(/I/)) is distance > ln 2 from /I/, it suffices 
-- to check whether the unit ideal is within 4 steps either way of /f/[sub /N/](m).
verify_period_multiple :: CLIntP -> Int -> CLInt -> Bool
verify_period_multiple bigD n m =
  let jj = fst $ fN m (2^n) 0 0 bigD
  in (unit_ideal bigD)
    `elem` ([jj] ++ (take 4 $ iterate rho jj) ++ (take 4 $ iterate rho_inv jj))

-- | Approximate the regulator for a given Δ (/bigD/).
--
-- Repeatedly run @'try_approximate_regulator'@ enough times, with increasing
-- /i/, that it eventually succeeds with high probability. 
approximate_regulator :: CLIntP -> IO CLReal
approximate_regulator bigD =
    -- Create a (infinite and lazy) list of attempts to approximate the
    -- regulator, assuming S ≤ 2^i for i = 1, 2, …
    -- (For each value of /i/, make (36 * i) attempts.)
    -- Run the attempts until one succeeds; return its answer.
    fmap (fromJust . fromJust) $ sequence_until isJust $ concat
      [ replicate (36*i) (try_approximate_regulator bigD i) | i <- [1..] ]

-- ======================================================================
-- * Stage 2 (classical): Compute the regulator more accurately. 
-- ======================================================================

-- | Improve the precision of the initial estimate of the regulator /R/, for 
-- a quadratic discriminant Δ.
--
-- The implementation is essentially based on the proof of Theorem 5 of 
-- [Jozsa 2003].
improve_regulator_accuracy :: CLReal -> Integer -> CLReal
improve_regulator_accuracy bigR bigD =
    fRefine dist idealNew
    where
        (dist, idealNew) = improve_regulator_accuracy' bigD
        improve_regulator_accuracy' :: Integer -> (CLReal, IdDist)
        improve_regulator_accuracy' bigd = refineR (head j') ideals

        -- -------------------------------------------------------------------------
        -- Step 3: So far we have computed ideals, I_i , I_i-1 , I_i-2 ,.., I_1.
        -- Now, for I_i perform dot (*) operation with  Ii-1,  Ii-2, .., I_1 while
        -- (I_i * I_k) < R is true.  If (I_i *I_k) > R, then discard I_k and
        -- continue with I_k-1.  Finish when I_1 is reached.
        -- At this point a reduced Ideal J* is produced to the left of R with
        -- R - delta(J*).  In parallel accumulate distances using fomula
        -- delta(I,rho(I)) = ln |gamma| for I = Z +gammaZ and Proposition 34
        -- of [Jozsa 2003].  In the end apply repeatedly rho**2 to J* while
        -- distance does not exeed R.
        -- ------------------------------------------------------------------------
        fRefine :: CLReal -> IdDist -> CLReal
        fRefine currDist reducedI =
            -- fRefine currDist reducedI = if (newDist < bigR)
            let
                newReducedI = rho_d $ rho_d reducedI
                newDist = delta newReducedI
            in    if (newDist < bigR)
                then
                    fRefine  newDist newReducedI
                else
                    currDist

        refineR :: IdDist -> [IdDist] -> (CLReal, IdDist)
        refineR currI (x:xs) =
            -- repeat applying an Ideal to the reference Ideal until
            -- the distance that is smaller than 'r' is found.
            if (null xs)
                then
                    case (distance > bigR) of
                        True -> (delta currI, currI)
                        False -> (distance, i')
                else
                    if (distance > bigR)
                    then
                        refineR currI xs
                    else
                        refineR i' xs
            where
                distance = delta i'
                i'' = currI `dot` x
                i' = while (not . is_reduced . fst) rho_d i''
        
        refineR _ [] = undefined -- keep the compiler happy                

        -- --------------------------------------------------------------------
        -- Step 2: Compute the closest ideal I to the left of R along the cycle
        -- of principal reduced ideals and its distance which is the closest
        -- to real value.
        -- At the end of this step an Ideal I_i and a list of ideals I_i-1,
        -- I_i-2,.., In1, will be constructed.
        -- --------------------------------------------------------------------
        -- The following function constructs a list of ideals I_i, I_i-1, I+i-2,..., I_1,
        -- where delta(I_n) < bigR.
        -- j' is an Ideal, I_i (or I_N of [Jozsa 2003], in first paragraph of p.24)
        -- 
        -- @ideals@ contains the list of ideals so far collected, with the
        -- the newest entry at the head.
        (j', ideals) =  splitAt 1 $ reverse $ refineR1 i0

        refineR1 :: IdDist -> [IdDist]
        refineR1 x
            -- each time multiplication is done, reduce the Ideal and compute delta as well
            -- rho function also computes the new accumulating distance each time
            | (delta x) < bigR    = x : refineR1 (reduceIdeal $ dot' x)
            | otherwise        = []
            where
                -- reduce the ideal
                reduceIdeal ::IdDist -> IdDist
                reduceIdeal i = while (not . is_reduced . fst) rho_d i

        -- ----------------------------------------------------------------
        -- Step 1: Compute the initial Ideal I0 and its distance Delta(I0).
        -- compute the initial Ideal
        -- ----------------------------------------------------------------
        i0 = rho_d $ rho_d $ (unit_ideal bigD, 0)

-- ======================================================================
-- * Stage 3 (classical): Find generators of the class group.
-- ======================================================================

-- | A set of ideal classes generating /CL/(/K/).
-- 
-- Implementation: assuming the Generalized Riemann Hypothesis, it is
-- enough to enumerate the non-principal prime ideals arising as
-- factors of (/p/), for primes /p/ ≤ 12(ln Δ)[super 2]. ([Haase and
-- Maier 2006], Prop. 4.4.)  For each /p/, there are at most two such
-- prime ideals, and they are easily described.
compute_generators :: CLIntP -> [IdealRed]
compute_generators bigD =
    map (reduce . ideal_from_generator) $
      concat [gens_from_prime p | p <- primes_to primes_bound, p >= 3]
    where
      primes_bound = (12*((floor $ log $ fromIntegral bigD)^2))
      d = d_of_bigD bigD
      omega = omega_of_bigD bigD
      omega_bar = conjugate omega

      -- the polynomial with roots omega, omega_bar
      f = if (bigD `mod` 4 == 1)
                   then (\x -> x^2 - x - ((bigD - 1) `div` 4)) 
                   else (\x -> x^2 - bigD)

      gens_from_prime 2 = case (d `mod` 8) of
        5 -> []                             
        1 -> [(2, omega), (2, omega_bar)]    
        3 -> [(2, AlgNum (-1) (1/2) bigD)]                   
        7 -> [(2, AlgNum (-1) (1/2) bigD)]                   
        _ -> [(2, AlgNum 0 (1/2) bigD)]
      gens_from_prime p = case (d `jacobi_symbol` p) of
        0 -> [(p, omega - c)]
        1 -> [(p, omega - c),(p, c - omega_bar)]
        _ -> []
        where
          c = fromIntegral $ head [ x | x <- [0..p-1], (f x) `mod` p == 0 ] 

      -- give the standard form of the ideal generated by (p,x),
      -- provided that x is of the form (b + √Δ)/2
      ideal_from_generator :: (CLIntP, AlgNum) -> Ideal
      ideal_from_generator (p, w) =
        let b = (2*w - (AlgNum 0 1 bigD))
        in assert (snd_AlgNum b == 0 && is_int (fst_AlgNum b)) 
          ("compute_generators: w = " ++ show w ++ " is not of expected form")
          (Ideal bigD 1 1 (fromIntegral p) (truncate (fst_AlgNum b)))

-- ======================================================================
-- * Stage 4 (quantum): Find relations between generators.
--
-- $ Notation is as in [Hallgren 2006, Section 5].  Note: Some
-- components are currently missing here, and are marked
-- \"incomplete\" in the code below.

-- ======================================================================

-- | Compute the generators of /CL/(/K/), function /hI/.
hI :: IdDist -> CLInt -> CLInt -> CLInt -> CLIntP -> CLIntP -> (IdDist, CLInt)
hI ideal_I a b j n l =
        (ideal_K'', floor (fromIntegral n * delta ideal_K''))
    where
        bigD = bigD_of_Ideal (fst ideal_I)
        ideal_J = ideal_I                                            
        ideal_K = (unit_ideal bigD, 0)  
        i       = a                                                  
        (i', ideal_J', ideal_K') =
            bounded_while condition bound body (i, ideal_J, ideal_K)  
            where
                bound        = ceiling $ logBase 2 (fromIntegral a)
                
                body (i,j,k) = ( 
                     floor ((fromIntegral i) / 2),                    
                     j `star` j,                                     
                     if (i `mod` 2 /= 0) then k `star` j else k)     
                
                condition (i,j,k) = (i /= 0)                         

        ideal_J'' = fst $ fN_d b j n l (bigD_of_Ideal $ fst ideal_I)        
        ideal_K'' = ideal_K' `star` ideal_J''                        

-- | Compute the ideals from the generators (ĝ function).
compute_ghat :: (Integral int) => [IdDist] -> [int] -> IdDist
compute_ghat gs is =
    foldl1 (\g_i g_j -> g_i `star` g_j) $
        map (\(ik, gk) -> gk `power` ik) $ zip is gs

    where
        power :: (Integral int) => IdDist -> int -> IdDist
        power gk 0 = let (Ideal bigD m l a b, _) = gk in (unit_ideal bigD, 0)
        power gk 1 = gk
        power gk n = gk `star` (power gk (n-1))

-- | Compute /i/\//N/. Incomplete.
compute_i_N_at :: QDInt -> QDInt -> Circ()
compute_i_N_at reg_I reg_out = 
    error "incomplete"


-- | Compute register sizes for @structure_circuit@, given
--  Δ and a precise estimate of /R/. Return a 7-tuple
--   (/q/,1,2,3,4,5,6) where /q/ is the size of the first
--   /k/ registers, and 1…6 are the sizes of registers /k/+1…/k/+6.
register_sizes :: CLIntP -> CLReal -> (Int,Int,Int,Int,Int,Int,Int)
register_sizes bigD r =
    (q, r1, r2, r3, r4, r5, r6)
    where
        q  =     clog2i bigD
        r1 = 2 * clog2r sqrt_bigD
        r2 =     clog2i round_nr
        r3 = 2 * clog2r sqrt_bigD + clog2i round_nr
        r4 =     clog2i (m * round_nr)
        r5 =     clog2i round_nr
        r6 = 2 * clog2r sqrt_bigD + clog2i round_nr

        -- Algorithm constants
        sqrt_bigD    = sqrt $ fromIntegral bigD
        round_nr     = round nr

        m            = ceiling $ 2*r+1
        b            = ceiling $ 2 * sqrt_bigD
        (p',q')      = find_pq_satisfying_condition br m
        n            = q' * b
        l            = 16 * q * n
        nr           = fromIntegral n * r
        br           = fromIntegral b * r

        -- Find a pair (p,q) from the continued fraction expansion of BR such
        -- that |BR - p\/q| <= 1/(4qM)
        find_pq_satisfying_condition :: (Integral int, Show int) => CLReal -> int -> (int, int)
        find_pq_satisfying_condition br m =
            if   (isJust found)
            then (num, denom)
            else error $
                    "Could not find p/q such that |BR - p/q| <= 1/(4qM) for:\n" ++
                    "br = " ++ (show br) ++ "\n" ++
                    "m  = " ++ (show m)  ++ "\n" ++
                    "convergents = " ++ (show convs)
            where
                num   = fromIntegral $ numerator   $ fromJust found
                denom = fromIntegral $ denominator $ fromJust found

                found = find satisfies convs

                convs = convergents $
                            continued_list
                                (numerator   $ toRational $ br)
                                (denominator $ toRational $ br)

                satisfies :: Rational -> Bool
                satisfies p_over_q =
                    abs (br - fromRational p_over_q) <= 1/(4*q*m')
                    where q  = fromIntegral $ denominator p_over_q
                          m' = fromIntegral m

        -- Helper function - ceiling(log_2 val)
        clog2r :: (RealFrac a, Floating a, Integral int) => a -> int
        clog2r val    = ceiling $ logBase 2 val

        clog2i :: (Integral int) => int -> Int
        clog2i val    = clog2r $ fromIntegral val


-- | The quantum circuit used in computing the structure of /CL/(/K/),
-- given Δ, a precise estimate of /R/, and a generating set for /CL/(/K/).
structure_circuit :: CLIntP -> CLReal -> [IdealRed] -> (Circ [CInt])
structure_circuit bigD r gs = do
    -- Apply H to first k registers of size 'q' each
    reg_ks <- qinit [ intm q 0 | x <- gs ]
    reg_ks <- mapUnary hadamard reg_ks

    -- Initialize the rest of the registers in state zero
    -- note: fIN and fJN is the same thing.
    reg_I   <- qinit (intm reg_I_size   0)      -- register 1
    reg_i   <- qinit (intm reg_i_size   0)      -- register 2
    reg_fIN <- qinit (intm reg_fIN_size 0)      -- register 3
    reg_i_N <- qinit (intm reg_i_N_size 0)      -- register 4

    -- Apply U_g_hat
--  Incomplete: (q_compute_ghat gs) reg_ks reg_I

    -- Superposition of distances
    reg_i <- mapUnary hadamard reg_i

    -- Evaluate f_I,N
--  Imcomplete: q_fJN reg_i reg_I reg_fIN

    -- Compute i/N
    compute_i_N_at reg_I reg_i_N

    -- Erase reg_i
--  Incomplete: erase_at fJN reg_i reg_I reg_fIN

    -- Uncompute i/N
--  Incomplete: uncompute_i_N_at reg_I reg_i_N

    -- Uncompute I
--  Incomplete: q_compute_ghat gs reg_ks reg_I

    -- Measure and discard result (used to project the system)
    result_discard <- measure reg_fIN

    -- Apply QFT
    -- FIX: Looking at the definition:
    --    Fq x Fq ... (|l1>...|lk>) = Fq|l1> x ... x Fq|lk>
    -- it seems the QFT can can be applied on the per-register basis. Check.
    -- FIX: Check if the endianness is correct
    reg_ks <- sequence $ map qft_int reg_ks

    -- Measure the system
    reg_ks_measured <- mapM measure reg_ks
    return (reg_ks_measured)

    where
        (q,
         reg_I_size,   reg_i_size,
         reg_fIN_size, reg_i_N_size,
         _,            _)              = register_sizes bigD r

-- | Compute the relations between a given set of reduced generators.
compute_relations :: CLIntP -> CLReal -> [IdealRed] -> IO [CLInt]
compute_relations bigD r generators = do
    result <- run_generic_io (undefined :: Double) $ structure_circuit bigD r generators
    return (result)

-- ======================================================================
-- * Section 5 (classical): compute class number.
-- ======================================================================

-- | The full implementation of Hallgren’s algorithm.
-- 
-- @class_number dd t@: computes the class number |/CL/(/K/)| for Δ = /dd/,
-- with success probability at least (1 - 1\/2[sup /t/]).
class_number :: CLIntP -> Int -> IO(CLInt)
class_number bigD t = do
    -- Stage 1: Approximate regulator to low precision
    approximate_regulator <- approximate_regulator bigD

    -- Stage 2 & 3: Classical algorithms
    let regulator        =  improve_regulator_accuracy approximate_regulator bigD
        generators       =  compute_generators bigD

        k                = length generators
        q                = ceiling $ logBase 2 $ fromIntegral bigD
        bigT             = t + k * (ceiling $ logBase 10 $ fromIntegral q)

    -- Stage 4: Use HSP to compute set of relations
    relations <- mapM (\_ -> compute_relations bigD regulator generators) [ 1 .. bigT ]

    -- Stage 5: Make canonical set and derive CL(K) from structure
    return $ group_order_from_matrix $ matrix_from_list relations
