-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module implements the classical operations on ideals used in Hallgren’s
-- algorithm (including also classical versions of the quantum operations required).
 
module Algorithms.CL.RegulatorClassical where

import Data.Maybe

import QuipperLib.Arith
import QuipperLib.FPReal

import Algorithms.CL.Auxiliary
import Algorithms.CL.Types

-- ======================================================================
-- * Basic operations on ideals

-- | @'unit_ideal' /bigD/ /l/@: the unit ideal /O/, for Δ = /bigD/, with the ideal’s coefficients given as /l/-bit integers.  
-- ([Jozsa 2003], Prop. 14.)
unit_ideal :: CLIntP -> Ideal
unit_ideal = forget_reduced . unit_idealRed 

-- | Like 'unit_ideal', but considered as a reduced ideal.
unit_idealRed :: CLIntP -> IdealRed
unit_idealRed bigD = assert (is_valid_bigD bigD) ("unit_idealRed: " ++ show bigD ++ " not valid discriminant") 
                  $ IdealRed bigD 1 (tau bigD (fromIntegral bigD) 1)

-- | The integer constant /c/ of an ideal.
--   ([Jozsa 2003], page 14 bottom: \"Since 4/a/ divides /b/[sup 2]-/D/
--   (cf. proposition 16) we introduce the integer /c/ = |/D/ − /b/[sup 2]|\/(4/a/)\")
c_of_ideal :: Ideal -> CLInt
c_of_ideal i@(Ideal bigD m l a b) =
    if (num `mod` denom == 0) then num `div` denom
                              else error error_string
    where num   = abs ((fromIntegral bigD) - b*b)
          denom = 4*a
          error_string = "rho of ideal [" ++ show i ++ "] produces non-integer c"

-- | γ(/I/) = (/b/+√Δ)\/(2/a/) for a given ideal /I/.
--   ([Jozsa 2003], Sec. 6.2.)
gamma_of_ideal :: Ideal -> AlgNum
gamma_of_ideal (Ideal bigD m l a b) = AlgNum a' b' bigD
    where
        a' = (fromIntegral b / fromIntegral (2*a)) :: CLRational
        b' = (fromIntegral 1 / fromIntegral (2*a)) :: CLRational
  -- Recall: @'AlgNum' u v bigD@ represents (u + v * √bigD).

-- | The reduction function ρ on ideals.
-- ([Jozsa 2003], Sec. 6.2.)
rho :: Ideal -> Ideal
rho ii@(Ideal bigD m l a b) = (Ideal bigD m'' l'' a' b')
    where
        -- With little algebra, one can derive these:
        m'   = m * a
        l'   = l * a'
        m''  = m' `div` (gcd m' l')
        l''  = l' `div` (gcd m' l')
        -- From  [Jozsa 2003], p.15, equation (10)
        a'   = c_of_ideal ii
        b'   = tau bigD (-b) a'

-- | The ρ[sup -1] function on ideals.  Inverse to 'rho'.
-- ([Jozsa 2003], Sec. 6.4.)
rho_inv :: Ideal -> Ideal
rho_inv (Ideal bigD m l a b) = (Ideal bigD m'' l'' a'' b'')
    where
        -- Create m and l
        m'    = m * a
        l'    = l * a''
        -- Reduce them to have no common denominator
        m''   = m' `div` (gcd m' l')
        l''   = l' `div` (gcd m' l')
        -- Calculate b* (b' below)
        b'    = tau bigD (-b) a
        -- Calculate new a and b
        a''   = ((fromIntegral bigD) - b'*b') `divchk` (4*a)
        b''   = tau bigD b' a''

-- | The ρ operation on reduced ideals.
rho_red :: IdealRed -> IdealRed
rho_red = to_reduced . rho . forget_reduced

-- | The ρ[sup –1] operation on reduced ideals.
rho_inv_red :: IdealRed -> IdealRed
rho_inv_red = to_reduced . rho_inv . forget_reduced

-- | The ρ operation on ideals-with-distance.
rho_d :: IdDist -> IdDist
rho_d (ii, del) = (rho ii, del + del_change)
  where
    gamma = gamma_of_ideal ii
    gamma_bar_by_gamma = (floating_of_AlgNum $ conjugate gamma) / (floating_of_AlgNum gamma)
    del_change = (log $ abs gamma_bar_by_gamma) / 2

-- | The ρ[sup –1] operation on ideals-with-distance.
rho_inv_d :: IdDist -> IdDist
rho_inv_d (ii, del) = (ii', del - del_change)
  where
    ii' = rho_inv ii
    gamma = gamma_of_ideal ii'
    gamma_bar_by_gamma = (floating_of_AlgNum $ conjugate gamma) / (floating_of_AlgNum gamma)
    del_change = (log $ abs gamma_bar_by_gamma) / 2

-- | The ρ operation on ideals-with-generator (i.e. pairs of an ideal /I/ and an 'AlgNum' /x/ such that /I/ is the principal ideal (/x/)).
rho_num :: (Ideal,AlgNum) -> (Ideal,AlgNum)
rho_num (ii, gen) = (rho ii, gen / (gamma_of_ideal ii))

-- | Apply ρ to an reduced-ideals-with-generator
rho_red_num :: (IdealRed,AlgNum) -> (IdealRed,AlgNum)
rho_red_num (ii, gen) = (rho_red ii, gen / (gamma_of_ideal $ forget_reduced ii))

-- ======================================================================
-- * Ideal reductions (bounded)

-- | Reduce an ideal, by repeatedly applying ρ.
reduce :: Ideal -> IdealRed
reduce ii = to_reduced $ while (not . is_reduced) rho ii

-- | Reduce an ideal within a bounded loop. Applies the ρ function
--   until the ideal is reduced. Used in 'star' and 'fJN' algorithms.
bounded_reduce :: IdDist -> IdDist
bounded_reduce k@(ideal@(Ideal bigD m l a b),dist) = 
    fst $ bounded_while condition bound func (k,0)
    where
        -- NOTE: some uncertainty regarding loop bound.
        bound             = ceiling $ bound_log + 1
        bound_log         = (logBase 2 ((fromIntegral bound_a) 
                            / (sqrt $ fromIntegral $ bigD_of_Ideal $ ideal)))
        bound_a           = 2 ^ (fromJust (intm_length $ a))

        condition (k,itr) = not $ is_reduced $ fst k
        func      (k,itr) = ((rho_d k),(itr+1))

-- | Apply a function (like ρ,ρ[sup -1],ρ[sup 2]) to an ideal, bounded
--   by 3*ln(Δ)\/2*ln(2). Execute while satisfies condition function.
bounded_step :: (IdDist -> Bool) -> (IdDist -> IdDist) -> IdDist -> IdDist
bounded_step condition step_function ideal =
    -- Execute a bounded while loop
    bounded_while condition bound step_function ideal
    where
        bound = ceiling $ (3 * (log $ fromIntegral $ bigD_of_Ideal $ fst ideal)) / (2 * log 2)

-- | Like 'bounded_step', but the condition is checked against delta of the
--   current ideal.
bounded_step_delta :: (CLReal -> Bool) -> (IdDist -> IdDist) -> IdDist -> IdDist
bounded_step_delta condition step_function ideal =
    bounded_step new_condition step_function ideal
    where new_condition = (\k -> condition (delta k))

-- ======================================================================
-- * Products of ideals

-- | The ordinary (not necessarily reduced) product of two reduced fractional ideals.
-- 
-- /I/⋅/J/ of [Jozsa 2003], Sec 7.1, following the description
-- given in Prop. 34.

-- NOTE: assumes I, J reduced.  Type should reflect this!
dot :: IdDist -> IdDist -> IdDist
dot i1@(Ideal bigD1 m1 l1 a1 b1, delta1) i2@(Ideal bigD2 m2 l2 a2 b2, delta2) =
    assert_reduced (fst i1) $
        assert_reduced (fst i2) $
            (Ideal bigD1 m l a3 b3, del)
    where
        sqrtd :: CLReal
        sqrtd = sqrt (fromIntegral bigD1)
        (k', u', v') = extended_euclid a1 a2
        (k,  x,  w ) = extended_euclid k' ((b1 + b2) `divchk` 2)
        a3 = (a1 * a2) `divchk` (k * k)
        t1 = x * u' * a1 * b2
        t2 = x * v' * a2 * b1
        t3 = w*(b1 * b2 + (fromIntegral bigD1)) `divchk` 2
        t  = (t1 + t2 + t3) `divchk` k
        b3 = tau bigD1 t a3
        m = k
        l = a3
        del = ((delta i1) + (delta i2))

-- | The dot-square /I/⋅/I/ of an ideal-with-distance /I/.
dot' :: IdDist -> IdDist
dot' i1@(Ideal bigD1 m1 l1 a1 b1, delta1) =
    assert_reduced (fst i1) $
            (Ideal bigD1 m l a3 b3, del)
    where
        sqrtd :: CLReal
        sqrtd = sqrt (fromIntegral bigD1)
        (k, u, w) = extended_euclid (abs a1) (abs b1)
        a3 = (a1 * a1) `divchk` (k * k)
        t1 = u * a1 * b1
        t3 = w*(b1 * b1 + (fromIntegral bigD1)) `divchk` 2
        t  = (t1 + t3) `divchk` k
        b3 = tau bigD1 t a3
        m = k
        -- l = a3
        l = 1
        del = ((delta i1) + (delta i1))

-- | The star-product of two ideals-with-distance.
--
-- This is /I/*/J/ of [Jozsa 2003], Sec. 7.1, defined as the first reduced
-- ideal-with-distance following /I/⋅/J/.

-- NOTE: assumes I, J reduced.  Type should reflect this!
star :: IdDist -> IdDist -> IdDist
star i j =
    if (delta k1 <= delta i_dot_j)
        then       bounded_step_delta (<= delta i_dot_j) rho_d k1
        else rho_d $ bounded_step_delta (>= delta i_dot_j) rho_inv_d k1
    where
        i_dot_j = i `dot` j
        -- FIX: Over bound (infinite loop) in reducing the following:
        --      <m:1 l:3 a:3 b:2 bigD:28 del:1.1>*<m:1 l:3 a:3 b:4 bigD:28 del:1.6>
        k1      = bounded_reduce i_dot_j

-- ======================================================================
-- * The function f[sub /N/], and variants

-- | Compute the expression i\/N + j\/L.
compute_injl :: (Integral int) => CLInt -> int -> CLInt -> int -> CLReal
compute_injl i nn j ll =
    (fromIntegral i)/(fromIntegral nn) + (fromIntegral j)/(fromIntegral ll)

-- |  @'fN' /i/ /j/ /n/ /l/ Δ@: find the minimal ideal-with-distance (/J/,δ[sub /J/]) such that δ[sub /J/] > /x/, where /x/ = /i/\//N/ + /j/\//L/, where /N/ = 2[sup /n/], /L/ = 2[sup /l/]. Return (/i/,/J/,δ[sub /J/]–/x/).  Work under the assumption that /R/ < 2[sup /s/].
--
-- This is the function /h/ of [Jozsa 2003, Section 9], discretized with precision 1\//N/ = 2[sup −/n/],
-- and perturbed by the jitter parameter /j/\//L/.
fN :: (Integral int) => CLInt -> CLInt -> int -> int -> CLIntP -> (Ideal, CLInt)
fN i j nn ll bigD =
  let ((ideal_J, _), diff) = fN_d i j nn ll bigD
  in (ideal_J, diff)

-- | Like 'fN', but returning an ideal-with-distance not just an ideal.
fN_d :: (Integral int) => CLInt -> CLInt -> int -> int -> CLIntP -> (IdDist, CLInt)
fN_d i j nn ll bigD =
    (j_star_19, floor $ (fromIntegral nn) * (toRational $ injl - (snd j_star_19)))
    where
        -- Expression "i/N + j/L" used repeatedly
        injl     = compute_injl i nn j ll

        -- Generate J1
        j1       = rho_d $ rho_d $ (unit_ideal bigD, 0)

        -- Generate Jk's (make an infinite list and take only what is needed)
        jks      = takeWhile (\jk -> (delta jk) <= injl) $
                        bounded_iterate bound_jks
                            (\jk -> jk `star` jk) j1
                   where
                       -- Bound for jk generation
                       max_i     = 2^(fromJust (intm_length $ i))
                       bound_jks = ceiling $
                                    (log $ fromIntegral max_i) /
                                        ((fromIntegral nn) * (delta j1))

        -- Apply all Jk's to J* using '*' in reverse (remember that the last
        -- element is J* itself)
        j_star_14   = foldr1 applyJkIfConditionHolds jks

        -- Apply Jk to J* if a condition holds.
        applyJkIfConditionHolds :: IdDist -> IdDist -> IdDist
        applyJkIfConditionHolds jk jstar =
            if (delta (jstar `star` jk) <= injl) then jstar `star` jk else jstar

        -- Go forward one step at a time as much as needed
        j_star_17   = bounded_step_delta (< injl) (rho_d.rho_d) j_star_14

        -- Go back one step if needed
        j_star_19   = if (delta (rho_inv_d j_star_17) >= injl)
                      then rho_inv_d j_star_17
                      else j_star_17

-- | Analogue of 'fN', working within the cycle determined by a given ideal /J/.
--   ([Hallgren 2006], Section 5.)
fJN :: IdDist -> CLInt -> CLInt -> CLInt -> CLInt -> CLIntP -> (Ideal, CLInt)
fJN ideal_J i j nn ll bigD =
  let ((ideal_J', _), diff) = fJN_d ideal_J i j nn ll bigD
  in (ideal_J', diff)

-- | Like 'fJN', but returning an ideal-with-distance not just an ideal.
fJN_d :: IdDist -> CLInt -> CLInt -> CLInt -> CLInt -> CLIntP -> (IdDist, CLInt)
fJN_d ideal_J i j nn ll bigD =
    (ideal_KFinal, floor $ (fromIntegral nn) * (injl - (delta ideal_KFinal)))
    where
        -- Expression "i/N + j/L"
        injl      = compute_injl i nn j ll

        -- Generate I and K
        ideal_I = fst (fN_d i j nn ll bigD)
        ideal_K = bounded_reduce (ideal_I `dot` ideal_J)

        -- Step forward/backward as much as needed
        ideal_KFinal =
            if (delta ideal_K <= injl)
            then        bounded_step_delta (<  injl) (rho_d)    ideal_K
            else rho_d $ bounded_step_delta (>= injl) (rho_inv_d) ideal_K

-- ======================================================================
-- * Classical period-finding

-- $ Functions for classically finding the regulator and fundamental unit of a field using the period of /f_N/.

-- ======================================================================
-- ** Auxiliary functions

-- | Find the order of an endofunction on an argument.  That is, @'order' /f/ /x/@ returns the first /n/ > 0 such that /f/[sup /n/](/x/) = /x/. 
--
--  Method: simple brute-force search/comparison.
order :: (Eq a) => (a -> a) -> a -> Int
order = order_with_projection id

-- | Given a function /p/, an endofunction /f/, and an argument /x/, returns the first /n/ > 0 such that /p/(/f/[sup /n/](/x/)) = /p/(/x/).  
--
-- Method: simple brute-force search/comparison.
order_with_projection :: (Eq b) => (a -> b) -> (a -> a) -> a -> Int
order_with_projection p f x = 1 + (length $ takeWhile (\y -> p y /= p x) (tail $ iterate f x))

-- | Given a function /p/, an endofunction /f/, and an argument /x/, return /f/[sup /n/](/x/), for the first /n/ > 0 such that /p/(/f/[sup /n/](/x/)) = /p/(/x/).  
--
-- Method: simple brute-force search/comparison.
first_return_with_projection :: (Eq b) => (a -> b) -> (a -> a) -> a -> a
first_return_with_projection p f x = head $ dropWhile (\y -> p y /= p x) $ tail $ iterate f x

-- | Given a bound /b/, a function /p/, an endofunction /f/, and an argument /x/, return /f/[sup /n/](/x/), for the first /n/ > 0 such that /p/(/f/[sup /n/](/x/)) = /p/(/x/), if there exists such an /n/ ≤ /b/.
--
-- Method: simple brute-force search/comparison.
first_return_with_proj_bdd :: (Eq b) => Int -> (a -> b) -> (a -> a) -> a -> Maybe a
first_return_with_proj_bdd b p f x = listToMaybe $ dropWhile (\y -> p y /= p x) $ take b $ tail $ iterate f x

-- | Find the period of a function on integers, assuming that it is periodic and injective on its period.  That is, @'period' /f/@ returns the first /n/ > 0 such that /f/(/n/) = /f/(0).  Method: simple brute-force search/comparison.
period :: (Eq a, Integral int) => (int -> a) -> int
period f = minimum [ n | n <- [1..], f n == f 0 ]
 
-- ======================================================================
-- ** Haskell native arithmetic

-- $ The functions of this section use Haskell’s native integer and floating computation.

-- | Find the regulator /R/ = log ε[sub 0] of a field, given the discriminant Δ, 
-- by finding (classically) the order of ρ.  
--
-- Uses 'IdDist' and 'rho_d'.
regulator :: CLIntP -> FPReal
regulator bigD = snd $ head $ dropWhile (\(ii,_) -> ii /= calO) $ tail $ iterate rho_d $ (calO,0)
  where calO = unit_ideal bigD

-- | Find the fundamental unit ε[sub 0] of a field, given the discriminant Δ, 
-- by finding (classically) the order of ρ.
--
-- Uses '(Ideal,Number)' and 'rho_num'.
fundamental_unit :: CLIntP -> AlgNum
fundamental_unit bigD = maximum [eps, -eps, 1/eps, -1/eps]
  where eps = snd $ first_return_with_projection fst rho_num (calO,1)
        calO = unit_ideal bigD

-- | Find the fundamental solution of Pell’s equation, given /d/.
--
-- Solutions of Pell’s equations are integer pairs (/x/,/y/) such that
-- /x/,/y/ > 0, and (/x/ + /y/√d)(/x/ – /y/√d) = 1.
--
-- In this situation, (/x/ + /y/√d) is a unit of the algebraic integers 
-- of /K/, and is >1, so we simply search the powers of ε[sub 0] for a
-- unit of the desired form.
fundamental_solution :: CLIntP -> (Integer,Integer)
fundamental_solution d = head pell_solutions
  where bigD = bigD_of_d d
        eps0 = fundamental_unit bigD
        pell_solutions = 
          [ (round x, round y) | n <- [1..],
                                 let eps@(AlgNum a b _) = eps0^n,
                                 a >= 0, b >= 0,
                                 let x = a,
                                 let y = if bigD == d then b else 2*b,
                                 is_int x, is_int y,
                                 eps * (conjugate eps) == 1]

-- ======================================================================
-- ** Fixed-precision arithmetic

-- $ The functions of this section perform period-finding using fixed-precision arithmetic.
-- This should parallel closely (though at present not exactly, due to the implementations 
-- of floating-point operations) the quantum circuit implementations, and hence allows
-- testing of whether the chosen precisions are accurate.

-- | Find the regulator /R/ = log ε[sub 0] of a field, given the discriminant Δ, 
-- by finding (classically) the order of ρ
-- using fixed-precision arithmetic: 'fix_sizes_Ideal' for 'Ideal's,
-- and given an assumed bound /b/ on log[sub 2] /R/.
--
-- Uses 'IdDist' and 'rho_d'.
regulator_fixed_prec :: Int -> CLIntP -> Maybe FPReal
regulator_fixed_prec b bigD = fmap snd (first_return_with_proj_bdd b' fst rho_d (calO,zero))
  where calO = fix_sizes_Ideal $ unit_ideal bigD
        n = n_of_bigD bigD
  -- S = 2RN, so this /i/ gives an assumed bound on log_2 S:  
        i = 1 + b + n
  -- Following precisions are as used in 'approximate_regulator_circuit', 'q_fN':
        q = 2 + 2 * i 
        l = 4 + q + n
        p = precision_for_fN bigD n l
        zero = fprealx (-p) (intm (q - n + p) 0)
  -- δ(I, ρ^2 (I)) ≥ √2 for any I, so the order of ρ is at most 2R / (√2 / 2):
        b' = ceiling $ 2 * sqrt(2) * (fromIntegral 2^b)


{-
Waiting for 'AlgNum' to be rebased using 'IntM' instead of 'Integer'.

-- | Find the fundamental unit ε[sub 0] of a field, given the discriminant Δ, 
-- by finding (classically) the order of ρ,
-- using fixed-precision arithmetic: 'fix_sizes_Ideal' for 'Ideal's,
-- and a given /l/ for the 'AlgNum's generating them.
--
-- Uses '(Ideal,Number)' and 'rho_num'.
fundamental_unit_with_fixed :: Int -> CLIntP -> AlgNum
fundamental_unit_with_fixed l bigD = maximum [eps, -eps, 1/eps, -1/eps]
  where eps = snd $ head $ dropWhile (\(ii,_) -> ii /= calO) $ tail $ iterate rho_num $ (calO,one)
        calO = fix_sizes_Ideal $ unit_ideal bigD
        one = intm_with_length (Just l) 1
-}
