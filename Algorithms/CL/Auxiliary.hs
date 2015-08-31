-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-} 

-- | This module defines general-purpose functions not specific to the Class Number algorithm, but required by it.

module Algorithms.CL.Auxiliary where

import Quipper
import QuipperLib.Arith hiding (q_ext_euclid, q_add, q_mult, q_div_exact,
                               q_add_in_place, q_add_param_in_place, q_div,
                               q_mult_param, q_mod_unsigned, q_sub_in_place,
                               q_increment)
import qualified QuipperLib.Arith as Arith
import QuipperLib.FPReal

-- Needed to define boxed arithmetic functions:
import Quipper.Internal

import Data.Maybe
import Control.Monad

-- ======================================================================
-- * Classical functions

-- ======================================================================
-- ** Control

-- | Assert that a condition is true, otherwise throwing an error with a given 
--   error message, in a functional setting.
assert :: Bool -> String -> a -> a
assert condition error_message x = if condition then x else error error_message

-- | Assert a condition, imperatively in a monad.
assertM :: (Monad m) => Bool -> String -> m ()
assertM b errorstring = if b then return () else error errorstring

-- | Given a list of monadic actions and a predicate on their results,
-- do the actions in sequence until one produces a result satisfying
-- the predicate; return this result.
sequence_until :: (Monad m) => (a -> Bool) -> [m a] -> m (Maybe a)
sequence_until _ [] = return Nothing
sequence_until p (m0:ms) = do
  a0 <- m0
  if p a0 then return (Just a0) else sequence_until p ms

-- | Test whether elements of a list are all equal  
all_eq :: (Eq a) => [a] -> Bool
all_eq [] = True
all_eq [a] = True
all_eq (a:b:rest) = (a == b) && all_eq (b:rest)

-- | Apply a function to data while condition holds true. For example:
--
-- > while (not . isReduced . fst) rho ideal
--
-- will apply the function 'rho' to an ideal-with-distance while it is not yet
-- reduced (until it is reduced).
while :: (a -> Bool) -> (a -> a) -> a -> a
while cond func x = if (cond x) then while cond func (func x) else x

-- | Like 'while', but with a known bound on number of iterations. This
--   construct can be converted to a quantum circuit, while a general unbounded
--   'while' cannot be lifted.
bounded_while :: (Integral int) => (a -> Bool) -> int -> (a -> a) -> a -> a
bounded_while cond bound func x
    | bound <  0                   = error "bounded_while: negative bound"
    | bound == 0 && (not $ cond x) = x
    | bound == 0                   = error "bounded_while: last iteration doesn't satisfy condition"
    | otherwise  =
                   bounded_while cond (bound-1) func x'
                   where x' = if (cond x) then func x else x

-- | A bounded version of Haskell 'iterate' function that produces an infinite
--   list. This function produces a finite bounded list.
bounded_iterate :: (Integral int) => int -> (a -> a) -> a -> [a]
bounded_iterate bound func x
    | bound <  0 = error "negative bound in bounded_iterate"
    | bound == 0 = [x]
    | otherwise  =
                   x : bounded_iterate (bound-1) (func) (func x)

-- ===========================================
-- ** Mathematical functions

-- | Generate primes using the Sieve of Eratosthenes. Straightforward
--   implementation - when a prime is found, filter all of its multiples
--   out of the already filtered list. This implementation may eventually blow
--   out of stack, but it should grow with the number of primes, which seems
--   to be O(log log n).
primes :: (Integral a) => [a]
primes  = primesn (2 : [ k*2+1 | k <- [1..] ])
    where primesn (n:xs) =
                n : (primesn (filter (\k -> k `mod` n /= 0) xs))
          primesn [] = undefined -- keep the compiler happy

-- | Generate primes up to a given number. See implementation of 'primes' for
--   details.
primes_to :: (Integral a) => a -> [a]
primes_to k =  takeWhile (<= k) primes

-- | Check if a number is square-free (by brute force).
is_square_free :: (Integral a) => a -> Bool
is_square_free n = 
    (n /= 0) && 
    (not $ any (\p -> (p*p) `divides` n) $ takeWhile (\x -> x^2 <= (abs n)) [2..])

-- | Compute the Jacobi symbol. The definition and algorithm description is
--   taken from <http://en.wikipedia.org/wiki/Jacobi_symbol>.
jacobi_symbol :: (Integral a, Num b) => a -> a -> b
jacobi_symbol a p =
        jacobi_symbol' a p
    where
        -- The actual implementation of the algorithm. Splitted away to allow
        -- logging.
        jacobi_symbol' a p
            | a == 0        = 0
            | a == 1        = 1                                                       -- Rule 4
            | a == 2        = if (p `mod` 8 == 1 || p `mod` 8 == 7) then 1 else -1    -- Rule 8
            | a >= p        = jacobi_symbol (a `mod` p) p                             -- Rule 2
            | 2 `divides` a = (jacobi_symbol (a `div` 2) p) * (jacobi_symbol 2 p)     -- Rule 4
            | otherwise     = (if p `mod` 4 == 3 && a `mod` 4 == 3 then -1 else 1)    -- Rule 6
                              * (jacobi_symbol p a)

-- | @'mod_with_max' /x/ /y/ /max/@: reduce /x/ modulo /y/, returning the unique representative /x'/ in the range /max/ – /y/ < /x'/ ≤ /max/.
mod_with_max :: (Integral a) => a -> a -> a -> a
mod_with_max x y max = max - ((max - x) `mod` y)

-- | Integer division with asserts making sure that the denominator
--   indeed divides the numerator.
divchk :: (Show a, Integral a) => a -> a -> a
divchk nom denom =
    if (nom `mod` denom == 0)
        then nom `div` denom
        else error ("divchk: " ++ show denom ++ " does not divide " ++ show nom ++ "!")

-- | @'extended_euclid' /a/ /b/@: return (/d/,/x/,/y/), 
-- such that /d/ = gcd(/a/,/b/), and /ax/ + /by/ = /d/.
extended_euclid :: Integral a => a -> a -> (a, a, a)
extended_euclid a b =
    if (b == 0) then (a, 1, 0) else (d, x, y)
    where
        (d', x', y') = extended_euclid b (a `mod` b)
        (d,  x,  y ) = (d', y', x' - (a `div` b)*y')

-- | @/a/ `divides` /b/@: return 'True' if /a/ divides /b/.
divides :: (Integral a) => a -> a -> Bool
divides denom nom = (nom `mod` denom == 0)

-- | Test whether a real number is an integer.
is_int :: (RealFrac a, Eq a) => a -> Bool
is_int x = x == (fromIntegral $ round x)

-- | Generate the list of integers describing the continued fraction of a given
--   rational number. Since the number is rational, the expansion is finite.
-- 
-- Each rational number /q/ is equal to a unique expression of the form
-- 
-- > [image contfrac.png]
-- 
-- where /n/ ≥ 0, /a/[sub 0] is an integer, /a/[sub 1], …, /a/[sub /n/] are
-- positive integers, and /a/[sub /n/] ≠ 1 unless /n/=0. This is called the 
-- (short) continued fraction expansion of /q/. The function 'continued_list' inputs
-- two integers /num/ and /denom/, computes the continued fraction expansion of 
-- /q/ = /num/ \/ /denom/, and returns the non-empty sequence 
-- [/a/[sub 0], …, /a/[sub /n/]].  
continued_list :: (Integral int) => int -> int -> [int]
continued_list _   0     = []
continued_list num denom =
    int_part : continued_list denom num'
    where
        int_part = num `div` denom
        num'     = num - int_part*denom

-- | Generate a list of convergents from a continued fraction (as described by
--   the non-empty list of integers of that fraction).
convergents :: (Integral int, Fractional a) => [int] -> [a]
convergents as = recursive (0,1) (1,0) as 
  where
    recursive (h0, k0) (h1, k1) [] = []
    recursive (h0, k0) (h1, k1) (a2:as) = b2 : recursive (h1, k1) (h2, k2) as 
      where
        h2 = a2 * h1 + h0
        k2 = a2 * k1 + k0
        b2 = (fromIntegral h2) / (fromIntegral k2)
    
-- ===========================================
-- * Quantum functions
-- ===========================================

-- ===========================================
-- ** Generic blackboxing

-- | Unimplemented components need to be given as black boxes — like named gates,
-- except their types may not just be an endomorphism; like subroutines, except
-- with only a placeholder on the inside.
--
-- For this module, black boxes are only needed for classical functional routines,
-- i.e. with type qa -> Circ (qa, qb)
blackbox :: (QData qa, QData qb) => String -> qb -> qa -> Circ (qa,qb)
blackbox n out_shape = box n $ \qx -> do
  qy <- qinit $ qc_false out_shape
  (qx,qy) <- named_gate n (qx,qy)
  return (qx,qy)

-- ===========================================
-- ** Boxed imported arithmetic

-- $ To reduce the printed sizes of circuits, we box all imported arithmetic components. 

-- | Like 'box', but prepends \"Arith.\" to subroutine names, 
-- as a crude form of namespace management.
arithbox :: (QCData qa, QCData qb, QCurry qa_qb qa qb) => String -> qa_qb -> qa_qb
arithbox n = box ("Arith." ++ n)

-- | Boxed analogue of 'Arith.q_ext_euclid'.
q_ext_euclid :: QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt,QDInt,QDInt)
q_ext_euclid = arithbox "q_ext_euclid" Arith.q_ext_euclid

-- | Boxed analogue of 'Arith.q_add'.
q_add :: QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt)
q_add = arithbox "q_add" Arith.q_add

-- | Boxed analogue of 'Arith.q_mult'.
q_mult :: (QCData qa, QNum qa)
       => qa -> qa -> Circ (qa,qa,qa)
q_mult = arithbox "q_mult" Arith.q_mult

-- | Boxed analogue of 'Arith.q_div_exact'.
q_div_exact :: QDInt -> QDInt -> Circ (QDInt, QDInt, QDInt)
q_div_exact = arithbox "q_div_exact" Arith.q_div_exact

-- | Boxed analogue of 'Arith.q_add_in_place'.
q_add_in_place :: QDInt -> QDInt -> Circ (QDInt, QDInt)
q_add_in_place = arithbox "q_add_in_place" Arith.q_add_in_place

-- | Boxed analogue of 'Arith.q_add_param_in_place'.
q_add_param_in_place ::IntM -> QDInt -> Circ QDInt
q_add_param_in_place = Arith.q_add_param_in_place
{- Currently doesn’t work:
q_add_param_in_place n = 
  arithbox ("q_add_param_in_place; n = " ++ show n ++ "; ") (Arith.q_add_param_in_place n)
-}

-- | Boxed analogue of 'Arith.q_div'.
q_div :: QDInt -> QDInt -> Circ (QDInt, QDInt, QDInt)
q_div = arithbox "q_div" Arith.q_div

-- | Boxed analogue of 'Arith.q_mult_param'.
q_mult_param :: IntM -> QDInt -> Circ (QDInt, QDInt)
q_mult_param = Arith.q_mult_param
{- Currently doesn’t work:
q_mult_param n =
  arithbox ("q_mult_param; n = " ++ show n ++ "; ") (Arith.q_mult_param n)
-}

-- | Boxed analogue of 'Arith.q_mod_unsigned'.
q_mod_unsigned :: QDInt -> QDInt -> Circ (QDInt, QDInt, QDInt)
q_mod_unsigned = arithbox "q_mod_unsigned" Arith.q_mod_unsigned

-- | Boxed analogue of 'Arith.q_sub_in_place'.
q_sub_in_place :: QDInt -> QDInt -> Circ (QDInt, QDInt)
q_sub_in_place = arithbox "q_sub_in_place" Arith.q_sub_in_place

-- | Boxed analogue of 'Arith.q_increment'.
q_increment :: QDInt -> Circ QDInt
q_increment = arithbox "q_increment" Arith.q_increment

-- ===========================================
-- ** Other arithmetic functions

-- | Turn a 'QDInt' into an 'FPRealQ', with shape specified by another 'FPRealQ'
fprealq_of_QDInt_with_shape :: FPRealQ -> QDInt -> Circ (QDInt, FPRealQ)
fprealq_of_QDInt_with_shape = blackbox "fprealq_of_QDInt_with_shape" 

-- | Divide a 'QDInt' by 2, in place.  (Behavior on odd integers: so far, not required.)
-- As this is not required on odd integers, we can assume that the least significant
-- bit is 0, and use an operation equivalent to a right rotate, instead of a right
-- shift. This can be achieved by changing the list indices within the 'QDInt', and not
-- a quantum operation, but this operation is *NOT* controllable.
q_div2 :: QDInt -> Circ QDInt
q_div2 = return . qdint_of_qulist_bh . rotate . qulist_of_qdint_bh
  where
    rotate as = last as:init as

-- | Square a 'QDInt'. This is achieved by creating a copy of the input, using the
-- out of place multiplier, and then uncopying the input.
q_square :: QDInt -> Circ (QDInt,QDInt)
q_square qx = do
  qx' <- qc_copy qx
  (qx,qx',qxqx) <- q_mult qx qx'
  qx <- qc_uncopy_fun qx qx'
  return (qx,qxqx)

-- | Test whether a 'QDInt' is (strictly) greater than a parameter 'IntM'.
q_gt_param :: QDInt -> IntM -> Circ (QDInt,Qubit)
q_gt_param qx y = do
  let y' = intm_promote y qx "q_gt_param: qx and y must be of the same length"
  qy <- qinit y'
  (qx, qy, qx_gt_y) <- q_gt qx qy
  qterm y' qy
  return (qx, qx_gt_y)

-- | Test whether a 'QDInt' is greater than or equal to a parameter 'IntM'.
q_ge_param :: QDInt -> IntM -> Circ (QDInt,Qubit)
q_ge_param qx y = do
  let y' = intm_promote y qx "q_ge_param: qx and y must be of the same length"
  qy <- qinit y'
  (qx, qy, qx_ge_y) <- q_ge qx qy
  qterm y' qy
  return (qx, qx_ge_y)

-- | @'q_mod' /x/ /y/@: reduce /x/ modulo /y/.  /x/ is treated as signed, /y/ as unsigned.
--
--  Note: not non-linear safe in /x/.
q_mod_semi_signed :: QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt)
q_mod_semi_signed = box "mod" $ \x y -> do
-- Approach: if x < 0, then (-1-x) >= 0, and 
-- x `mod` y == (y-1) - ((-1-x) `mod` y) 
-- 
-- The (cheap) operations before and after 'q_mod' are therefore conditioned
-- on the sign of x; the (expensive) 'q_mod' is performed just once,
-- unconditionally.
  x_mod_y <- with_computed
    (do
      sign_x <- case qdint_length x of
        0 -> qinit False
        _ -> qc_copy $ head $ qulist_of_qdint_bh x
      x <- q_negate_in_place x `controlled` sign_x
      x <- q_decrement x `controlled` sign_x
      (_, _, x') <- q_mod_unsigned x y
      x' <- q_increment x' `controlled` sign_x
      x' <- q_negate_in_place x' `controlled` sign_x
      (y,x') <- q_add_in_place y x' `controlled` sign_x
      return x')
    qc_copy
  return (x, y, x_mod_y)

-- | @'q_mod_with_max' /x/ /y/ /m/@: reduce /x/ modulo /y/, into the range /max/ – /y/ < /x'/ ≤ /max/.  (Compare 'mod_with_max'.)
q_mod_with_max :: QDInt -> QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt,QDInt)
q_mod_with_max x y m = do
  -- Goal: max - ((max - x) `mod` y)
  x_modmax_y <- with_computed
    (do
      (_, _, x') <- q_sub m x
      (_, _, x'_mod_y) <- q_mod_semi_signed x' y
      (_, _, x_modmax_y) <- q_sub m x'_mod_y
      return x_modmax_y)
    qc_copy
  return (x, y, m, x_modmax_y)


-- | Obsolete function, retained for testing since it evokes a subtle bug in 'with_computed'. 
q_mod_2times_buggy :: QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt)
q_mod_2times_buggy x a = do
  x_mod_2a <- with_computed ( do
    a' <- qc_copy a 
    (a,two_a) <- q_add_in_place a a'
    x' <- qc_copy x
    (x_mod_2a,two_a,x_div_2a) <- q_moddiv_unsigned_in_place x' two_a
    return x_mod_2a
   ) ( \x_mod_2a -> do
    x_mod_2a' <- qc_copy x_mod_2a 
    return x_mod_2a'      
   )
  return (x,a,x_mod_2a)

-- ======================================================================
-- ** Looping combinators

-- | Perform a bounded while loop, whose body may produce extra output.  
q_bounded_while_with_garbage :: (QData qa, QCData qb) =>
  (qa -> Circ (qa,Qubit))  -- ^ the conditional test on the data
  -> Int                   -- ^ a bound on the number of times the loop can run
  -> qa                    -- ^ the starting value
  -> (qa -> Circ (qa,qb))  -- ^ the body of the loop
  -> Circ (qa,qa)          -- ^ the initial and final values, and the produced data
q_bounded_while_with_garbage _ 0 x _ = qc_copy_fun x
q_bounded_while_with_garbage test bound x body = do
  (x, x_really_out) <- with_computed_fun x
    (\x -> do
      x_out <- qinit $ qc_false x 
      failed_before <- qinit False
      (x_final, x_out, failed_ever, loop_garbage) <- loopM bound (x, x_out, failed_before, [])
        (\(x_cur, x_out, failed_before, garbage) -> do
          (x_cur, good_now) <- test x_cur
          -- If we fail now for the first time, copy the current value to the output value:
          (x_out, x_cur) <- controlled_not x_out x_cur `controlled` good_now .==. 0 .&&. failed_before .==. 0
          -- Going forward, we’ve failed unless we’re good now *and* we’ve not failed before:
          failed_now <- qinit True
          failed_now <- qnot failed_now `controlled` good_now .==. 1 .&&. failed_before .==. 0
          -- In any case, apply the body again:
          (x_cur, new_garbage) <- body x_cur
          return (x_cur, x_out, failed_now, (good_now, failed_before, new_garbage):garbage))
      -- If the loop never finished, copy its last value to the output value:
      (x_out, x_final) <- controlled_not x_out x_final `controlled` failed_ever .==. 0
      return (x_out, (x_final, failed_ever, loop_garbage)))
    (\(x_out, garbage) -> do
      (x_out, x_really_out) <- qc_copy_fun x_out
      return ((x_out, garbage), x_really_out))
  return (x, x_really_out)

-- | Perform a bounded-length while loop, with an endo-typed body.
--
-- Note: uses /2 * bound/ ancillas.  Can this be avoided?
q_bounded_while :: (QCData qa) =>
  (qa -> Circ (qa,Qubit))  -- ^ the conditional statement
  -> Int                   -- ^ a bound on the number of times the loop can run
  -> qa                    -- ^ the starting value
  -> (qa -> Circ qa)       -- ^ the body of the loop
  -> Circ (qa,qa)          -- ^ return the initial value, and the final post-loop value
q_bounded_while _ 0 x _ = qc_copy_fun x
q_bounded_while test bound x body =
  with_computed_fun x
    (\x -> do
      (x,c) <- test x 
      x <- body x `controlled` c
      return (x,c))

    (\(x,c) -> bw_aux (bound-1) x c)
  where
--  Auxiliary function: perform the loop with a running control qubit,
--  to avoid building up multi-ary controls:
--    bw_aux :: Int -> qa -> Qubit -> Circ ((qa,Qubit),qa)
--    Oddly, Haskell reads this type signature as generalising qa,
--    causing the following to fail to typecheck. 
    bw_aux 0 x c = do (x,x') <- qc_copy_fun x; return ((x,c),x')
    bw_aux bound x c = do
      with_computed_fun (x,c)
        (\(x,c) -> do
          (x,c') <- test x
          c'' <- qinit False
          c'' <- qnot c'' `controlled` [c,c']
          x <- body x `controlled` c''
          return (x,c,c',c''))
        (\(x,c,c',c'') -> do
          ((x,c''),x') <- bw_aux (bound-1) x c''
          return ((x,c,c',c''),x'))

-- | Perform a bounded while loop, whose body may produce extra output.  
q_bounded_while_productive :: (QCData qa, QCData qb) =>
  (qa -> Circ (qa,Qubit))  -- ^ the conditional test on the data
  -> Int                   -- ^ a bound on the number of times the loop can run
  -> qa                    -- ^ the starting value
  -> (qa -> Circ (qa,qb))  -- ^ the body of the loop
  -> Circ (qa,qa,[qb])     -- ^ the initial and final values, and the produced data
q_bounded_while_productive test bound x body = do
  ((x,[]),(x',ys)) <-
    q_bounded_while 
      (\(x,ys) -> do (x,c) <- test x; return ((x,ys),c))
      bound
      (x,[])
      (\(x,ys) -> do (x,y_new) <- body x; return (x,y_new:ys))
  return (x,x',ys)

-- | Perform a bounded “do_until” loop.  
q_do_until :: (QCData qa) =>
  Int                      -- ^ a bound on the number of times the loop can run
  -> qa                    -- ^ the starting value
  -> (qa -> Circ (qa,Qubit))  -- ^ the body of the loop, producing an input to the next iteration, plus a qubit to mark if we’re finished yet. 
  -> Circ (qa,qa)          -- ^ return the initial and final values
q_do_until bound x body = do
  with_computed_fun x body
    (\(x,c) -> do_aux (bound-1) x c)
  where
--    Auxiliary function: perform the loop with a running control qubit,
--    to avoid building up multi-ary controls:
--  do_aux :: Int -> qa -> Qubit -> Circ ((qa,Qubit),qa)
--    Oddly, Haskell reads this type signature as generalising qa,
--    causing the following to fail to typecheck. 
    do_aux 0 x c = do (x,x') <- qc_copy_fun x; return ((x,c),x')
    do_aux bound x c = do
      with_computed_fun (x,c)
        (\(x,c) -> do
          (x,c') <- body x `controlled` c
          c'' <- qinit False
          c'' <- qnot c'' `controlled` [c,c']
          return (x,c,c',c''))
        
        (\(x,c,c',c'') -> do
          ((x,c''),x') <- do_aux (bound-1) x c''
          return ((x,c,c',c''),x'))
