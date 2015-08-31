-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | Test the Class Number algorithm, and its components, using classical computation

module Algorithms.CL.Test where

import Quipper
import QuipperLib.Arith
import QuipperLib.FPReal
import Algorithms.CL.Auxiliary
import Algorithms.CL.Types
import Algorithms.CL.RegulatorClassical
import Algorithms.CL.CL
import Algorithms.CL.SmithReduction
import Data.Ratio
import Data.List

-- * Sample data

-- $ Some fairly arbitrarily chosen sample elements of various types, for convenience in testing functions.

-- ** Matrices

-- | A sample square matrix
sample_matrix :: CLMatrix Integer
sample_matrix = matrix_from_list [
    [  8,  16, 16 ],
    [ 32,  6,  12 ],
    [  8, -4, -16 ]
 ]

-- | A sample non-square matrix
sample_matrix_2 :: CLMatrix Integer
sample_matrix_2 = matrix_from_list [
    [ 5, 1, 5, 253, 15, -725, 1 ],
    [ 253,2,1001,11,23,273,14079 ],
    [ 1,-185861,-28,11,91,29,-2717 ],
    [ -319,1,-19,11,3146,1,-1 ],
    [ 19285,-493,145,25,-1482,1,6647]
 ]

-- | Another sample non-square matrix
sample_matrix_3 :: CLMatrix Integer 
sample_matrix_3 = matrix_from_list [
    [ 4, 8, 4 ],
    [ 8, 4, 8 ]
 ]

-- ** Ideals and related types

-- | A sample 'CLReal'.
sample_CLReal :: Int -> FPReal
sample_CLReal l = (fprealx 0 (intm l 0))

-- | A sample 'Ideal'.
sample_Ideal :: CLIntP -> Ideal
sample_Ideal bigD =
  let l = max (length_for_ab bigD) (length_for_ml bigD)
      x = (intm l 0)
  in (Ideal bigD x x x x)

-- | A sample 'IdealQ'.
sample_IdealQ :: CLIntP -> IdealQ
sample_IdealQ = qshape . sample_Ideal

-- | A sample 'IdealRed'.
sample_IdealRed :: CLIntP -> IdealRed
sample_IdealRed bigD =
  let l = max (length_for_ab bigD) (length_for_ml bigD)
      x = (intm l 0)
  in (IdealRed bigD x x)

-- | A sample 'IdealRedQ'.
sample_IdealRedQ :: CLIntP -> IdealRedQ
sample_IdealRedQ = qshape . sample_IdealRed

-- | A sample 'IdDist'.
sample_IdDist :: CLIntP -> IdDist
sample_IdDist bigD = (sample_Ideal bigD, sample_CLReal (length_for_ab bigD))

-- | A sample 'IdDistQ'.
sample_IdDistQ :: CLIntP -> IdDistQ
sample_IdDistQ = qshape . sample_IdDist

-- | A sample 'IdRedDist'.
sample_IdRedDist :: CLIntP -> IdRedDist
sample_IdRedDist bigD = (sample_IdealRed bigD, sample_CLReal (length_for_ab bigD))

-- | A sample 'IdRedDistQ'.
sample_IdRedDistQ :: CLIntP -> IdRedDistQ
sample_IdRedDistQ = qshape . sample_IdRedDist

-- * Testing routines

-- ** Smith reduction

-- | Test the Smith Normal Form code.
test_SNF :: IO ()
test_SNF = do
    flip mapM_ [sample_matrix,sample_matrix_2,sample_matrix_3] $ \m -> do
      putStrLn $ show $ m
      putStrLn $ show $ structure_constants_from_matrix m
      putStrLn $ show $ group_order_from_matrix m
      putStrLn ""

-- ** Class group functions

-- | Classical period finding (just compare the \"next\" ideal to /O/ and see if
--   it is the same). Takes in the /O/ ideal with appropriate Δ, and returns
--   the circle length (sum δ(I)) and the list of ideals in the first iteration.
period_of_ideals :: (IdDist->IdDist) -> IdDist -> (CLReal, [IdDist])
period_of_ideals func o = (delta $ last list, list)
    where
        list = takePeriod False (iterate (\i -> func i) o)
        takePeriod :: Bool -> [IdDist] -> [IdDist]
        takePeriod got_first_o [] = undefined -- not reached
        takePeriod got_first_o (x:xs) =
            if (fst x == fst o) then
                if (got_first_o) then
                    [x]                     -- Have two O's, stop iterating here
                else
                    x : takePeriod True xs  -- This was first O, mark as such
            else
                x : takePeriod got_first_o xs

-- | Show period string for a given Δ.
show_period_for_bigD :: CLIntP -> String
show_period_for_bigD bigD =
    let (delta, ideals) = period_of_ideals rho_d $ (unit_ideal bigD, 0)
     in "For bigD=" ++ (show bigD) ++ " the period has "
                 ++ (show $ (length ideals) - 1) ++ " ideals and sum delta is "
                 ++ (show delta)

-- | Show the period for the first /n/ valid Δ's.
show_period_for_many_bigDs :: Int -> IO()
show_period_for_many_bigDs n = do
   putStrLn $ unlines $ map (\bigD -> show_period_for_bigD bigD) $ sort $ take n all_bigDs

-- | Show period string and the list of ideals for a given Δ.
show_period_for_some_bigD :: CLIntP -> IO()
show_period_for_some_bigD bigD = do
    putStrLn $ show_period_for_bigD bigD
    putStrLn "Fwd rho_d:"
    putStrLn $ unlines $ map printIdeal ideals
    putStrLn "Inv rho_d:"
    putStrLn $ unlines $ map printIdeal invideals
    where
        (delta,    ideals)    = period_of_ideals rho_d    $ (unit_ideal bigD, 0)
        (invdelta, invideals) = period_of_ideals rho_inv_d $ (unit_ideal bigD, 0)
        printIdeal ideal =
            (show ideal)
            ++ " Reduced: "
            ++ if (is_reduced $ fst ideal) then "true" else "false"

-- | Show a list of valid Δ's.
show_bigDs :: Int -> IO()
show_bigDs n = do
    putStrLn $ show $ take n all_bigDs

-- | Explicitly compute first few ideals for some Δ.
first_few :: IO()
first_few = do
    putStrLn $ "O   :" ++ show j_0
    putStrLn $ "j1/2:" ++ show j_05
    putStrLn $ "j1  :" ++ show j_1
    where
        bigD = 17
        j_0  = (unit_ideal bigD, 0)
        j_05 = rho_d j_0
        j_1  = rho_d j_05

-- | Perform an operation on all ideal pairs that are generated by Δ.
op_all_ideals :: (IdDist -> IdDist -> IdDist) -> String -> CLIntP -> IO()
op_all_ideals op opString bigD = do
    putStrLn $ unlines $ [ doOp i j | i <- ideals, j <- ideals ]
    where
        (delta, ideals_with_o) = period_of_ideals rho_d $ (unit_ideal bigD, 0)
        ideals = init ideals_with_o
        doOp i j = "(" ++ (show i) ++ ")" ++ opString ++ "(" ++ (show j) ++ ") = "
                    ++ (show (i_op_j))
                    ++ " Reduced:"
                    ++ (if (is_reduced $ fst i_op_j) then "true" else "false")
--                    ++ " rho_d of:" ++ (show $ rho_d i_op_j)
                    where i_op_j = i `op` j

-- | The the product of all pairs of ideals for a given Δ.
dot_all_ideals :: CLIntP -> IO()
dot_all_ideals bigD = op_all_ideals dot "." bigD

-- | Take the star product of all pairs of ideals for a given Δ.
star_all_ideals :: CLIntP -> IO()
star_all_ideals bigD = op_all_ideals star "*" bigD

-- | Test the 'bounded_while' functionality.
test_bounded_while :: (Show int, Integral int) => int -> int -> IO()
test_bounded_while bound start = do
    putStrLn $ show $
        bounded_while (\k -> k > 0) bound
            (\k -> k-1) start

-- | Run classical tests for Class Number algorithm.
main :: IO()
main = do
--    test_bounded_while 10 5
--    putStrLn $ "a=23, b=-41, bigD=28, tau =" ++ show (tau (-41) 23 28)
--    putStrLn $ "a=23, b=-41, bigD=28, itau=" ++ show (itau (-41) 23 28)
--    putStrLn $ unlines $ testTauForDelta 28 tau
--    first_few
--    showDs 50
--    showPeriodForManyBigDs 400
--    show_period_for_some_bigD 28
--    dot_all_ideals 28
    star_all_ideals 28
--    putStrLn $ show $ rho_d $ (Ideal 28 1 1 9 8, 0)

--    putStrLn $ show $ take 100 all_small_ds
--    putStrLn $ show $ sort $ take 100 all_bigDs

-- For bigD=2524 the period has 48 ideals and sum delta is 41.3199021281136

--    putStrLn $ show $ continued_list 649 200
--    putStrLn $ show $ convergents $ continued_list 649 200

-- | Test the primes code.
test_primes :: IO ()
test_primes = do
--    putStrLn $ show $ jacobi_symbol 1001 9907
--    putStrLn $ show $ jacobi_symbol 14 7
    putStrLn $ show $ primes_to 8000
