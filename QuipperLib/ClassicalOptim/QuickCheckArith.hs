-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module contains small examples of arithmetic functions,
-- coded in Template Haskell, for use with
-- "QuipperLib.ClassicalOptim.QuickCheck".
module QuipperLib.ClassicalOptim.QuickCheckArith where

import qualified Test.QuickCheck as Test

import Quipper

import Data.List
import Quipper
import QuipperLib.Arith
import Libraries.Auxiliary
import Prelude hiding (subtract)

-- ----------------------------------------------------------------------
-- * Binary representation of integers

-- | Compute an unsigned integer from its binary representation. The
-- input is a big-headian list of booleans. This means that the head
-- of the list is the most significant digit.
int_of_boollist :: [Bool] -> Integer
int_of_boollist = integer_of_intm_unsigned . intm_of_boollist_bh . reverse

-- | Compute the binary representation of an unsigned integer, using
-- the given number of digits. The output is the binary representation
-- as a big-headian list of booleans.
boollist_of_int :: Int -> Integer -> [Bool]
boollist_of_int m n = reverse (boollist_of_intm_bh $ intm_with_length (Just m) n)

-- ----------------------------------------------------------------------
-- * Circuit templates for common functions

-- | Template Haskell version of 'map'.
template_map :: Circ ((a -> Circ a) -> Circ ([a] -> Circ [a]))
template_map = return $ \func -> return $ \qs -> mapM func qs

-- | Template Haskell version of 'zip'.
template_zip :: Circ ([a] -> Circ ([b] -> Circ [(a,b)]))
template_zip = return $ \a -> return $ \b -> return (zip a b)

-- | Template Haskell version of 'tail'.
template_tail :: Circ ([a] -> Circ [a])
template_tail = return $ \t -> return $ tail t

-- | Template Haskell version of @[]@.
template_symb_obracket_symb_cbracket_ :: Circ [a]
template_symb_obracket_symb_cbracket_ = return []

-- | Monadic version of 'mapAccumL'.
mapAccumLM :: (acc -> x -> Circ (acc,y)) -> acc -> [x] -> Circ (acc,[y])
mapAccumLM f acc [] = return (acc,[])
mapAccumLM f acc (h:t) = do
     (a,y) <- f acc h
     (a',t') <- mapAccumLM f a t
     return (a',y:t')        

-- | Template Haskell version of 'mapAccumL'.
template_mapAccumL :: Circ ((acc -> Circ (x -> Circ (acc,y))) -> Circ (acc -> Circ ([x] -> Circ (acc,[y]))))
template_mapAccumL = return $ \fcirc -> return $ \acc -> return $ \xs ->
                       let f = (\acc x -> do
                                  g <- fcirc acc
                                  g x)
                       in mapAccumLM f acc xs

-- ----------------------------------------------------------------------
-- * Tests

-- ----------------------------------------------------------------------
-- ** Addition

-- | Return the majority of three booleans.
build_circuit
majority :: Bool -> Bool -> Bool -> Bool
majority a b c = if (a `bool_xor` b) then c else a
                                                 
-- majority a b c = a `bool_xor` ((a `bool_xor` b) && (a `bool_xor` c))

-- | Bit adder. The first input is 'False' for adding, and 'True' for
-- subtracting. The second input is a triple consisting of a carry,
-- and two bits to be added. The output consists of the new carry and
-- the sum.
build_circuit
bit_adder :: Bool -> (Bool,Bool,Bool) -> (Bool,Bool)
bit_adder sign (carry, x,y) =
      let y' = y `bool_xor` sign in
      let z = carry `bool_xor` x `bool_xor` y' in
      let carry' = majority carry x y' in
      (carry', z)


-- | Multi-bit adder. Add two /n/-bit integers, represented as
-- little-tailian bit lists.
build_circuit
adder :: [Bool] -> [Bool] -> [Bool]
adder f l = 
  reverse $ snd $ fold_right_zip (bit_adder False) (False, reverse l, reverse f)

-- | Test the validity of the functional implementation of 'adder'.
test_adder' :: Test.Property
test_adder' = Test.forAll (Test.choose (0,255)) $ \x ->
                   Test.forAll (Test.choose (0,255)) $ \y ->
                   boollist_of_int 9 (x + y) 
                   == 
                   adder (boollist_of_int 9 x) (boollist_of_int 9 y)

-- | Wrapper around 'test_adder''.
test_adder :: IO ()
test_adder = Test.quickCheck test_adder'

-- ----------------------------------------------------------------------
-- ** Subtraction

-- | Reversible subtraction.
build_circuit
subtract :: [Bool] -> [Bool] -> [Bool]
subtract f l = 
  let l' = map not l in 
  case l' of
    [] -> []
    (h:t) -> let one = (True:(map (\x -> False) t)) in
             adder one (adder f l')

-- | Test the validity of the functional implementation of 'subtract'.
test_subtract' :: Test.Property
test_subtract' = Test.forAll (Test.choose (0,255)) $ \x ->
                   Test.forAll (Test.choose (0,255)) $ \y ->
                   boollist_of_int 9 x 
                   == 
                   subtract (boollist_of_int 9 (x+y)) (boollist_of_int 9 y)

-- | Wrapper around 'test_subtract''.
test_subtract :: IO ()
test_subtract = Test.quickCheck test_subtract'

-- ----------------------------------------------------------------------
-- ** Multiplication

-- | Pad the second list on the right, to the length of (and using the
-- corresponding elements of) the first list.
build_circuit
pad_right :: [Bool] -> [Bool] -> [Bool]
pad_right shape l = case (shape,l) of
                       (shape, []) -> shape
                       ([], l)     -> l
                       ((_:t1), (h:t2)) -> h:(pad_right t1 t2)

-- | Shift a bit list to the right by one.
build_circuit
shift :: [Bool] -> [Bool]
shift l = False:l

-- | 'takeOnly' /shape/ /l/: take the first @('length' /shape/)@
-- elements out of /l/.
build_circuit
takeOnly :: [Bool] -> [Bool] -> [Bool]
takeOnly _  [] = []
takeOnly [] _  = []
takeOnly (h1:t1) (h2:t2) = h2:(takeOnly t1 t2) 


-- | Reversible multiplier stripping high bits.
build_circuit
multiplier' :: [Bool] -> [Bool] -> [Bool]
multiplier' l1 l2 = 
     let zero = map (\x -> False) (l1 ++ l2) in
     takeOnly l1 $ foldl adder zero (snd (
        mapAccumL 
          (\acc x -> (False:acc, pad_right zero (acc ++ (map (\y -> y && x) l1)))) [] l2
     ))


-- | Reversible multiplier keeping high bits.
build_circuit
multiplier :: [Bool] -> [Bool] -> [Bool]
multiplier l1 l2 = 
     let zero = map (\x -> False) (l1 ++ l2) in
     foldl adder zero (snd (
        mapAccumL 
          (\acc x -> (False:acc, pad_right zero (acc ++ (map (\y -> y && x) l1)))) [] l2
     ))

-- | Test the validity of the functional implementation of 'multiplier'.
test_multiplier' :: Test.Property
test_multiplier' = Test.forAll (Test.choose (0,255)) $ \x ->
                   Test.forAll (Test.choose (0,255)) $ \y ->
                   boollist_of_int 18 (x * y) 
                   == 
                   multiplier (boollist_of_int 9 x) (boollist_of_int 9 y)

-- | Wrapper around 'test_multiplier''.
test_multiplier :: IO ()
test_multiplier = Test.quickCheck test_multiplier'

