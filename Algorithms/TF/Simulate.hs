-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module contains functions for simulating and debugging
-- the Triangle Finding Oracle and its subroutines.

module Algorithms.TF.Simulate where

import Quipper

import QuipperLib.Arith
import QuipperLib.Simulation

import Algorithms.TF.Definitions
import Algorithms.TF.Oracle
import Algorithms.TF.Alternatives

import Data.Maybe

import Libraries.Sampling
import Libraries.Auxiliary (boollist_of_int_bh)

-- ======================================================================
-- * Native and simulated arithmetic functions

-- $ For each arithmetic routine implemented in the Triangle Finding 
-- Oracle, we give two parallel implementations: one using Haskell’s 
-- arithmetic, and one by simulating the circuit execution.
-- 
-- These can then be cross-checked against each other for correctness.

-- | Increment an /m/-bit Quipper integer (mod 2[sup /m/]).  Native Haskell.
increment_haskell :: IntM -> IntM
increment_haskell = succ

-- | Increment an /m/-bit Quipper integer (mod 2[sup /m/]).  Simulated from 
-- 'increment'.
increment_simulate :: IntM -> IntM
increment_simulate = run_classical_generic increment

-- | Increment an /m/-bit Triangle Finding integer (mod 2[sup /m/]–1).  
-- Native Haskell.
incrementTF_haskell :: IntTF -> IntTF
incrementTF_haskell x1 = (inttf m ((x+1) `mod` (2^m - 1)))
  where
    m = fromJust (inttf_length x1)
    x = integer_of_inttf x1
      
-- | Increment an /m/-bit TF integer (mod 2[sup /m/]–1).  Simulated from
--  'increment_TF'.
incrementTF_simulate :: IntTF -> IntTF
incrementTF_simulate = run_classical_generic increment_TF

-- | Double an /m/-bit TF integer (mod 2[sup /m/]–1).  Native Haskell.
doubleTF_haskell :: IntTF -> IntTF
doubleTF_haskell x1 = (inttf m ((2*x) `mod` (2^m - 1)))
  where
    m = fromJust (inttf_length x1)
    x = integer_of_inttf x1

-- | Double an /m/-bit TF integer (mod 2[sup /m/]–1).  Simulated from 
-- 'double_TF'.
doubleTF_simulate :: IntTF -> IntTF
doubleTF_simulate = run_classical_generic double_TF

-- | Add two 'IntTF's.  Native Haskell.
addTF_haskell :: IntTF -> IntTF -> IntTF
addTF_haskell x1 y1 =
  if (m == n) then (inttf m $ (x + y) `mod` (2^m - 1))
              else error "addTF_haskell: Cannot add IntTF’s with different moduli."
    where
      m = fromJust (inttf_length x1)
      x = integer_of_inttf x1
      n = fromJust (inttf_length y1)
      y = integer_of_inttf y1

-- | Add two 'IntTF's.  Simulated from 'o7_ADD'.
addTF_simulate :: IntTF -> IntTF -> IntTF
addTF_simulate =
  run_classical_generic (\x y -> do
    (_,_,z) <- o7_ADD x y
    return z)

-- | Multiply two 'IntTF's.  Native Haskell.
multTF_haskell :: IntTF -> IntTF -> IntTF
multTF_haskell x1 y1 =
  if (m == n) then (inttf m $ (x * y) `mod` (2^m - 1))
              else error "multTF_haskell: Cannot multiply IntTF’s with different moduli."
    where
      m = fromJust (inttf_length x1)
      x = integer_of_inttf x1
      n = fromJust (inttf_length y1)
      y = integer_of_inttf y1

-- | Multiply two 'IntTF's.  Simulated from 'o8_MUL'.
multTF_simulate :: IntTF -> IntTF -> IntTF
multTF_simulate =
  run_classical_generic (\x y -> do
    (_,_,z) <- o8_MUL x y
    return z)

-- | Raise an 'IntTF' to the 17th power.  Native Haskell.
pow17_haskell :: IntTF -> IntTF
pow17_haskell x1 = inttf m ((x^17) `mod` (2^m - 1)) 
    where
      m = fromJust (inttf_length x1)
      x = integer_of_inttf x1

-- | Raise an 'IntTF' to the 17th power.  Simulated from 'o4_POW17'.
pow17_simulate :: IntTF -> IntTF
pow17_simulate =
  run_classical_generic (\x -> do
    (_,z) <- o4_POW17 x
    return z)

-- | Compute the reduction, mod 3, of lower-order bits of an 'IntTF'.  
-- Native Haskell.
mod3_haskell :: IntTF -> IntTF
mod3_haskell x1 = inttf 2 ((x `mod` (2^(m-1))) `mod` 3)
    where
      m = fromJust (inttf_length x1)
      x = integer_of_inttf x1

-- | Compute the reduction, mod 3, of lower-order bits of an 'IntTF'.  
-- Simulated from 'o5_MOD3'.
mod3_simulate :: IntTF -> IntTF
mod3_simulate = 
  run_classical_generic (\x -> do
    (_,z) <- o5_MOD3 x
    return z)

-- | Compute the reduction, mod 3, of lower-order bits of an 'IntTF'.  
-- Simulated from 'o5_MOD3_alt'.
mod3_alt_simulate :: IntTF -> IntTF
mod3_alt_simulate = 
  run_classical_generic (\x -> do
    (_,z) <- o5_MOD3_alt x
    return z)

-- ======================================================================
-- * Native and simulated oracle functions

-- | Oracle: compute the edge information between two nodes.  
-- Native Haskell.
oracle_haskell :: Int -> [Bool] -> [Bool] -> Bool
oracle_haskell l u v 
  | n /= length v = error "oracle_haskell: bad input size: length of v and u must be the same" 
  | n >= l        = error "oracle_haskell: bad input size: n must be less than l"
  | otherwise =
    if uint == vint then False
    else if (u17 == uint) && (v17 == vint) then True
    else if (u17 /= uint) && (v17 /= vint) then
      (uH /= vH) && (u3 /= v3) 
    else (u3 == v3) 
    where 
     modup z n = ((z-1) `mod` n) + 1
     n = length u :: Int
     hn = 2^(n-1)
     incl :: [Bool] -> Integer
     incl x = 
       ((sum [ if b then 2^i else 0 | (b,i) <- zip x [0..]]) - hn)
       `modup` (2^l - 1)
     uint = incl u
     vint = incl v
     u17 = (uint^17) `modup` (2^l - 1)
     v17 = (vint^17) `modup` (2^l - 1)
     u3 = (u17 `mod` 2^(l-1)) `modup` 3
     v3 = (v17 `mod` 2^(l-1)) `modup` 3
     uF = u17 == uint
     vF = v17 == vint
     uH = (uint >= 2^(l-1))
     vH = (vint >= 2^(l-1))

-- | Oracle: compute the edge information between two nodes.  
-- Simulated from 'o1_ORACLE'.
oracle_simulate :: Int -> [Bool] -> [Bool] -> Bool
oracle_simulate l =
  run_classical_generic (\u v -> do
    e <- qinit False
    (u,v,e) <- o1_ORACLE l u v e
    return e)


-- | Oracle auxiliary information.  Native Haskell.
oracle_aux_haskell :: Int -> [Bool] -> [Bool] -> 
  (([Bool], [Bool]),
    (IntTF, IntTF, IntTF, IntTF, IntTF, IntTF),
    (Bool, Bool, Bool, Bool, Bool, Bool, Bool))
oracle_aux_haskell l u v
  | n /= length v = error "oracle_aux_haskell: bad input size: length of v and u must be the same" 
  | n >= l        = error "oracle_aux_haskell: bad input size: n must be less than l"
  | otherwise =
    ((u,v),(inttf l uint,inttf l vint,inttf l u17,inttf l v17,inttf 2 u3,inttf 2 v3),(uF,vF,uH,vH,t_uv,t_uHvH,t_u3v3))
    where 
     modup z n = ((z-1) `mod` n) + 1
     n = length u :: Int
     hn = 2^(n-1)
     incl :: [Bool] -> Integer
     incl x = 
       ((sum [ if b then 2^i else 0 | (b,i) <- zip x [0..]]) - hn)
       `modup` (2^l - 1)
     uint = incl u
     vint = incl v
     u17 = (uint^17) `modup` (2^l - 1)
     v17 = (vint^17) `modup` (2^l - 1)
     u3 = (u17 `mod` 2^(l-1)) `modup` 3
     v3 = (v17 `mod` 2^(l-1)) `modup` 3
     uF = u17 == uint
     vF = v17 == vint
     uH = (uint >= 2^(l-1))
     vH = (vint >= 2^(l-1))
     t_uv = uint == vint
     t_uHvH = uH == vH
     t_u3v3 = u3 == v3


-- | Oracle auxiliary information.  Simulated from 'o1_ORACLE_aux'.
oracle_aux_simulate :: Int -> [Bool] -> [Bool] -> 
  (([Bool], [Bool]),
    (IntTF, IntTF, IntTF, IntTF, IntTF, IntTF),
    (Bool, Bool, Bool, Bool, Bool, Bool, Bool))
oracle_aux_simulate l =
  run_classical_generic (\u v -> o1_ORACLE_aux l (2^((length u)-1)) (u,v))

-- | A specialized 'show' for oracle auxiliary data.
show_oracle_details :: Show a => (([Bool], [Bool]),
    (a,a,a,a,a,a),
    (Bool, Bool, Bool, Bool, Bool, Bool, Bool))
    -> String
show_oracle_details ((u,v),(uint,vint,u17,v17,u3,v3),(uF,vF,uH,vH,t_uv,t_uHvH,t_u3v3))
  = (showBits u) ++ " " ++ (showBits v) ++ " " ++
    showBits [uF,vF,uH,vH,t_uv,t_uHvH,t_u3v3] ++ " " ++
    show [uint,vint,u17,v17,u3,v3]
  where
    showBits :: [Bool] -> String
    showBits [] = "[]"
    showBits bs = map (\b -> if b then '1' else '0') bs

-- | Conversion of a node to an integer.  Native Haskell.
convertNode_haskell :: Int -> [Bool] -> IntTF
convertNode_haskell l u = inttf l (incl u)
  where
   incl :: [Bool] -> Integer
   incl u = 
     ((sum [ if b then 2^i else 0 | (b,i) <- zip u [0..]]) - (2^((length u)-1)))
     `mod` (2^l - 1)

-- | Conversion of a node to an integer.  Simulated from 'o2_ConvertNode'.
convertNode_simulate :: Int -> [Bool] -> IntTF
convertNode_simulate l = run_classical_generic (\u -> do
     (u,uint) <- o2_ConvertNode l u (2^((length u)-1))
     return uint)

-- ======================================================================
-- * Testing functions

-- $ Various small test suites, checking the simulated circuit arithmetic
-- functions against their Haskell equivalents.

-- | Give full table  of values for 'increment' functions. 
increment_table :: Int -> [String]
increment_table l = [ "increment table for l = " ++ (show l) ++ ":"
                      , ""
                      , "x   x+H         x+Q      "]
                    ++
                      [ (show x) ++ "   " ++ (show x_h) ++ "   " ++ (show x_q) ++ flag
                      | x <- [0..(2^l - 1)]
                      , let x_h = integer_of_intm_unsigned $ increment_haskell (intm l x) 
                      , let x_q = integer_of_intm_unsigned $ increment_simulate (intm l x)
                      , let flag = if x_h /= x_q then "  **MISMATCH**" else ""]  
                    ++
                      ["",""]

-- | Give full table  of values for the 'increment_TF' functions. 
incrementTF_table :: Int -> [String]
incrementTF_table l = [ "incrementTF table for l = " ++ (show l) ++ ":"
                      , ""
                      , "x   x+H         x+Q      "]
                    ++
                      [ (show x) ++ "   " ++ (show x_h) ++ "   " ++ (show x_q) ++ flag
                      | x <- [0..(2^l - 2)]
                      , let x_h = incrementTF_haskell (inttf l x) 
                      , let x_q = incrementTF_simulate (inttf l x)
                      , let flag = if x_h /= x_q then "  **MISMATCH**" else ""]
                    ++
                      ["",""]

-- | Give full table  of values for the 'double_TF' functions. 
doubleTF_table :: Int -> [String]
doubleTF_table l = [ "doubleTF table for l = " ++ (show l) ++ ":"
                      , ""
                      , "x  2xH         2xQ      "]
                    ++
                      [ (show x) ++ "   " ++ (show x_h) ++ "   " ++ (show x_q) ++ flag
                      | x <- [0..(2^l - 2)]
                      , let x_h = doubleTF_haskell (inttf l x) 
                      , let x_q = doubleTF_simulate (inttf l x)
                      , let flag = if x_h /= x_q then "  **MISMATCH**" else ""]
                    ++
                      ["",""]

-- | Give full table  of values for the TF addition ('o7_ADD') 
-- functions. 
addTF_table :: Int -> [String]
addTF_table l = [ "addTF table for l = " ++ (show l) ++ ":"
                , ""
                , "x   y   x+yH          x+yQ      "]
              ++
                [ (show x) ++ "   " ++ (show y) ++ "   "
                   ++ (show xyh) ++ "     " ++ (show xyq)
                   ++ flag
                | x <- [0..(2^l - 1)] , y <- [0..(2^l - 1)]
                , let xyh = addTF_haskell (inttf l x) (inttf l y)
                , let xyq = addTF_simulate (inttf l x) (inttf l y)
                , let flag = if xyh /= xyq then "  **MISMATCH**" else ""]
              ++
                ["",""]

-- | Give full table  of values for the TF multiplication ('o8_MUL') 
-- functions. 
multTF_table :: Int -> [String]
multTF_table l = [ "multTF table for l = " ++ (show l) ++ ":"
                , ""
                , "x   y   x*yH          x*yQ      "]
              ++
                [ (show x) ++ "   " ++ (show y) ++ "   "
                   ++ (show xyh) ++ "     " ++ (show xyq)
                   ++ flag
                | x <- [0..(2^l - 1)] , y <- [0..(2^l - 1)]
                , let xyh = multTF_haskell (inttf l x) (inttf l y)
                , let xyq = multTF_simulate (inttf l x) (inttf l y)
                , let flag = if xyh /= xyq then "  **MISMATCH**" else ""]
              ++
                ["",""]


-- | Give full table  of values for the 'pow17' functions. 
pow17_table :: Int -> [String]
pow17_table l = [ "pow17 table for l = " ++ (show l) ++ ":"
                      , ""
                      , "x  x17H        x17Q      "]
                    ++
                      [ (show x) ++ "   " ++ (show x_h) ++ "   " ++ (show x_q) ++ flag
                      | x <- [0..(2^l - 1)]
                      , let x_h = pow17_haskell (inttf l x) 
                      , let x_q = pow17_simulate (inttf l x)
                      , let flag = if x_h /= x_q then "  **MISMATCH**" else ""]
                    ++
                      ["",""]

-- | Give full table  of values for the 'mod3' functions. 
mod3_table :: Int -> [String]
mod3_table l = [ "mod3 table for l = " ++ (show l) ++ ":"
                      , ""
                      , "x  Haskell    o5_MOD3     o5_MOD3_alt"]
                    ++
                      [ (show x) ++ "   " ++ (show x_h) ++ "   "
                        ++ (show x_q) ++ flag
                      | x <- [0..(2^l - 1)]
                      , let x_h = mod3_haskell (inttf l x) 
                      , let x_q = mod3_simulate (inttf l x)
                      , let x_q' = mod3_alt_simulate (inttf l x)
                      , let flag = if x_h /= x_q then "  **MISMATCH**" else ""]
                    ++
                      ["",""]

-- | Give full table  of values for the oracle. 
oracle_table :: Int -> Int -> [String]
oracle_table n l = [ "oracle table for l = " ++ (show l) ++ ", n = " ++ (show n) ++ ":"
                      , ""
                      , "u    v    E_H   E_Q"]
                    ++
                      [ (showBits u) ++ "   " ++ (showBits v) ++ "   "
                        ++ (show e_h) ++ "   " ++ (show e_q) ++ flag
                      | uint <- [0..(2^n - 1)], let u = boollist_of_int_bh n uint
                      , vint <- [0..(2^n - 1)], let v = boollist_of_int_bh n vint
                      , let e_h = oracle_haskell l u v 
                      , let e_q = oracle_simulate l u v
                      , let flag = if e_h /= e_q then "  **MISMATCH**" else ""]
                    ++
                      ["",""]
  where
    showBits :: [Bool] -> String
    showBits [] = "[]"
    showBits bs = map (\b -> if b then '1' else '0') bs

-- | Give a full table of values for 'o1_ORACLE_aux'.
oracle_table_detailed :: Int -> Int -> [String]
oracle_table_detailed n l = [ "oracle_aux table for l = " ++ (show l) ++ ", n = " ++ (show n) ++ ":"
                      , ""
                      , "((u,v),(uint,vint,u17,v17,u3,v3),(uF,vF,uH,vH,t_uv,t_uHvH,t_u3v3))"]
                    ++
                      (concat 
                      [ [show_oracle_details od_h,show_oracle_details od_q]
                      | uint <- [0..(2^n - 1)], let u = boollist_of_int_bh n uint
                      , vint <- [0..(2^n - 1)], let v = boollist_of_int_bh n vint
                      , let od_h = oracle_aux_haskell l u v 
                      , let od_q = oracle_aux_simulate l u v
                      , let flag = if od_h /= od_q then "  **MISMATCH**" else ""
                      ])
                    ++
                      ["",""]
  where
    showBits :: [Bool] -> String
    showBits [] = "[]"
    showBits bs = map (\b -> if b then '1' else '0') bs


-- | Give full table  of values for the 'ConvertNode' functions. 
convertNode_table :: Int -> Int -> [String]
convertNode_table l n = [ "convertNode table for l = " ++ (show l) ++ ", n = " ++ (show n) ++ ":"
                      , ""
                      , "u     uint_H    uint_Q"]
                    ++
                      [ (showBits u) ++ "   " ++ (show u_h) ++ "   " ++ (show u_q) ++ flag
                      | uint <- [0..(2^n - 1)], let u = boollist_of_int_bh n uint
                      , let u_h = convertNode_haskell l u 
                      , let u_q = convertNode_simulate l u
                      , let flag = if u_h /= u_q then "  **MISMATCH**" else ""]
                    ++
                      ["",""]
  where
    showBits :: [Bool] -> String
    showBits [] = "[]"
    showBits bs = map (\b -> if b then '1' else '0') bs

-- | A compilation of the various tests above, to be called by 
-- 'Algorithms.TF.Main'.
arithmetic_tests :: Int -> IO ()
arithmetic_tests l = do
  mapM putStrLn $ increment_table l
  mapM putStrLn $ incrementTF_table l
  mapM putStrLn $ doubleTF_table l
  mapM putStrLn $ addTF_table l
  mapM putStrLn $ multTF_table l
  mapM putStrLn $ pow17_table l
  mapM putStrLn $ mod3_table l
  return ()

-- | A suite of tests for the oracle, to be called by 
-- 'Algorithms.TF.Main'.
oracle_tests :: Int -> Int -> IO ()
oracle_tests n l = do
  mapM_ putStrLn $ oracle_table n l
  mapM_ putStrLn $ oracle_table_detailed n l
  mapM_ putStrLn $ convertNode_table l n
