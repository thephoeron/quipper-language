-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper
import QuipperLib.Arith
import QuipperLib.QFTAdd
import QuipperLib.Simulation
import QuipperLib.Unboxing

import System.Environment

------ Functions for testing the QFTAdd circuit --------

-- | Output a preview of the qft_add_in_place circuit for quantum integers of
-- the given size
print_qft_add :: Int -> IO ()
print_qft_add m = print_generic PDF qft_add_in_place (qdint_shape m) (qdint_shape m)

-- | Simulate the running of the qft_add_in_place circuit for the given IntM inputs
run_qft_add :: IntM -> IntM -> IO (IntM,IntM)
run_qft_add = run_generic_io (undefined :: Double) (unbox qft_add_in_place)

-- | A wrapper around 'run_qft_add' so that it can be used with standard Integer
-- arguments.
test_add :: Integer -> Integer -> IO Integer
test_add a b = if (a < 0) || (b < 0) then error "test_add: negative argument" else
 do
  let m = 2 + ceiling (log (fromInteger (a+b)) / log 2) -- a slight cheat to work out how many qubits to use
  let a' = intm m a
  let b' = intm m b
  (_,ab) <- run_qft_add a' b'
  return (fromIntegral ab)

-- | A datatype for the possible command line arguments
data Args = Usage | One Int | Two Integer Integer 

-- | A function to parse the command line arguments
parseArgs :: [String] -> Args
parseArgs [s1] = case reads s1 of
  [(x1,_)] -> One x1
  _ -> Usage
parseArgs [s1,s2] = case (reads s1,reads s2) of
  ([(x1,_)],[(x2,_)]) -> Two  x1 x2
  _ -> Usage
parseArgs _ = Usage

-- | The main function calls either test_add or print_qft_add depending upon
-- command line arguments.
main ::  IO ()
main = do
  args <- getArgs
  case parseArgs args of
   Usage -> usage
   One x -> print_qft_add x
   Two x1 x2 -> do
     res <- test_add x1 x2
     putStrLn (show x1 ++ " + " ++ show x2 ++ " = " ++ show res)

usage :: IO ()
usage = do
  name <- getProgName
  putStrLn ("usage: " ++ name ++ " num1 <num2>") 
  putStrLn "  - one argument:"
  putStrLn "     preview the circuit for quantum integers of that length"
  putStrLn "  - two arguments:"
  putStrLn "     simulate the circuit for adding the two numbers"
  putStrLn "     (note that quantum simulation is not efficient)"
