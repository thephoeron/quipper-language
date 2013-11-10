-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleContexts #-}

-- ----------------------------------------------------------------------
-- | This tool reads a circuit from standard input, and then simulates
-- it by applying it to every possible basis vector. This is only
-- intended for debugging (of very small circuits), and is by no means
-- an industrial-strength simulator. Any measurements in the circuit
-- will be simulated probabilistically.

module Main where

import Quipper
import Quipper.Internal
import QuipperLib.Simulation
import QuipperLib.QuipperASCIIParser

import Libraries.Auxiliary (string_of_list)
import Libraries.CommandLine
import Libraries.Sampling
import Libraries.Synthesis.Random.FixedPrec
import Libraries.Synthesis.Ring
import Libraries.Synthesis.SymReal

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad
import Data.Number.FixedPrec
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.Random

-- ----------------------------------------------------------------------
-- * Command line options

-- | A data type to hold the command line options.
data Options = Options {
  prec :: Integer,       -- ^ Precision in decimal digits.
  addprec :: Int         -- ^ Additional precision to use internally.
} deriving Show

-- | The default options.
defaultOptions :: Options
defaultOptions = Options
  { prec = 30,
    addprec = 10
  }

-- | The list of command line options, in the format required by 'getOpt'.
options =
  [ Option ['h'] ["help"]    
      (NoArg help)                
      "print usage info and exit",
    Option ['d'] ["digits"]  
      (ReqArg opt_digits "<num>") 
      "precision in decimal digits (default: 30)",
    Option ['a'] ["addprec"]  
      (ReqArg opt_additional "<num>") 
      "additional digits to use internally (default: 10)"
  ]
    where
      opt_digits :: String -> Options -> IO Options
      opt_digits str o = 
        case parse_int str of
          Just d -> return o { prec = d }
          _ -> optfail ("Invalid value for option -d -- " ++ str ++ "\n")
          
      opt_additional :: String -> Options -> IO Options
      opt_additional str o = 
        case parse_int str of
          Just d -> return o { addprec = d }
          _ -> optfail ("Invalid value for option -a -- " ++ str ++ "\n")
          
      help :: Options -> IO Options
      help o = do
        usage
        exitSuccess

-- | Process /argv/-style command line options into an 'Options' structure.
dopts :: [String] -> IO Options
dopts argv =
  case getOpt Permute options argv of
    (o, [], []) -> (foldM (flip id) defaultOptions o)
    (_, _, []) -> optfail "Too many non-option arguments\n"
    (_, _, errs) -> optfail (concat errs)

-- | Print a usage message to 'stdout'.
usage :: IO ()
usage = do
  putStr (usageInfo header options)  
    where header = "Usage: Simulate [option...]"

-- ----------------------------------------------------------------------
-- * Payload functions

-- | Convert a boolean vector to ket notation.
show_ket :: [Bool] -> String
show_ket = string_of_list "|" "" ">" "|>" show_bit where
  show_bit False = "0"
  show_bit True = "1"

-- | A version of 'sim_amps' that works on 'FixedPrec' numbers and
-- uses /n/ digits of additional precision internally during the
-- simulation.
sim_amps_addprec :: (RandomGen g, Precision p, QData qa, QData qb, Ord (BType qb)) => g -> Int -> (qa -> Circ qb) -> Map (BType qa) (Cplx (FixedPrec p)) -> Map (BType qb) (Cplx (FixedPrec p))
sim_amps_addprec g addprec circ state =
  with_added_digits addprec f (dummy state) where
    dummy :: Map a (Cplx f) -> f
    dummy = undefined
    f arg = Map.map cast_cplx out_state where
      in_state = Map.map cast_cplx state
      out_state = sim_amps g circ in_state
      _ = dummy in_state `attypeof` arg
      attypeof :: a -> a -> a
      attypeof x y = x
      cast_cplx (Cplx a b) = Cplx (cast a) (cast b)

-- | Input a source of randomness, an added precision, a real number,
-- a circuit, and a basis vector. Simulate the circuit on the given
-- basis vector, and print out the result of the simulation in the
-- format
-- 
-- > |011> ->
-- >          |011> 0.7071067811
-- >          |010> -0.7071067811
-- 
-- The real number argument is a dummy argument; it serves to
-- determine the real number type (e.g., 'Double', 'FixedPrec' /e/) to
-- be used for the simulation. In this way, it is possible to simulate
-- up to arbitrary precision.
print_simulation_internal :: (RandomGen g, Precision e) => g -> Int -> FixedPrec e -> ([Qubit] -> Circ [Qubit]) -> [Bool] -> IO ()
print_simulation_internal g addprec r circ l = do
  putStrLn $ show_ket l ++ " ->" 
  foreach amps $ \(ket, amp) -> do
    when (amp /= 0) $ do
      putStrLn $ [' ' | x <- l] ++ "      " ++ show_ket ket ++ " " ++ show amp
  where
    state = Map.fromList [(l, Cplx (1 `attypeof` r) 0)]
    amps = Map.toList $ sim_amps_addprec g addprec circ state
    
    attypeof :: a -> a -> a
    attypeof x y = x

-- | Like 'print_simulation_internal', but instead of a dummy real number
-- argument, specify a number of decimal digits for the simulation.
print_simulation :: (RandomGen g) => g -> Integer -> Int -> ([Qubit] -> Circ [Qubit]) -> [Bool] -> IO ()
print_simulation g d addprec = dynamic_fixedprec d (print_simulation_internal g addprec) (undefined :: Double)

-- | Input a source of randomness, a precision (in decimal digits), a
-- quantum circuit and a shape argument. Simulate the circuit for
-- every possible basis vector of the given shape, and print out the
-- result of the simulations in the format
-- 
-- > |011> ->
-- >          |011> 0.7071067811
-- >          |010> -0.7071067811
simulate_all :: (RandomGen g) => g -> Integer -> Int -> ([Qubit] -> Circ [Qubit]) -> [a] -> IO ()
simulate_all g d addprec circ ins = do
  let ls = sample_all0 [ True | x <- ins ]
  foreach ls $ \l -> do
    print_simulation g d addprec circ l

-- ----------------------------------------------------------------------
-- * The main function

-- | Main function: read from 'stdin', then simulate.
main :: IO ()
main = do
  -- Process command line options
  argv <- getArgs
  options <- dopts argv
  let d = prec options
  let a = addprec options
  
  -- Read circuit
  (ins, circuit) <- parse_from_stdin
  let circ :: [Qubit] -> Circ [Qubit]
      circ qs = do
        let es = [ Endpoint_Qubit q | q <- qs ]
        es <- circuit es
        let qs = [ q | Endpoint_Qubit q <- es ]
        return qs
  
  -- Simulate circuit
  g <- newStdGen
  simulate_all g d a circ ins
