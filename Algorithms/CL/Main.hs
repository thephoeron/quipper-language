-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- |
-- Authors: Keith Kim, Peter LeFanu Lumsdaine, Alexandr Virodov
--  
-- An implementation of Hallgren’s Class Number algorithm.  This algorithm computes various invariants of 
-- a real quadratic number field /K/ = ℚ(√Δ), notably the class number and the structure of the class group /CL/(/K/).
-- The field /K/ is specified by its discriminant /Δ/, the main input to the algorithm.
--
-- The algorithm may also be adapted to other problems from algebraic number theory, including Pell's equation (finding integer solutions to /x/ [sup 2] − /dy/ [sup 2] = 1, for non-square /d/) and the principal ideal problem (determining whether an ideal of a number field is principal, and finding a generator if so).
--
-- The present implementation falls into five stages, which we will refer to throughout the documentation:
-- 
-- 1. Approximate the regulator of /K/, to low precision, using a version of the the (quantum) HSP algorithm.
-- 
-- 2. Classically, refine the approximation from part 1 to higher precision.
-- 
-- 3. Classically compute a small generating set for the class group, using the value of the regulator from part 2.
-- 
-- 4. Compute relations for these generators, again using a version of the HSP algorithm.
--
-- 5. Classically compute from these the structure of the class group, and hence the class number. 
-- 
-- Further details are given in the documentation of individual modules.
--
-- The algorithm and its mathematical background are described in:
-- 
-- * Sean Hallgren, \"Polynomial-time quantum algorithms for Pell’s equation and the principal ideal problem\",
-- in /STOC ’02: Proceedings of the thirty-fourth annual ACM symposium on Theory of computing/, pp. 653–658, 2002.
-- (Also published in J. ACM, 54(1), 2007.)
-- 
-- * Richard Jozsa, \"Quantum computation in algebraic number theory: Hallgren’s efficient quantum
-- algorithm for solving Pell’s equation.\" Annals of Physics, 306:241–279, February 2003; 
-- also available as <http://arxiv.org/abs/quant-ph/0302134>.  All references in documentation
-- refer to arXiv version.
-- 
-- * Daniel Haase and Helmut Maier, \"Quantum algorithms for number fields.\" Fortschr. Phys.,
-- 54(8):866–881, 2006.
--
-- The present implementation is based on a detailed algorithm specification that was provided to us by the IARPA QCS
-- program and written by Brian J. Matt, Durward McDonell, and David Zaret.
--
-- Modules:
-- 
-- * "Algorithms.CL.Main": Command line interface.
-- 
-- * "Algorithms.CL.Auxiliary": General-purpose functions required in Hallgren’s algorithm.
-- 
-- * "Algorithms.CL.Types": Specialized classical and quantum datatypes used in Hallgren’s algorithm, and basic functions on these types.
-- 
-- * "Algorithms.CL.CL": The high-level structure of Hallgren’s algorithm.
-- 
-- * "Algorithms.CL.RegulatorClassical": A classical implementation of the functions and operations of stages 1–4.
-- 
-- * "Algorithms.CL.RegulatorQuantum": A quantum implementation of the functions required for stages 1 and 4
-- 
-- * "Algorithms.CL.SmithReduction": Matrices, and reduction to Smith Normal Form, for Stage 5. 
-- 
-- * "Algorithms.CL.Test": Functions to test components of the present implementation, using classical computation.

module Algorithms.CL.Main where

import Quipper
import Libraries.CommandLine
import QuipperLib.Arith
import QuipperLib.FPReal
import QuipperLib.Decompose
import QuipperLib.Unboxing

import Algorithms.CL.Auxiliary
import Algorithms.CL.Types
import Algorithms.CL.RegulatorClassical
import Algorithms.CL.RegulatorQuantum
import Algorithms.CL.CL
import Algorithms.CL.Test

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.Random
import Control.Monad
import Data.Bits
import Data.Maybe
import Data.List
import Data.Char

-- ----------------------------------------------------------------------
-- * Command line interface

-- $ This module provides a command line interface for Hallgren’s Class
-- Number algorithm. This allows the user, for example, to print or simulate 
-- the circuits used in quantum portions of the algorithm, or to run 
-- small instances of the algorithm in a classical implementation.
--
-- Sample invocations:
--
-- >>> ./cl -R
--
-- Compute, classically, the regulator of ℚ[√Δ], with Δ = 28 (default value).
--
-- >>> ./cl -P -d 17
-- 
-- Compute, classically, the fundamental solution of Pell’s equation 
-- /x/[super 2] − /d//y/[super 2] = 1 
-- with /d/ = /Δ/ = 17.
--
-- >>> ./cl -S fn -d 5 -f eps > cl_fn_d5.eps 
--
-- Produce an .eps file of the quantum circuit implementing the 
-- pseudo-periodic function /f/[sub /N/] used for regulator estimation,
-- for Δ = 5
--
-- >>> ./cl -S starprod -d 60 -f gatecount
--
-- Give gate-count for the quantum circuit implementing the star-product
-- on ideals, for Δ = 17
--
-- >>> ./cl --help
--
-- Print detailed usage information.

-- ----------------------------------------------------------------------
-- * Option processing
-- 
-- | An enumeration type for determining what the main function should do.
data WhatToShow =
    Stage1          -- ^Show the circuit for stage 1 of the algorithm
  | Stage4          -- ^Show the circuit for stage 4 of the algorithm
  | Sub             -- ^Show the circuit for a specific quantum subroutine
  | Regulator       -- ^Classically, find the regulator
  | FundamentalUnit -- ^Classically, find the fundamental unit
  | PellSolution    -- ^Classically, find the fundamental solution of Pell’s equation
  deriving Show

-- | An enumeration type for selecting a subroutine.
data Subroutine = 
    Rho
  | RhoInv
  | Normalize
  | DotProd
  | StarProd
  | FN
  deriving (Show, Enum, Bounded)

-- | An enumeration of available subroutines.  (Compare 'format_enum', 'gatebase_enum'.)
subroutine_enum :: [(String, Subroutine)]
subroutine_enum = map (\x -> (map toLower (show x),x)) [minBound..maxBound]

-- | A data type to hold values set by command line options.
data Options = Options {
  -- Main “what to do” type options:
  what     :: WhatToShow,    -- ^What kind of thing to output.
  format   :: Format,        -- ^The output format.
  gatebase :: GateBase,      -- ^What kind of gates to decompose into.
  sub      :: Subroutine,    -- ^Which subroutine to output (if @'what' == 'Sub'@).

  -- Master problem parameter
  cl_delta :: CLIntP,        -- ^The discriminant Δ, specifying the problem.

  -- Inputs for stage 1 of the algorithm
  cl_i     :: Int,           -- ^i, log_2 of the estimated bound 2^i for the weak period S.

  -- Inputs for stage 4 of the algorithm
  cl_r     :: CLReal,        -- ^ The (good) approximation R of the period.
  cl_q     :: CLIntP,        -- ^The parameter q for stage 4 of the algorithm.
  cl_k     :: CLIntP,        -- ^The parameter k for stage 4 of the algorithm.
  cl_n     :: CLIntP,        -- ^The parameter n for stage 4 of the algorithm.
  cl_m     :: CLIntP,        -- ^The parameter m for stage 4 of the algorithm.

  cl_generators :: [IdealRed], -- ^A generating set for /CL/(/K/).

  -- Misc options
  cl_seed  :: Int           -- ^The seed for the random generator (0 for seed from time)
} deriving (Show)

-- | The default options.
default_options :: Options
default_options = Options {
  what         = Stage1,
  format       = ASCII,
  gatebase     = Logical,
  sub          = FN,

  cl_delta     = 28,

  cl_i         = 1,

  cl_r         = 12.345,
  cl_q         = 4,
  cl_k         = 3,
  cl_n         = 3,
  cl_m         = 5,

  cl_generators = [],

  cl_seed      = 1
}

-- | Show the default value of an option.
show_default :: (Show a) => (Options -> a) -> String
show_default func = show (func default_options)

-- | The list of command line options, in the format required by 'getOpt'.
options :: [OptDescr (Options -> IO Options)]
options = [
-- Generic options:
  Option ['h'] ["help"]      (NoArg  help)                       $ "print usage info and exit",
  Option ['f'] ["format"]    (ReqArg read_format "<format>")     $ "output format for circuits        (default: " ++ show_default format   ++ ")",
  Option ['g'] ["gatebase"]  (ReqArg read_gatebase "<gatebase>") $ "gates to decompose into           (default: " ++ show_default gatebase ++ ")",

-- Select what to do:
  Option ['1'] []            (NoArg (what Stage1))                $ "output the circuit for stage 1 of the algorithm (default)",
  Option ['4'] []            (NoArg (what Stage4))                $ "output the circuit for stage 4 of the algorithm",
  Option ['S'] ["sub"]       (ReqArg read_subroutine "<subroutine>")   $ "output the circuit for a specific subroutine",
  Option ['R'] ["regulator"] (NoArg (what Regulator))            $ "classically, find the regulator, given Δ",
  Option ['F'] []            (NoArg (what FundamentalUnit))      $ "classically, find the fundamental unit, given Δ",
  Option ['P'] []            (NoArg (what PellSolution))         $ "classically, find the fundamental solution of Pell’s equation, given Δ",

-- Input parameters
  Option ['d'] ["delta"]     (ReqArg read_delta "<N>")           $ "discriminant Δ (a.k.a. D)                 (default: " ++ show_default cl_delta ++ ")",

  Option ['s'] ["ss"]        (ReqArg read_s     "<N>")           $ "estimated bound on period S, for stage 1 (default: " ++ show (2^(cl_i default_options))     ++ ")",
  Option ['i'] []            (ReqArg read_i     "<N>")           $ "estimated bound on log_2 S, for stage 1 (default: " ++ show (cl_i default_options)     ++ ")",

  Option ['r'] ["rr"]        (ReqArg read_r     "<N>")           $ "approximate regulator R, for stage 4  (default: " ++ show_default cl_r     ++ ")",
  Option ['q'] []            (ReqArg read_q     "<N>")           $ "The parameter q, for stage 4        (default: " ++ show_default cl_q     ++ ")",
  Option ['k'] []            (ReqArg read_k     "<N>")           $ "The parameter k, for stage 4        (default: " ++ show_default cl_k     ++ ")",
  Option ['n'] []            (ReqArg read_n     "<N>")           $ "The parameter n, for stage 4        (default: " ++ show_default cl_n     ++ ")",
  Option ['m'] []            (ReqArg read_m     "<N>")           $ "The parameter m, for stage 4        (default: " ++ show_default cl_m     ++ ")",

-- Miscellaneous options
  Option []    ["seed"]      (ReqArg read_seed  "<N>")           $ "Random seed (0 for seed from time)(default: " ++ show_default cl_seed  ++ ")"
  ]
    where
      what :: WhatToShow -> Options -> IO Options
      what w o = return o { what = w }

      read_format :: String -> Options -> IO Options
      read_format str o = do
        case match_enum format_enum str of
          [(_, f)] -> return o { format = f }
          [] -> optfail ("Unknown format -- " ++ str ++ "\n")
          _  -> optfail ("Ambiguous format -- " ++ str ++ "\n")

      read_gatebase :: String -> Options -> IO Options
      read_gatebase str o = do
        case match_enum gatebase_enum str of
          [(_, f)] -> return o { gatebase = f }
          [] -> optfail ("Unknown gate base -- " ++ str ++ "\n")
          _  -> optfail ("Ambiguous gate base -- " ++ str ++ "\n")

      read_subroutine :: String -> Options -> IO Options
      read_subroutine str o = do
        case match_enum subroutine_enum str of
          [(_, f)] -> return o { sub = f, what = Sub }
          [] -> optfail ("Unknown subroutine -- " ++ str ++ "\n")
          _  -> optfail ("Ambiguous subroutine -- " ++ str ++ "\n")

      read_delta = read_arg parse_int    (>0) (\n o -> o { cl_delta = fromIntegral n }) "Invalid Δ"
      read_seed  = read_arg parse_int    (>=0) (\n o -> o { cl_seed  = fromIntegral n }) "Invalid seed"
      read_i     = read_arg parse_int    (>=0) (\n o -> o { cl_i     = fromIntegral n }) "Invalid i"
      read_s     = read_arg parse_int    (>0) (\n o -> o { cl_i     = ceiling $ logBase 2 $ fromIntegral n }) "Invalid s"
      read_r     = read_arg parse_double (>0) (\n o -> o { cl_r     = fromRational $ toRational n }) "Invalid r"
      read_q     = read_arg parse_int    (>0) (\n o -> o { cl_q     = fromIntegral n }) "Invalid q"
      read_k     = read_arg parse_int    (>0) (\n o -> o { cl_k     = fromIntegral n }) "Invalid k"
      read_n     = read_arg parse_int    (>0) (\n o -> o { cl_n     = fromIntegral n }) "Invalid n"
      read_m     = read_arg parse_int    (>0) (\n o -> o { cl_m     = fromIntegral n }) "Invalid m"

      read_arg :: (String -> Maybe a) -> (a -> Bool) -> (a -> Options -> Options) -> String -> String -> Options -> IO Options
      read_arg parse cond func err string o =
        case parse string of
          Just n | cond n -> return $ func n o
          _ -> optfail (err ++ " -- " ++ string ++ "\n")

      help :: Options -> IO Options
      help o = do
        usage
        exitSuccess

-- | Process /argv/-style command line options into an 'Options' structure.
dopts :: [String] -> IO Options
dopts argv =
  case getOpt Permute options argv of
    (o, [], []) -> (foldM (flip id) default_options o)
    (_, _, []) -> optfail "Too many non-option arguments\n"
    (_, _, errs) -> optfail (concat errs)

-- | Print usage message to 'stdout'.
usage :: IO ()
usage = do
  putStr (usageInfo header options)
  putStr (show_enum "format" format_enum)
  putStr (show_enum "gatebase" gatebase_enum)
  putStr (show_enum "subroutine" subroutine_enum)
    where header = "Usage: cl [OPTION...]"

-- ----------------------------------------------------------------------
-- * The CL circuit generation main function

-- | Main function: read options, then execute the appropriate task.
main :: IO()
main = do
  -- Read options.
  argv <- getArgs
  options <- dopts argv

  let bigD = cl_delta options
  assertM (is_valid_bigD bigD) $
    "Δ = " ++ (show $ cl_delta options) ++ " not valid discriminant"
  let d = d_of_bigD bigD

  case what options of
    Stage1 -> main_stage1 options
    Stage4 -> main_stage4 options
    Sub -> main_sub options
    Regulator -> do
      putStrLn $ "Regulator (by classical period-finding):"
      putStrLn $ "Δ = " ++ show bigD
      putStrLn $ "d = " ++ show d
      putStrLn $ "R = " ++ show (regulator bigD)
    FundamentalUnit -> do
      putStrLn $ "Fundamental unit (by classical period-finding):"
      putStrLn $ "Δ = " ++ show bigD
      putStrLn $ "d = " ++ show d
      putStrLn $ "ε_0 = " ++ pretty_show_AlgNum (fundamental_unit bigD)
    PellSolution -> do
      putStrLn $ "Fundamental solution of Pell’s equation x^2 − d y^2 = 1 (by classical period-finding):"
      let (x,y) = fundamental_solution d
      putStrLn $ "Δ = " ++ show bigD
      putStrLn $ "d = " ++ show d
      putStrLn $ "x = " ++ show x
      putStrLn $ "y = " ++ show y

-- | Main function for outputting the circuit for stage 1 of Hallgren’s algorithm.
main_stage1 :: Options -> IO()
main_stage1 options = do

    -- Generate the main circuit.
    let bigD    = cl_delta options
    assertM (is_valid_bigD bigD) $
      "Δ = " ++ (show $ cl_delta options) ++ " not valid discriminant"
    let i       = cl_i     options
        ss_bound = 2^i
        q       = 2 + 2 * i   -- So 2^q = 4 * S_bound^2 is the first power of 2 above S_bound  
        t       = 2 * (ceiling (logBase 2 (sqrt $ fromIntegral bigD))) + i

    putStrLn $ "Generating circuit for stage 1 with args: "
    putStrLn $ show options
    putStrLn $ ""
    putStrLn $ "Computed values: "
    putStrLn $ "Δ: " ++ show bigD
    putStrLn $ "i: " ++ show i
    putStrLn $ "S_bound: " ++ show ss_bound
    putStrLn $ "q: " ++ show q
    putStrLn $ "t: " ++ show t

    -- rand <- getStdRandom (random)
    let rand    = 0    -- Fix the random generator to get consistent circuits
    let circuit = approximate_regulator_circuit bigD i rand

    -- Print it.
    print_simple (format options) (decompose_generic (gatebase options) circuit)


-- | Main function for outputting the circuit for stage 4 of Hallgren’s algorithm.
main_stage4 :: Options -> IO()
main_stage4 options = do
    putStrLn $ "Generating circuit for stage 4 with args: " ++ show options


-- | Main function for outputting the circuits for specific subroutines.
main_sub :: Options -> IO()
main_sub options =
  let fmt = format options
      gtb = gatebase options
      bigD = cl_delta options
  in case sub options of
    Rho -> do
      print_generic fmt (unbox q_rho_d) (sample_IdDistQ bigD)
    RhoInv -> do
      print_generic fmt (unbox q_rho_inv_d) (sample_IdDistQ bigD)
    Normalize -> do
      print_generic fmt (unbox q_normalize) (sample_IdDistQ bigD)
    DotProd -> do
      print_generic fmt (unbox q_dot_prod) iirq iirq
      where iirq = sample_IdealRedQ bigD
    StarProd -> do
      print_generic fmt (unbox q_star_prod) iirdq iirdq
      where iirdq = sample_IdRedDistQ bigD
    FN -> do
      print_generic fmt (unbox $ \qi -> q_fN bigD n 0 qi j) iq
      where
        i = cl_i options
        q = 2 + 2 * i -- as used in Part 1
        n = n_of_bigD bigD
        iq = qshape (intm q 0)
        j = (intm (q + 4) 0)
