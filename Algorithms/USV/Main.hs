-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- |
-- Author: Neil Julien Ross
-- 
-- An implementation of the Unique Shortest Vector (USV) 
-- algorithm. The input to the Unique Shortest Vector 
-- problem is an /n/×/n/ integer matrix /B/ with
-- the property that the lattice /L(B)/ spanned by /B/
-- contains a unique vector /u/ such that that any 
-- other non-parallel vector /v/ in the lattice is 
-- longer then /u/ by a factor of /n/[sup 3]. The
-- output is the vector /u/.
--
-- The algorithm proceeds in two steps: first it uses 
-- Regev’s method to reduce the USV to the Two
-- Point problem (TPP) and then to the Dihedral 
-- Coset problem (DCP), second it uses Kuperberg’s 
-- algorithm to solve the DCP. The first step 
-- transforms the input matrix into a set of coset 
-- states by partitioning the space into hypercubes 
-- containing at most two lattice points, and then 
-- collapsing the space onto one such cube. The second 
-- step uses a sieving method on the obtained set of 
-- coset states to extract the shortest vector.
--
-- These algorithms are described in:
--
-- * G. Kuperberg, \"A subexponential-time quantum
-- algorithm for the dihedral hidden subgroup problem.\"
-- /SIAM J. Comput./ 35(1):170-188,2005.
-- 
-- * O. Regev, \"Quantum computation and lattice problems.\"
-- In Danielle C. Martin, editor, 
-- /Proceedings of the 43rd IEEE Symposium on Foundations of Computer Science/, 
-- pp.  520-529, Nov. 16-19, Vancouver, BC, Canada, 2002. IEEE, IEEE
-- Press, Los Alamitos, CA.
--
-- The present implementation is based on a detailed algorithm 
-- specification that was provided to us by the IARPA QCS
-- program and written by Andrew J. Landahl.
--
-- Modules: 
--
-- * "Algorithms.USV.Main": Command line interface.
-- 
-- * "Algorithms.USV.Definitions": Some general-purpose
-- definitions.
-- 
-- * "Algorithms.USV.USV": The implementation of the 
-- main Unique Shortest Vector algorithm.
--
-- * "Algorithms.USV.Simulate": Functions for testing 
-- and debugging certain subroutines.

module Algorithms.USV.Main where

import Quipper

import QuipperLib.Arith
import QuipperLib.Decompose

import Algorithms.USV.Definitions
import Algorithms.USV.USV
import Algorithms.USV.Simulate

import Libraries.CommandLine
import Libraries.Sampling

import System.Console.GetOpt
import System.Environment    
import System.Exit
import System.IO
import System.Random
import Control.Monad
import Data.List
import Data.Char

-- ----------------------------------------------------------------------
-- * Command line interface

-- $ This module provides a command line interface for the Unique
-- Shortest Vector algorithm. This allows the user, for example, to
-- show different parts of the circuit, select a gate base,
-- select parameters such as /n/ and /b/, and select different output
-- formats.
-- 
-- [Example invocations:]
--
-- > ./usv
--
-- Default options: the 'sieving' algorithm with 
-- /n/=5 and ASCII output format. Because the 'sieving'
-- algorithm uses the 'dynamic_lift' function, the user 
-- will be prompted to provide values corresponding to 
-- a hypothetical measurement outcome (0 or 1) .
--
-- > ./usv -F -f gatecount
--
-- The gate count for 'f_quantum'. 
-- 
-- [Options and parameters:]
-- 
-- * /b/ is the lattice basis (Default value: a 5×5 
-- matrix with entries set to 1).
--
-- * /n/ is the dimension of the lattice 
-- (Default value: 5).
--
-- * /s/ is the seed for the random number generator
-- (Default value: 1).
--
-- [Restrictions:]
--
-- The 'sieving' algorithm uses the 'dynamic_lift' function.  
-- The only output format that currently supports such a 
-- functionality is ASCII. All algorithms that call 
-- 'sieving' must therefore be run with the default 
-- (ASCII) output format. These are: 'sieving', 'dCP', 'tPP',
-- 'algorithm_Q' and 'uSVP'.

-- ==============================================================

-- * Option processing

-- | An enumeration type for determining what the main function 
-- should do.
data WhatToShow = 
  F          -- ^Show 'f_quantum'. Depends on input /b/.
  | G        -- ^Show 'g_quantum'. Depends on input /b/.
  | H        -- ^Show 'h_quantum'. Depends on input /n/.
  | USVP     -- ^Run 'uSVP'. Depends on input /b/.
  | Q        -- ^Run 'algorithm_Q'. Depends on input /b/.
  | R        -- ^Show 'algorithm_R'. Depends on input /b/.
  | TPP      -- ^Run 'tPP'. Depends on input /n/.
  | Sieve    -- ^Run 'sieving'. Depends on input /n/.
  | DCP      -- ^Run 'dCP'. Depends on input /n/.
  | Test     -- ^Run Simulation test for 'h_quantum'. Depends on input /n/.
  deriving Show

-- | A data type to hold values set by command line options.
data Options = Options {
  s :: Int,                    -- ^Parameter /s/ (seed for random number generator).
  n :: Int,                    -- ^Parameter /n/ (lattice dimension).
  b :: [[Integer]],            -- ^Parameter /b/ (lattice basis).
  what :: WhatToShow,          -- ^What kind of thing to output.
  format :: Format,            -- ^The output format.
  gatebase :: GateBase         -- ^What kind of gates to decompose into.
} deriving Show

-- | The default options.
defaultOptions :: Options
defaultOptions = Options
  { s = 1,
    n = 5,
    b = (replicate 5 (replicate 5 1)),
    what = Sieve,
    format = ASCII,
    gatebase = Logical
  }

-- | The list of command line options, in the format required by 'getOpt'.
options :: [OptDescr (Options -> IO Options)]
options =
  [ 
-- Generic options
    Option ['h'] ["help"]      (NoArg help)                    "print usage info and exit",
    Option ['f'] ["format"]    (ReqArg format "<format>")      "output format for circuits (default: eps)",
    Option ['g'] ["gatebase"]  (ReqArg gatebase "<gatebase>")  "type of gates to decompose into (default: logical)",
-- Algorithm parameter 
    Option ['n'] ["n"]         (ReqArg nnn "<n>")              "parameter n (default: 5)",
    Option ['b'] ["b"]         (ReqArg bbb "<b>")              "parameter b (default: 5X5 with entries = 1)",
    Option ['s'] ["s"]         (ReqArg sss "<s>")              "Random number generator seed s (default: 1)",
-- Algorithm specific options
    Option ['F'] []            (NoArg (what F))                "output subroutine f (depends on b).",
    Option ['G'] []            (NoArg (what G))                "output subroutine g (depends on b).",
    Option ['H'] []            (NoArg (what H))                "output subroutine h (depends on n).",
    Option ['U'] []            (NoArg (what USVP))             "output algorithm 1 (depends on b).",
    Option ['Q'] []            (NoArg (what Q))                "output algorithm 2 (depends on b).",
    Option ['R'] []            (NoArg (what R))                "output algorithm 3 (depends on b).",
    Option ['T'] []            (NoArg (what TPP))              "output algorithm 4 (depends on n).",
    Option ['S'] []            (NoArg (what Sieve))            "output sieving subroutine (depends on n).",
    Option ['D'] []            (NoArg (what DCP))              "output algorithm 5 (depends on n).",
-- Testing options
    Option ['t'] []            (NoArg (what Test))             "test subroutine h (depends on n)."
  ]
    where
      help :: Options -> IO Options
      help o = do
        usage
        exitSuccess

      format :: String -> Options -> IO Options
      format str o = do
        case match_enum format_enum str of
          [(_, f)] -> return o { format = f }
          [] -> optfail ("Unknown format -- " ++ str ++ "\n")
          _ -> optfail ("Ambiguous format -- " ++ str ++ "\n")

      gatebase :: String -> Options -> IO Options
      gatebase str o = do
        case match_enum gatebase_enum str of
          [(_, f)] -> return o { gatebase = f }
          [] -> optfail ("Unknown gate base -- " ++ str ++ "\n")
          _ -> optfail ("Ambiguous gate base -- " ++ str ++ "\n")

      nnn :: String -> Options -> IO Options
      nnn string o =
        case parse_int string of 
          Just n | n >= 1 -> return o { n = n }
          _ -> optfail ("Invalid value for parameter n -- " ++ string ++ "\n")

      bbb :: String -> Options -> IO Options
      bbb string o =
        case parse_list_basis string of 
          Just b -> if (all is_zero_vector b) 
                        then optfail ("0 is an invalid value for parameter b " ++ "\n") 
                        else return o { b = b }
          _ -> optfail ("Invalid value for parameter b -- " ++ string ++ "\n")

      sss :: String -> Options -> IO Options
      sss string o =
        case parse_int string of 
          Just s -> return o { s = s }
          _ -> optfail ("Invalid value for parameter s -- " ++ string ++ "\n")

      what :: WhatToShow -> Options -> IO Options
      what w o = return o { what = w }

-- | Process /argv/-style command line options into an 'Options' structure.
dopts :: [String] -> IO Options
dopts argv =
  case getOpt Permute options argv of
    (o, [], []) -> (foldM (flip id) defaultOptions o)
    (_, _, []) -> optfail "Too many non-option arguments\n"
    (_, _, errs) -> optfail (concat errs)

-- | Print usage message to 'stdout'.
usage :: IO ()
usage = do
  putStr (usageInfo header options) 
  putStr (show_enum "format" format_enum)
  putStr (show_enum "gatebase" gatebase_enum)
    where header = "Usage: usv [OPTION...]"

-- | Parse a string to a list of integers, or return 'Nothing' on failure.
parse_list_basis :: String -> Maybe [[Integer]]      
parse_list_basis s = case reads s of
  [(ns, "")] -> Just ns
  _ -> Nothing

-- ==============================================================
-- * Main function

-- | The main function for the Unique Shortest Vector problem: read
-- options, then execute the appropriate task.
main :: IO()
main = do
  argv <- getArgs
  options <- dopts argv 
  case options of
  
    Options { what = what, format = format, gatebase = gatebase, n = n, b = b, s = s} ->
      case what of
        F -> print_generic format (decompose_generic gatebase (f_quantum b p m i0)) twopoint_from_b
        G -> print_generic format (decompose_generic gatebase (g_quantum (toInteger n) ws)) vector_from_b
        H -> print_generic format (decompose_generic gatebase h_quantum) vector_from_n
        USVP -> print_generic format (decompose_generic gatebase (uSVP b))
        Q -> print_generic format (decompose_generic gatebase (algorithm_Q b (l, m, i0, p) randomgen))
        R -> print_generic format (decompose_generic gatebase (algorithm_R b l m i0 p randomgen))
        TPP -> print_generic format (decompose_generic gatebase (tPP n)) (replicate (4*n^2+n) twopoint_from_n)
        Sieve -> print_generic format (decompose_generic gatebase (\l -> sieving n 2 (zip l [0..]))) (replicate (2^n-1) qubit)
        DCP -> print_generic format (decompose_generic gatebase (dCP n 0 0)) (replicate (8^n) cosetstate)
        Test -> h_test n

      where
        randomgen = mkStdGen s
        -- To reduce the number of inputs to be provided by the user, 
        -- inputs other than n and b are derived. 
        --
        -- Some inputs are therefore hardwired to arbitrary values.
        -- Moreover, some subroutines are parameterized by b while 
        -- others are parameterized by n. Subroutines H, TPP, Sieve, Test
        -- and DCP depend on n. The remaining subroutines depend on b.
        --
        -- Inputs derived from b:
        --
        n_from_b = length b
        l = ceiling $ norm $ head b
        p = find_prime ((n_from_b)^3)
        m = p-1                       -- In fact, m ranges from 1 to (p-1).
        i0 = 0                        -- In fact, i_0 ranges from 0 to (n-1).
        max_b = maximum (map maximum b)
        s = ceiling (logBase 2 (fromIntegral max_b)) + 5*n
        twopoint_from_b = (qubit, (replicate n_from_b (qdint_shape (4*n_from_b))))
        vector_from_b = (replicate n_from_b (qdint_shape s))
        --
        -- Inputs derived from n:
        --
        vector_from_n = (replicate n (qdint_shape (4*n))) 
        twopoint_from_n = (qubit, vector_from_n)
        cosetstate = (qubit, (qdint_shape n))
        ws = take n $ sample_random0 randomgen 1 
