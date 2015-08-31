-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# OPTIONS -O0 #-}
{-# OPTIONS -fcontext-stack=50 #-}

-- |
-- Authors: Peter LeFanu Lumsdaine, Neil Julien Ross
--
-- An implementation of the Triangle Finding Algorithm. The
-- Triangle Finding Problem is given by an undirected dense
-- simple graph /G/ containing exactly one triangle ∆. The
-- graph is given by an oracle function /f/ , such that, for 
-- any two nodes /v/, /w/ of /G/, /f/(/v/,/w/)=1 if (/v/,/w/) 
-- is an edge of /G/ and /f/(/v/,/w/)=0 otherwise. To solve 
-- such an instance of the problem is to find the set of 
-- vertices {/e/[sub 1] , /e/[sub 2] , /e/[sub 3]} forming 
-- ∆ by querying /f/.
--
-- The algorithm works by performing a Grover-based quantum 
-- walk on a larger graph /H/, called the Hamming graph
-- associated to /G/. It is designed to find ∆ with high
-- probability. The algorithm is parametric on an oracle
-- defining the graph /G/. In our implementation, the 
-- oracle is a changeable part, but we have also 
-- implemented a particular predefined oracle. 
--
-- The algorithm is described in:
--
-- * A. Childs and R. Kothari. \"Quantum query complexity of
-- minor-closed graph properties.\" In 
-- /Proceedings of the 28th Symposium on Theoretical Aspects of Computer Science/, 
-- pages 661–672, 2011.
--
-- * F. Magniez, M. Santha, and M. Szegedy. \"Quantum 
-- algorithms for the triangle problem.\" In 
-- /Proceedings of the 16th Annual ACM-SIAM Symposium on Discrete Algorithms/, 
-- pages 1109–1117, 2005.
--
-- The present implementation is based on detailed 
-- algorithm and oracle specifications that were provided to 
-- us by the IARPA QCS program and written by Richard 
-- Wisniewski.
--
-- Modules:
--
-- * "Algorithms.TF.Main": Command line interface.
--
-- * "Algorithms.TF.Definitions": Some general purpose
-- definitions.
--
-- * "Algorithms.TF.QWTFP": The implementation of the main
-- Triangle Finding algorithm.
--
-- * "Algorithms.TF.Oracle": The implementation of the 
-- oracle for the Triangle Finding algorithm.
--
-- * "Algorithms.TF.Alternatives": Some alternative 
-- implementations of some of the subroutines.
--
-- * "Algorithms.TF.Simulate": Functions for simulating,
-- testing, and debugging oracles.

module Algorithms.TF.Main where

import Quipper

import QuipperLib.Arith
import QuipperLib.Decompose

import Algorithms.TF.Definitions
import Algorithms.TF.Oracle
import Algorithms.TF.QWTFP
import Algorithms.TF.Simulate
import Algorithms.TF.Alternatives

import Libraries.CommandLine

import System.Console.GetOpt
import System.Environment    
import System.Exit
import System.IO
import Control.Monad
import Data.List
import Data.Char
import qualified Data.IntMap as IntMap

----------------------------------------------------------------------
-- * Documentation

-- $ This module provides a command line interface for the
-- Triangle Finding Algorithm. This allows the user, for
-- example, to plug in different oracles, show different 
-- parts of the circuit, select a gate base, simulate, 
-- and select various parameters.
--
-- * Example invocations:
--
-- @./tf@
--
-- Default options: the full 'a1_QWTFP' circuit, with 
-- (l,n,r) = (4,3,2), and a black-box oracle.
--
-- @./tf --oracle -o "Orthodox" -l 3 -n 2 -r 2@
--
-- A manageable size to inspect the orthodox oracle.
--
-- @./tf -s mult -l 4@
--
-- The multiplier, for 4-bit integers mod 15.
--
-- @./tf --help@
--
-- Print detailed usage info (accepted options, etc.).
--
-- * Parameters:
-- 
-- /l/: the length of integers used in the oracle.  
-- (Default value: 4.)
--
-- /n/: the size of nodes in the graph.  
-- (Default value: 3.)
--
-- /r/: log[sub 2] of the tuple size of the Hamming graph.  
-- (Default value: 2.)

--
-- * Option processing
--
-- | An enumeration type for determining what the main function should do.
data WhatToShow = 
  Circuit      -- ^Show the whole circuit.
  | Oracle     -- ^Show only the oracle.
  | Sub        -- ^Show a specific subroutine.
  | Arith      -- ^Run simulation tests of the arithmetic subroutines. 
  | OTest      -- ^Run simulation tests of the oracle. 
  deriving Show

-- | An enumeration type for selecting an oracle.
data OracleSelect =
  Orthodox     -- ^The default oracle.
  | Blackbox   -- ^A blackbox oracle.
  deriving Show

-- | A datatype for selecting a qRAM implementation.
data QRamSelect =
  Standard_QRam         -- ^ The default qRAM.
  | Alt_QRam       -- ^ A slightly more efficient implementation.
  deriving Show

-- | An enumeration type for selecting a subroutine.
data Subroutine = 
  A2            -- ^Algorithm 2: Zero.
  | A3          -- ^Algorithm 3: Initialize.
  | A4          -- ^Algorithm 4: Hadamard.
  | A5          -- ^Algorithm 5: Setup.
  | A6          -- ^Algorithm 6: QWSH.
  | A7          -- ^Algorithm 7: Diffuse.
  | A8          -- ^Algorithm 8: FetchT.
  | A9          -- ^Algorithm 9: StoreT.
  | A10         -- ^Algorithm 10: FetchStoreT.
  | A11         -- ^Algorithm 11: FetchE.
  | A12         -- ^Algorithm 12: FetchStoreE.
  | A13         -- ^Algorithm 13: Update.
  | A14         -- ^Algorithm 14: SWAP.
  | A15         -- ^Algorithm 15: TestTriangleEdges (inner quantum walk).
  | A16         -- ^Algorithm 16: TriangleTestT.
  | A17         -- ^Algorithm 17: TriangleTestTw.
  | A18         -- ^Algorithm 18: TriangleEdgeSearch.
  | A19         -- ^Algorithm 19: GCQWalk.
  | A20         -- ^Algorithm 20: GCQWStep.
  | O2          -- ^Algorithm O2: ConvertNODE.
  | O3          -- ^Algorithm O3: TestEqual.
  | O4          -- ^Algorithm O4: Pow17.
  | O5          -- ^Algorithm O5: Mod3.
  | O6          -- ^Algorithm O6: Sub.
  | O7          -- ^Algorithm O7: Add.
  | O8          -- ^Algorithm O8: Mul.
  deriving Show

-- | A data type to hold values set by command line options.
data Options = Options {
  what :: WhatToShow,      -- ^What kind of thing to output.
  s :: Subroutine,         -- ^What specific subroutine to output. 
  format :: Format,        -- ^The output format.
  gatebase :: GateBase,    -- ^What kind of gates to decompose into.
  oracle :: OracleSelect,  -- ^Which kind of oracle to use.
  qram :: QRamSelect,      -- ^Which qram implementation to use.
  l :: Int,                -- ^Parameter 'l'.
  n :: Int,                -- ^Parameter 'n'.
  r :: Int                 -- ^Parameter 'r'.
} deriving Show


-- | The default options.
defaultOptions :: Options
defaultOptions = Options
  { what = Circuit,
    s = O7,
    format = Preview,
    gatebase = Logical,
    oracle = Blackbox,
    qram = Standard_QRam,
    l = 4,
    n = 3,
    r = 2
  }


-- | The list of command line options, in the format required by 'getOpt'.
options :: [OptDescr (Options -> IO Options)]
options =
  [ 
-- Generic options
    Option ['h'] ["help"]       (NoArg help)                       "print usage info and exit",
    Option ['f'] ["format"]     (ReqArg format "<format>")         "output format for circuits (default: preview)",
    Option ['g'] ["gatebase"]   (ReqArg gatebase "<gatebase>")     "type of gates to decompose into (default: logical)",
-- Triangle finding parameters
    Option ['l'] ["l"]          (ReqArg lll "<l>")                 "parameter l (default: 4)",
    Option ['n'] ["n"]          (ReqArg nnn "<n>")                 "parameter n (default: 3)",
    Option ['r'] ["r"]          (ReqArg rrr "<r>")                 "parameter r (default: 2)",
-- Main circuits
    Option ['C'] ["QWTFP"]      (NoArg (what Circuit))             "output the whole circuit (default)",
    Option ['O'] ["oracle"]     (NoArg (what Oracle))              "output only the oracle",
-- Subroutine option
    Option ['s'] ["subroutine"] (ReqArg sub "<subroutine>")        "output the chosen subroutine (default: adder)",
-- QRAM option
    Option ['Q'] []             (NoArg (qram Alt_QRam))            "use alternative qRAM implementation",
-- Oracle option
    Option ['o'] []             (ReqArg oracle "<oracle>")         "select oracle to use (default: blackbox)",
-- Testing options
    Option ['A'] ["arith"]      (NoArg (what Arith))               "test/simulate the arithmetic routines",
    Option ['T'] ["oracletest"] (NoArg (what OTest))               "test/simulate the oracle"
  ]
    where
      what :: WhatToShow -> Options -> IO Options
      what w o = return o { what = w }

      sub :: String -> Options -> IO Options
      sub str o = do
        case match_enum subroutine_enum str of
          [(_, f)] -> return o { what = Sub, s = f }
          [] -> optfail ("Unknown subroutine -- " ++ str ++ "\n")
          _ -> optfail ("Ambiguous subroutine -- " ++ str ++ "\n")

      qram :: QRamSelect -> Options -> IO Options
      qram q o = return o { qram = q }
      
      lll :: String -> Options -> IO Options
      lll string o = 
        case parse_int string of
          Just l | l >= 1 -> return o { l = l }
          _ -> optfail ("Invalid value for parameter l -- " ++ string ++ "\n")
          
      nnn :: String -> Options -> IO Options
      nnn string o =
        case parse_int string of 
          Just n | n >= 1 -> return o { n = n }
          _ -> optfail ("Invalid value for parameter n -- " ++ string ++ "\n")

      rrr :: String -> Options -> IO Options
      rrr string o =
        case parse_int string of 
          Just r | r >= 1 -> return o { r = r }
          _ -> optfail ("Invalid value for parameter r -- " ++ string ++ "\n")

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

      oracle :: String -> Options -> IO Options
      oracle str o = do
        case match_enum oracle_enum str of
          [(_, f)] -> return o { oracle = f }
          [] -> optfail ("Unknown oracle -- " ++ str ++ "\n")
          _ -> optfail ("Ambiguous oracle -- " ++ str ++ "\n")

      help :: Options -> IO Options
      help o = do
        usage
        exitSuccess
      
-- | An enumeration of available oracles and their names.
oracle_enum :: [(String, OracleSelect)]
oracle_enum = [
  ("orthodox", Orthodox),
  ("blackbox", Blackbox)
  ]

-- | An enumeration of available subroutines and their names.
subroutine_enum :: [(String, Subroutine)]
subroutine_enum = [
  ("zero", A2),
  ("initialize", A3),
  ("hadamard", A4),
  ("setup", A5),
  ("qwsh", A6),
  ("diffuse", A7),
  ("fetcht", A8),
  ("storet", A9),
  ("fetchstoret", A10),
  ("fetche", A11),
  ("fetchstoree", A12),
  ("update", A13),
  ("swap", A14),
  ("a15", A15),
  ("a16", A16),
  ("a17", A17),
  ("a18", A18),
  ("gcqwalk", A19),
  ("gcqwstep", A20),
  ("convertnode", O2),
  ("testequal", O3),
  ("pow17", O4),
  ("mod3", O5),
  ("sub", O6),
  ("add", O7),
  ("mult", O8)
  ]

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
  putStr (show_enum "oracle" oracle_enum)
  putStr (show_enum "subroutine" subroutine_enum)
    where header = "Usage: tf [OPTION...]"

-- ----------------------------------------------------------------------
-- * The Triangle Finding Algorithm main function

-- | Main function: read options, then execute the appropriate task.
main :: IO()
main = do
  argv <- getArgs
  options <- dopts argv 
  let spec = spec_of_options options
  let p = ceiling (logBase 2 (fromIntegral (2^9 `choose` 3))) 
  case options of

    Options { oracle = oracle, what = what, format = format, gatebase = gatebase, n = n, r = r, l = l, s = s} ->

      case what of
        Circuit -> print_generic format $ decompose_generic gatebase $ a1_QWTFP spec 
        Oracle ->  print_generic format (decompose_generic gatebase $ proj3 spec) node_shape node_shape qubit
        Arith -> arithmetic_tests l
        OTest -> oracle_tests n l
        Sub -> case s of
          A2 -> print_generic format (decompose_generic gatebase $ a2_ZERO (replicate n False))
          A3 -> print_generic format (decompose_generic gatebase $ a3_INITIALIZE (replicate n False))
          A4 -> print_generic format (decompose_generic gatebase $ a4_HADAMARD) (replicate n qubit)
          A5 -> print_generic format (decompose_generic gatebase $ a5_SETUP spec) tt_shape
          A6 -> print_generic format (decompose_generic gatebase $ a6_QWSH spec)
                      tt_shape (qdint_shape r) node_shape ee_shape
          A7 -> print_generic format (decompose_generic gatebase $ a7_DIFFUSE) node_shape
          A8 -> print_generic format (decompose_generic gatebase $ a8_FetchT)
                      (qdint_shape r) tt_shape node_shape
          A9-> print_generic format (decompose_generic gatebase $ a9_StoreT)
                      (qdint_shape r) tt_shape node_shape
          A10-> print_generic format (decompose_generic gatebase $ a10_FetchStoreT)
                      (qdint_shape r) tt_shape node_shape
          A11-> print_generic format (decompose_generic gatebase $ a11_FetchE)
                      (qdint_shape r) ee_shape eed_shape 
          A12-> print_generic format (decompose_generic gatebase $ a12_FetchStoreE)
                      (qdint_shape r) ee_shape eed_shape 
          A13-> print_generic format (decompose_generic gatebase $ a13_UPDATE spec)
                      tt_shape node_shape eed_shape 
          A14-> print_generic format (decompose_generic gatebase $ a14_SWAP)
                      node_shape node_shape
          A15 -> print_generic format (decompose_generic gatebase $ a15_TestTriangleEdges spec)
                      tt_shape ee_shape
          A16 -> print_generic format (decompose_generic gatebase $ a16_TriangleTestT)
                       ee_shape
          A17 -> print_generic format (decompose_generic gatebase $ a17_TriangleTestTw spec)
                       tt_shape ee_shape node_shape
          A18 -> print_generic format (decompose_generic gatebase $ a18_TriangleEdgeSearch spec)
                       tt_shape ee_shape qubit
          A19 -> print_generic format (decompose_generic gatebase $ a19_GCQWalk spec)
                       tt_shape ee_shape node_shape qubit
          A20 -> print_generic format (decompose_generic gatebase $ a20_GCQWStep spec)
                       tt_shape ee_shape node_shape gcqw_shape
          O2 -> print_generic format (decompose_generic gatebase $ \u -> o2_ConvertNode l u (2^(n-1))) node_shape	
          O3 -> print_generic format (decompose_generic gatebase $ o3_TestEqual) (qinttf_shape l) (qinttf_shape l)
          O4 -> print_generic format (decompose_generic gatebase $ o4_POW17) (qinttf_shape l)
          O5 -> print_generic format (decompose_generic gatebase $ o5_MOD3) (qinttf_shape l)
          O6 -> print_generic format (decompose_generic gatebase $ \u -> o6_SUB u (2^(n-1))) (qinttf_shape l)
          O7 -> print_generic format (decompose_generic gatebase $ o7_ADD) (qinttf_shape l) (qinttf_shape l)
          O8 -> print_generic format (decompose_generic gatebase $ o8_MUL) (qinttf_shape l) (qinttf_shape l)

      where
        rbar = max ((2 * r) `div` 3) 1
        proj3 (a,b,c,d) = c
        node_shape = (replicate n qubit)
        tt_shape = (intMap_replicate (2^r) node_shape)
        ee_shape = (IntMap.fromList [(j,intMap_replicate j qubit) | j <- [0..((2^r)-1)]])
        eed_shape = (intMap_replicate (2^r) qubit)
        gcqw_shape = (intMap_replicate (2^rbar) (qdint_shape r),
                     (qdint_shape rbar),
                     (qdint_shape r),
                     (intMap_replicate (2^rbar) qubit),
                     (qdint_shape (2*rbar - 1)),
                     qubit)


-- | Compute the appropriate problem specification for the given options.
spec_of_options :: Options -> QWTFP_spec
spec_of_options Options { oracle = Orthodox, n = n, r = r, l = l, qram = qram} = 
  (n,r,
   (\u v edge -> do (u,v,edge) <- o1_ORACLE l u v edge; return edge),
   qram_select qram)          
spec_of_options Options { oracle = Blackbox, n = n, r = r, qram = qram} = 
    (n,r,placeholder_oracle,qram_select qram)
    
-- | Maps a 'QRamSelect' element to the corresponding 'Qram' object.
qram_select :: QRamSelect -> Qram
qram_select Standard_QRam = standard_qram
qram_select Alt_QRam = alt_qram
