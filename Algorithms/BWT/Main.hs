-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- |
-- Authors: Peter Selinger, Benoît Valiron
-- 
-- An implementation of the Binary Welded Tree algorithm. This
-- algorithm inputs an oracle encoding a graph of the following form:
-- 
-- \[image weldedtree.png]
-- 
-- The graph consists of two binary trees whose leaves are connected
-- by two permutations as shown in the above illustration. Except for
-- the roots of the two trees, all nodes have degree 3. The edges
-- of the graph are colored with 4 different colors. The objective of
-- the algorithm is to find the exit node (17 in the above
-- illustration), given the entrance node (1 in the above
-- illustration). This is done by a Trotterized quantum walk on the
-- graph.
-- 
-- The algorithm is described in:
-- 
-- * A. M. Childs, R. Cleve, E. Deotto, E. Farhi, S. Gutmann, and
-- D. A. Spielman. \"Exponential algorithmic speedup by a quantum
-- walk.\" 
-- /Proceedings of the 35th Annual ACM Symposium on Theory of Computing/, 
-- pp. 59–68, 2003. See also <http://arxiv.org/abs/quant-ph/0209131>.
-- 
-- The present implementation is based on detailed algorithm and
-- oracle specifications that were provided to us by the IARPA QCS
-- program and written by Travis Humble.
-- 
-- Modules:
-- 
-- * "Algorithms.BWT.Main": Command line interface.
-- 
-- * "Algorithms.BWT.Definitions": Some general-purpose definitions.
-- 
-- * "Algorithms.BWT.BWT": The implementation of the main Binary
-- Welded Tree algorithm and oracle, using a more-or-less imperative
-- programming style.
-- 
-- * "Algorithms.BWT.Alternative": Alternate implementations of the
-- main algorithm and various oracles, using a more functional
-- programming style.
-- 
-- * "Algorithms.BWT.Template": Another oracle implementation, using
-- Quipper's \"build_circuit\" feature to automatically extract a
-- quantum circuit from a classical functional program.
-- 
-- * "Algorithms.BWT.Simulate": Functions for simulating, testing, and
-- debugging oracles.

module Algorithms.BWT.Main where

import Quipper

import QuipperLib.Decompose

import qualified Algorithms.BWT.BWT as BWT
import qualified Algorithms.BWT.Simulate as Simulate
import qualified Algorithms.BWT.Alternative as Alternative
import qualified Algorithms.BWT.Template as Template

import Libraries.CommandLine

import System.Console.GetOpt
import System.Environment    
import System.Exit
import System.IO
import Control.Monad
import Data.List
import Data.Char

-- ----------------------------------------------------------------------
-- * Command line interface

-- $ This module provides a command line interface for the Binary
-- Welded Tree algorithm. This allows the user, for example, to plug
-- in different oracles, show different parts of the circuit, select a
-- gate base, simulate, select parameters such as /n/ and /s/, and
-- select different output formats.

-- ----------------------------------------------------------------------
-- * Option processing

-- | An enumeration type for determining what the main function should do.
data WhatToShow = 
  Circuit     -- ^Show the whole circuit.
  | Oracle    -- ^Show only the oracle.
  | Graph     -- ^Show colored edges computed from oracle simulation.
  | OracleC   -- ^Show the \"classical\" oracle as a classical circuit.
  | Simulate  -- ^Run simulations of individual circuit fragments.
  deriving Show

-- | An enumeration type for selecting an oracle.
data OracleSelect =
  Orthodox     -- ^The \"orthodox\" oracle. 
  | Simple     -- ^The \"simple\" oracle.
  | Blackbox   -- ^A blackbox oracle.
  | Classical  -- ^An oracle generated from classical program.
  | Template   -- ^An oracle automatically generated using Template Haskell.
  | TemplateOptim   -- ^An oracle automatically generated using Template Haskell, with peep-hole optimization.
  deriving Show

-- | A data type to hold values set by command line options.
data Options = Options {
  what :: WhatToShow,           -- ^What kind of thing to output.
  format :: Format,             -- ^The output format.
  gatebase :: GateBase,         -- ^What kind of gates to decompose into.
  oracle :: OracleSelect,       -- ^Which kind of oracle to use.
  n :: Int,                     -- ^The tree height.
  c :: Int,                     -- ^The color to use with @--oracle@.
  s :: Int,                     -- ^The parameter /s/ to use.
  dt :: Timestep                -- ^The parameter /dt/ to use.
} deriving Show

-- | The default options.
defaultOptions :: Options
defaultOptions = Options
  { what = Circuit,
    format = Preview,
    n = 5,
    c = 0,
    gatebase = Logical,
    oracle = Orthodox,
    s = 1,
    dt = pi/180
  }

-- | The list of command line options, in the format required by 'getOpt'.
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option ['h'] ["help"]    (NoArg help)           "print usage info and exit",
    Option ['C'] ["circuit"] (NoArg (what Circuit)) "output the whole circuit (default)",
    Option ['O'] ["oracle"]  (NoArg (what Oracle))  "output only the oracle",
    Option ['K'] ["oraclec"] (NoArg (what OracleC)) "output the \"classical\" oracle as a classical circuit",
    Option ['G'] ["graph"]   (NoArg (what Graph))   "print colored graph computed from oracle",
    Option ['S'] ["simulate"] (NoArg (what Simulate)) "run simulations of some circuit fragments for tree height n",
    Option ['f'] ["format"]  (ReqArg format "<format>") "output format for circuits (default: preview)",
    Option ['g'] ["gatebase"] (ReqArg gatebase "<gatebase>") "type of gates to decompose into (default: logical)",
    Option ['o'] []          (ReqArg oracle "<oracle>") "select oracle to use (default: orthodox)",
    Option ['n'] ["height"]  (ReqArg height "<n>")  "set tree height (positive; default 5)",
    Option ['c'] ["color"]   (ReqArg color "<c>")   "color to use with --oracle (0..3, default 0)",
    Option ['s'] ["repeats"] (ReqArg repeats "<s>") "set parameter s (iteration count; default 1)",
    Option ['l'] ["large"]   (NoArg large) "set large problem size: n=300, s=336960",
    Option ['t'] ["dt"]      (ReqArg dt "<dt>")     "set parameter dt (simulation time step; default pi/180)"
  ]
    where
      what :: WhatToShow -> Options -> IO Options
      what w o = return o { what = w }
      
      height :: String -> Options -> IO Options
      height string o = 
        case parse_int string of
          Just n | n >= 1 -> return o { n = n }
          _ -> optfail ("Invalid tree height -- " ++ string ++ "\n")
          
      color :: String -> Options -> IO Options
      color string o =
        case parse_int string of 
          Just c | c >= 0 && c < 4 -> return o { c = c }
          _ -> optfail ("Invalid color -- " ++ string ++ "\n")

      repeats :: String -> Options -> IO Options
      repeats string o =
        case parse_int string of 
          Just s | s >= 0 -> return o { s = s }
          _ -> optfail ("Invalid value for parameter s -- " ++ string ++ "\n")

      large :: Options -> IO Options
      large o = return o { s = 336960, n = 300 }

      dt :: String -> Options -> IO Options
      dt string o =
        case parse_double string of 
          Just dt -> return o { dt = dt }
          _ -> optfail ("Invalid value for parameter dt -- " ++ string ++ "\n")

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

      n_def = show (n defaultOptions)
      c_def = show (c defaultOptions)
      
-- | An enumeration of available oracles and their names.
oracle_enum :: [(String, OracleSelect)]
oracle_enum = [
  ("orthodox", Orthodox),
  ("simple", Simple),
  ("blackbox", Blackbox),
  ("classical", Classical),
  ("template", Template),
  ("optimized", TemplateOptim)
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
    where header = "Usage: bwt [OPTION...]"

-- ----------------------------------------------------------------------
-- * The BWT main function

-- | Main function: read options, then execute the appropriate task.
main :: IO()
main = do
  argv <- getArgs
  options <- dopts argv
  let oracle = oracle_of_options options
  case options of
    Options { what = Circuit, format = format, gatebase = gatebase, s = s, dt = dt } -> 
      BWT.main_circuit format gatebase oracle s dt
    Options { what = Oracle, c = c, format = format, gatebase = gatebase } ->
      BWT.main_oracle format gatebase oracle c
    Options { what = OracleC, c = c, format = format } ->
      Alternative.main_oraclec format oracle c
    Options { what = Graph, format = ASCII, gatebase = gatebase } ->
      Simulate.simulate_edges gatebase oracle
    Options { what = Graph, format = format, oracle = Simple, gatebase = gatebase } -> do
      -- special case: if Simple, change the node numbering
      let doc = Simulate.render_oracle gatebase True oracle
      print_of_document format doc
    Options { what = Graph, format = format, gatebase = gatebase } -> do
      let doc = Simulate.render_oracle gatebase False oracle
      print_of_document format doc
    Options { what = Simulate, n = n } -> do
      Simulate.main_all n

-- | Compute the appropriate 'Oracle' for the given options.
oracle_of_options :: Options -> BWT.Oracle

oracle_of_options Options { oracle = Orthodox, n = n } = 
  BWT.oracle_orthodox f g
  where
    f = take n (True : False : f)
    g = take n (False : True : g)
              
oracle_of_options Options { oracle = Simple } = 
  Alternative.convert_oracle (Alternative.oracle_simple)

oracle_of_options Options { oracle = Blackbox, n = n } = 
  Alternative.convert_oracle (Alternative.oracle_blackbox n)

oracle_of_options Options { oracle = Classical, n = n } = 
  Alternative.convert_oracle (Alternative.oracle_classical f g)
  where
    f = take n (True : False : f)
    g = take n (False : True : g)

oracle_of_options Options { oracle = Template, n = n } =
  Alternative.convert_oracle (Template.oracle_template f g)
  where
    f = take n (True : False : f)
    g = take n (False : True : g)

oracle_of_options Options { oracle = TemplateOptim, n = n } =
  Alternative.convert_oracle (Template.oracle_template_optim f g)
  where
    f = take n (True : False : f)
    g = take n (False : True : g)

