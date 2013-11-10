-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- |
-- Authors: Artur Scherer, Siun-Chuon Mau, Benoît Valiron
-- 
-- An implementation of the quantum linear system algorithm. The
-- algorithm finds the solution to a sparse system of linear equations
-- /Ax/=/b/, with a scaling exponentially better than the best known
-- classical algorithms. Here, /A/ is an /N/ × /N/ sparse matrix, /b/
-- an /N/ × 1 vector of known values, and /x/ is the solution.
-- 
-- Huge sparse linear systems are common in applied sciences and
-- engineering, such as those resulting from solving partial
-- differential equations by means of Finite Element Method (FEM).
-- 
-- The example analyzed in this program is the scattering of
-- electromagnetic waves off a 2D metallic region, where the FEM
-- allows to convert Maxwell’s equations into a sparse linear system.
-- 
-- The QLS algorithm is based on two main techniques: 
-- 
-- * Quantum Phase Estimation, which uses the Quantum Fourier
-- Transform and Hamiltonian Simulation, which makes frequent queries
-- to the oracle for matrix /A/;
-- 
-- * Quantum Amplitude Estimation, based on Grover’s search technique.
-- 
-- 
-- The algorithm is described in:
-- 
-- * Aram W. Harrow, Avinatan Hassidim, Seth Lloyd. Quantum algorithm
-- for solving linear systems of equations. /Phys. Rev. Lett./ vol. 15,
-- no. 103, pp. 150502 (2009).
-- 
-- * B. D. Clader, B. C. Jacobs, C. R. Sprouse. Quantum algorithm to
-- calculate electromagnetic scattering cross
-- sections. <http://arxiv.org/abs/1301.2340>.
-- 
-- The present implementation is based on detailed algorithm and
-- oracle specifications that were provided to us by the IARPA QCS
-- program and written by B. David Clader and Bryan C. Jacobs.
-- 
-- 
-- Modules:
-- 
--  * "Algorithms.QLS.Main": Command line interface.
-- 
--  * "Algorithms.QLS.QSignedInt": An implementation of signed
--  integers.
-- 
--  * "Algorithms.QLS.QSignedIntAux": Helper module.
-- 
--  * "Algorithms.QLS.QDouble": An implementation of real numbers,
--  using fixed-point notation.
-- 
--  * "Algorithms.QLS.RealFunc": Implementation of various analytic
--  functions, for use with the automated circuit generation tool.
-- 
--  * "Algorithms.QLS.Utils": Helper module.
-- 
--  * "Algorithms.QLS.QLS": The implementation of the main algorithm.
-- 
--  * "Algorithms.QLS.CircLiftingImport": Helper module.
-- 
--  * "Algorithms.QLS.TemplateOracle": Implementation of the oracle,
--  in regular Haskell, together with the \"build_circuit\" keyword to
--  allow automated circuit generation.

module Algorithms.QLS.Main where

import Quipper

import QuipperLib.Arith
import QuipperLib.Decompose
import QuipperLib.Unboxing

import qualified Algorithms.QLS.QLS as QLS
import Algorithms.QLS.Utils
import Algorithms.QLS.QDouble    as QDouble
import Algorithms.QLS.RealFunc   as QReal
import Algorithms.QLS.QSignedInt as QSInt
import Algorithms.QLS.TemplateOracle

import Libraries.CommandLine

-- import other stuff
import System.Console.GetOpt
import System.Environment    
import System.Exit
import System.IO
import Control.Monad
import Data.List
import Data.Char
import Data.Ratio as Ratio

-- ----------------------------------------------------------------------
-- * Command line interface

-- $ This module provides a command line interface for the Quantum
-- Linear System algorithm. This allows the user, for example, to plug
-- in different oracles, select a gate base, control boxing of
-- subcircuits, and select different output formats.

-- ----------------------------------------------------------------------
-- * Option processing

-- | An enumeration type for determining what the main function should do.
data WhatToShow = 
  Circuit     -- ^Show the whole circuit.
  | Oracle    -- ^Show only an oracle.
  deriving Show

-- | An enumeration type for selecting an oracle implementation.
data OracleSelect =
  Matlab       -- ^The oracle, implemented with Template Haskell.
  | Blackbox   -- ^A blackbox oracle.
  deriving Show

-- | An enumeration type for selecting an oracle to print.
data WhichOracle = 
  OracleR             -- ^Oracle r.
  | OracleB           -- ^Oracle b.
  | OracleA Int Bool  -- ^Oracle A, with selected band and boolean parameter.
  deriving Show

-- | A data type to hold values set by command line options.
data Options = Options {
  what :: WhatToShow,           -- ^What kind of thing to output.
  format :: Format,             -- ^The output format.
  gatebase :: GateBase,         -- ^What kind of gates to decompose into.
  oracle :: OracleSelect,       -- ^Which oracle implementation to use.
  whichoracle :: WhichOracle,   -- ^Which oracle to output.
  param :: QLS.RunTimeParam,    -- ^Run time parameters.
  peel :: Int                   -- ^number of layers of subroutines to peel away.
} deriving Show

-- | The default options.
defaultOptions :: Options
defaultOptions = Options
  { what = Circuit,
    format = GateCount,
    gatebase = Logical,
    oracle = Blackbox,
    whichoracle = OracleR,
    param = QLS.dummy_RT_param,
    peel = 0
  }

-- | The list of command line options, in the format required by 'getOpt'.
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option ['h'] ["help"]    (NoArg help)           "print usage info and exit",
    Option ['C'] ["circuit"] (NoArg (what Circuit)) "output the whole circuit (default)",
    Option ['O'] ["oracle"]  (ReqArg whichoracle "<name>") "output only the oracle <name> (default: r) ", 
    Option ['f'] ["format"]  (ReqArg format "<format>") "output format for circuits (default: gatecount)",
    Option ['g'] ["gatebase"] (ReqArg gatebase "<gatebase>") "type of gates to decompose into (default: logical)",
    Option ['o'] []          (ReqArg oracle "<oracle>") "select oracle implementation to use (default: blackbox)",
    Option ['p'] ["param"]   (ReqArg param "<param>")  "choose a set of parameters (default: dummy).",
    Option ['P'] ["peel"]    (ReqArg peel "<n>") "peel <n> layers of boxed subroutines (default: 0)."
  ]
    where
      what :: WhatToShow -> Options -> IO Options
      what w o = return o { what = w }
      
      peel :: String -> Options -> IO Options
      peel string o = case (parse_int string) of
           Just i -> return o { peel = i }
           Nothing -> optfail ("peel requires a argument number.")

      param :: String -> Options -> IO Options
      param string o =
        case string of 
          "large"   -> return o { param = QLS.large_RT_param }
          "dummy" -> return o { param = QLS.dummy_RT_param }
          "small" -> return o { param = QLS.small_RT_param }
          _       -> let (p,v) = break ((==) '=') string in     
                     case p of
                        _ -> optfail ("Parameter not implemented -- " ++ string ++ "\n")
      
      whichoracle :: String -> Options -> IO Options
      whichoracle string o =
        case (toLower $ head string) of
          'r' -> return o { whichoracle = OracleR, what = Oracle }
          'b' -> return o { whichoracle = OracleB, what = Oracle }
          'a' -> let b = parse_int [string !! 1] in
                 let a = toLower (string !! 2) in
                 case (b,a) of
                 (Just i, 't') -> return o { whichoracle = OracleA i True, what = Oracle }
                 (Just i, 'f') -> return o { whichoracle = OracleA i False, what = Oracle }
                 _ -> error ("Band " ++ (show (string !! 1)) ++ " or boolean " ++ (show a) ++ " not valid.")
          _  -> error ("Oracle " ++ (show (string !! 0)) ++ " not valid.")


      format :: String -> Options -> IO Options
      format str o = do
        case match_enum format_enum str of
          [(_, GateCount)] -> return o { format = GateCount }
          [(_, ASCII)] -> return o { format = ASCII }          
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
  ("matlab", Matlab),
  ("blackbox", Blackbox)
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
  putStr (show_enum "format" [("ascii", ASCII),("gatecount",GateCount)])
  putStr (show_enum "gatebase" gatebase_enum)
  putStr (show_enum "oracle implementation" oracle_enum)
  putStrLn "Possible values for param are: dummy, small, large."
  putStrLn "Possible values for oracle are: r, b, A[band][t|f]. E.g. \"-OA1t\" asks for band 1 with boolean argument True. For all three oracles, the factors are set up to 1.0."
    where header = "Usage: qls [OPTION...]"


-- ----------------------------------------------------------------------
-- * The QLS main function

-- | Main function: read options, then execute the appropriate task.
main :: IO()
main = do
  argv <- getArgs
  options <- dopts argv
  case options of
    Options { what = Circuit, format = format, gatebase = gatebase, oracle = oracle, param = param, peel = peel} -> 
      let o = case oracle of {Blackbox -> QLS.dummy_oracle; Matlab -> QLS.inline_oracle} in
      print_simple format $ decompose_generic gatebase $ ncompose peel unbox $ do QLS.qlsa_FEM_main param o; return ()
    Options { what = Oracle, format = format, gatebase = gatebase, param = param, whichoracle = whichoracle, peel = peel } ->
      let n2_blist = replicate (QLS.n2 param) qubit in
      let n4_blist = replicate (QLS.n4 param) qubit in
      let (oracle, list_of_inputs) = 
            case whichoracle of 
              OracleR ->     (QLS.inline_oracle_r param 1.0 1.0, (n2_blist, n4_blist, n4_blist))
              OracleB ->     (QLS.inline_oracle_b param 1.0 1.0, (n2_blist, n4_blist, n4_blist))
              OracleA i b -> (QLS.inline_oracle_A param 1.0 i b, (n2_blist, n2_blist, n4_blist))
      in do
       print_generic format (decompose_generic gatebase $ ncompose peel unbox $ oracle) list_of_inputs

