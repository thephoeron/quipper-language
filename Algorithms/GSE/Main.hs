-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | 
-- Authors: Alexander S. Green, Artur Scherer, Peter Selinger,
-- Alexandr Virodov
-- 
-- An implementation of the Ground State Estimation algorithm. The
-- purpose of this algorithm is to determine the ground state energy
-- of a quantum molecular system. The algorithm depends on a table of
-- one- and two-electron transition integrals, which must be
-- separately pre-computed and supplied in a pair of data files. From
-- this integral data, the molecular electronic Hamiltonian is derived
-- using the Jordan-Wigner transformation. To simulate this
-- Hamiltonian by a quantum circuit, it is first broken into small
-- time steps using Trotterization. The second quantized local
-- Hamiltonian interaction terms can be divided into a small number of
-- cases (number operators, excitation operators, Coulomb and exchange
-- operators, number-excitation operators, and double excitation
-- operators). Each interaction term is synthesized into a piece of
-- quantum circuit following one of a small number of patterns (called
-- \"circuit templates\"). Finally, the quantum phase estimation
-- algorithm is applied to the resulting circuit to obtain the ground
-- state energy.
-- 
-- The algorithm is described in:
-- 
-- * James D. Whitfield, Jacob Biamonte, and Alán
-- Aspuru-Guzik. \"Simulation of electronic structure Hamiltonians
-- using quantum computers.\" 
-- /Molecular Physics/ 109(5):735–750, 2011.
-- See also <http://arxiv.org/abs/1001.3855>.
-- 
-- The present implementation is based on a detailed algorithm
-- specification that was provided to us by the IARPA QCS program and
-- written by Anargyros Papageorgiou, James Whitfield, Joseph Traub,
-- and Alán Aspuru-Guzik.
-- 
-- Modules:
-- 
-- * "Algorithms.GSE.Main": Command line interface.
-- 
-- * "Algorithms.GSE.JordanWigner": The Jordan-Wigner transformation
-- and automated symbolic derivation of circuit templates for second
-- quantized interaction terms.
-- 
-- * "Algorithms.GSE.GSE": The main circuit for the GSE Algorithm.
-- 
-- * "Algorithms.GSE.GSEData": Functions for reading the one- and
-- two-electron integral data from a pair of data files.

module Algorithms.GSE.Main where

import Quipper

import QuipperLib.Decompose

import Algorithms.GSE.GSE
import Algorithms.GSE.GSEData
import Algorithms.GSE.JordanWigner
import Libraries.CommandLine

-- import other stuff
import System.Console.GetOpt
import System.Environment    
import System.Exit
import Control.Monad
import Data.Bits
import qualified System.FilePath as FilePath

-- ----------------------------------------------------------------------
-- * Documentation

-- $ This module provides a command line interface for the Ground
-- State Estimation algorithm. This allows the user to set a number of
-- parameters, such as /b/ (the number of precision qubits), /M/ (the
-- number of spin orbitals), /N/ (the number of occupied spin orbitals
-- in the prepared approximate ground state), and /E/[sub min] and
-- /E/[sub max] (the energy range). Command line options are also
-- provided to specify the filenames for the Hamiltonian integral
-- data, and to specify the output format and gate base.

-- ----------------------------------------------------------------------
-- * Option processing

-- | An enumeration type for determining what the main function should do.
data WhatToShow = 
  Circuit           -- ^Show the whole circuit (default).
  | Template [Int]  -- ^Show a particular template.
  deriving Show

-- | A data type to hold values set by command line options.
data Options = Options {
  what :: WhatToShow,     -- ^What kind of thing to output.
  format :: Format,       -- ^The output format.
  gatebase :: GateBase,   -- ^What kind of gates to decompose into.
  gse_orthodox :: Bool,   -- ^Use the Coulomb operator of Whitman et al.
  
  gse_b :: Int,           -- ^The number of precision qubits /b/.
  gse_m :: Int,           -- ^The number of basis functions /M/.
  gse_occupied :: Int,    -- ^The number of occupied orbitals.
  gse_delta_e  :: Double, -- ^Energy range Δ/E/ = /E/[sub max] - /E/[sub min].
  gse_e_max :: Double,    -- ^Energy range /E/[sub max].
  gse_nfun :: Int -> Int, -- ^The function /k/ ↦ /N/[sub /k/].
  
  gse_h1_file :: String,  -- ^Filename for one-electron data.
  gse_h2_file :: String,  -- ^Filename for two-electron data.
  gse_datadir :: String   -- ^Directory for data files.
  }
             
-- | The default options.
defaultOptions :: Options
defaultOptions = Options { 
  what         = Circuit,    
  format       = Preview,
  gatebase     = Logical,
  gse_orthodox = False,
  
  gse_b        = 3,
  gse_m        = 4,
  gse_occupied = 2,
  gse_delta_e  = 6.5536,
  gse_e_max    = -3876.941,
  gse_nfun     = (\k -> 1),  -- by default, we skip the repetition
  
  gse_h1_file  = "h_1e_ascii",
  gse_h2_file  = "h_2e_ascii",
  gse_datadir  = "."
  }

-- | Show the default value of an option.
showDefault :: (Show a) => (Options -> a) -> String
showDefault func = show (func defaultOptions)
    
-- | The list of command line options, in the format required by 'getOpt'.
options :: [OptDescr (Options -> IO Options)]
options = [ 
  Option ['h'] ["help"]      (NoArg  help)                       $ "print usage info and exit",
  Option ['C'] ["circuit"]   (NoArg (what Circuit))              $ "output the whole circuit (default)",
  Option ['T'] ["template"]  (ReqArg read_template "<indices>")  $ "output a particular circuit template",
  Option ['f'] ["format"]    (ReqArg read_format "<format>")     $ "output format for circuits (default: " ++ showDefault format ++ ")",
  Option ['g'] ["gatebase"]  (ReqArg read_gatebase "<gatebase>") $ "gates to decompose into (default: " ++ showDefault gatebase ++ ")",
  Option ['m'] ["orbitals"]  (ReqArg read_m "<N>")               $ "number of orbitals (default: " ++ showDefault gse_m ++ ")",
  Option ['o'] ["occupied"]  (ReqArg read_occupied "<N>")        $ "number of occupied orbitals (default: " ++ showDefault gse_occupied ++ ")",
  Option ['b'] ["precision"] (ReqArg read_b "<N>")               $ "number of precision qubits (default: " ++ showDefault gse_b ++ ")",
  Option ['D'] ["delta_e"]   (ReqArg read_delta_e "<energy>")    $ "energy range (default: " ++ showDefault gse_delta_e ++ ")",
  Option ['E'] ["e_max"]     (ReqArg read_e_max "<energy>")      $ "maximum energy (default: " ++ showDefault gse_e_max ++ ")",
  Option []    ["n0"]        (ReqArg read_n0 "<N>")              $ "use N_k = n0 * 2^k (default: N_k = 1)",
  Option ['l'] ["large"]     (NoArg large_parameters)            $ "set large problem size (m=208, o=84, b=12, n0=100)",
  Option ['x'] ["orthodox"]  (NoArg orthodox)                    $ "use the Coulomb operator of Whitman et al.",
  Option []    ["h1"]        (ReqArg read_h1    "<file>")        $ "filename for one-electron data (default: " ++ showDefault gse_h1_file  ++ ")",
  Option []    ["h2"]        (ReqArg read_h2    "<file>")        $ "filename for two-electron data (default: " ++ showDefault gse_h2_file  ++ ")",
  Option ['d'] ["datadir"]   (ReqArg read_datadir "<file>")      $ "directory for one- and two-electron data (default: current)"
  ]
    where
      what :: WhatToShow -> Options -> IO Options
      what w o = return o { what = w }
      
      large_parameters o = 
        return o { 
          gse_b = 12, 
          gse_m = 208, 
          gse_delta_e  = 6.5536,
          gse_e_max    = -3876.941,
          gse_occupied = 84,
          gse_nfun = (\k -> 100 * (1 `shift` k))
          }
        
      orthodox o = return o {gse_orthodox = True }
      
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

      read_b :: String -> Options -> IO Options
      read_b string o =
        case parse_int string of 
          Just n | n > 0 -> return o { gse_b = n }
          _ -> optfail ("Invalid b (precision) -- " ++ string ++ "\n")
          
      read_m :: String -> Options -> IO Options
      read_m string o =
        case parse_int string of 
          Just n | n > 0 -> return o { gse_m = n }
          _ -> optfail ("Invalid m (orbitals) -- " ++ string ++ "\n")

      read_n0 :: String -> Options -> IO Options
      read_n0 string o =
        case parse_int string of 
          Just n | n > 0 -> return o { gse_nfun = (\k -> n * (1 `shift` k)) }
          _ -> optfail ("Invalid n0 -- " ++ string ++ "\n")

      read_occupied :: String -> Options -> IO Options
      read_occupied string o =
        case parse_int string of 
          Just n | n > 0 -> return o { gse_occupied = n }
          _ -> optfail ("Invalid o (occupied) -- " ++ string ++ "\n")
          
      read_delta_e :: String -> Options -> IO Options
      read_delta_e string o =
        case parse_double string of 
          Just n | n >= 0 -> return o { gse_delta_e = n }
          _ -> optfail ("Invalid Delta E -- " ++ string ++ "\n")

      read_e_max :: String -> Options -> IO Options
      read_e_max string o =
        case parse_double string of 
          Just n | n >= 0 -> return o { gse_e_max = n }
          _ -> optfail ("Invalid E_max -- " ++ string ++ "\n")

      read_h1 :: String -> Options -> IO Options
      read_h1 string o = return o { gse_h1_file = string }

      read_h2 :: String -> Options -> IO Options
      read_h2 string o = return o { gse_h2_file = string }

      read_datadir :: String -> Options -> IO Options
      read_datadir string o = return o { gse_datadir = string }

      read_template :: String -> Options -> IO Options
      read_template string o = do
        ps <- sequence [ convert p | p <- split ',' string ]
        let len = length ps
        if len == 2 || len == 4 then
          return o { what = Template ps }
         else
          optfail ("Must give 2 or 4 indices, not " ++ (show len) ++ "\n")
        where
          split c as = case break (== c) as of
            (h,_:t) -> h : (split c t)
            (h,[]) -> [h]
          convert p = case parse_int p of
            Just n | n >= 0 -> return n
            _ -> optfail ("Invalid index -- '" ++ p ++ "'\n")
            
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

-- | Print usage message to 'stdout'.
usage :: IO ()
usage = do
  putStr (usageInfo header options) 
  putStr (show_enum "format" format_enum)
  putStr (show_enum "gatebase" gatebase_enum)
  putStr ("Indices can be specified as p,q or p,q,r,s (with no spaces)\n")
    where header = "Usage: gse [OPTION...]"

-- ----------------------------------------------------------------------
-- * The GSE main function

-- | Main function: read options, then execute the appropriate task.
main :: IO()
main = do
  -- Read options.
  argv <- getArgs
  options <- dopts argv
  
  case what options of
    Circuit -> main_circuit options
    Template qs -> main_template options qs
    
-- | Main function for outputting the GSE circuit.
main_circuit :: Options -> IO()
main_circuit options = do

  -- Read parameters.
  let b = gse_b options
      m = gse_m options
      o = gse_occupied options
      dE = gse_delta_e options
      e_max = gse_e_max options
      datadir = gse_datadir options
      file1 = gse_h1_file options
      file2 = gse_h2_file options
      nfun = gse_nfun options
      orth = gse_orthodox options
      
  -- Calculate derived parameters.
  let tau = 2*pi / dE
      
      path1 = FilePath.combine datadir file1
      path2 = FilePath.combine datadir file2
  
  -- Load data from file.
  gse_data <- load_gse_data m path1 path2
  
  -- Generate the main circuit.
  let circuit = gse b m o gse_data tau e_max nfun orth
  
  -- Print it.
  print_simple (format options) (decompose_generic (gatebase options) circuit)

  -- Of course, if we had a quantum computer, we would run it instead.
  {- 
  ms <- run_simple circuit
  let e0 = e_max - dE * (int_from_bitlist mk) / (2**b)
  return e0
  -}

-- | Main function for outputting a particular template.
main_template :: Options -> [Int] -> IO()
main_template options [p,q] = do
  show_one_electron (format options) (gatebase options) p q

main_template options [p,q,r,s] = do
  if gse_orthodox options
    then show_two_electron_orthodox (format options) (gatebase options) p q r s
    else show_two_electron (format options) (gatebase options) p q r s
  
main_template options qs =
  error "main_template: wrong number of indices given"

