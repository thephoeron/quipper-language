-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | 
-- Author: Alexander S. Green
-- 
-- An implementation of the Boolean Formula algorithm, applied to
-- finding whether a winning strategy exists in a game of Hex.
-- 
-- \[image hex1.png]
-- \[image hex2.png]
-- 
-- The algorithm consists of eigenvalue analysis using phase estimation, 
-- acting on an oracle that defines a quantum walk over the NAND graph 
-- representation of a game of Hex, for a given size of board. 
--
-- The implementation defines the NAND graph of a game of Hex by adding a few 
-- extra nodes to a graph representing pieces being played during a game of Hex.
-- An extra node is added to each leaf node that represents a completed game of
-- Hex, for which the red player has won, as well as two extra nodes being
-- added below the root node.
--
-- The general form of the algorithm is described in:
-- 
-- * A. Ambainis, A. M. Childs, B. W. Reichardt, R. Spalek, and 
-- S. Zhang. \"Any AND-OR formula of size /N/ can be evaluated in 
-- time /N/[sup 1\/2+/o/(1)] on a quantum computer.\" /SIAM J. Comput./, 
-- 39:2513–2530, April 2010. See also
-- <http://www.ucw.cz/~robert/papers/andor-siamjc.pdf>.
-- 
-- * A. M. Childs, B. W. Reichardt, R. Spalek, and S. Zhang. 
-- \"Every NAND formula of size /N/ can be evaluated in time 
-- /N/[sup 1\/2+/o/(1)] on a quantum computer\" 2007.
-- <http://arxiv.org/abs/quant-ph/0703015>.
-- 
-- The present implementation is based on detailed algorithm and
-- oracle specifications that were provided to us by the IARPA QCS
-- program and written by Patrick Henry.
-- 
-- Modules:
-- 
-- * "Algorithms.BF.Main": Command line interface.
-- 
-- * "Algorithms.BF.BooleanFormula": Implementation of the various quantum
-- circuits that make up the boolean formula algorithm.
-- 
-- * "Algorithms.BF.Hex": Implementation of the circuits for determining which 
-- player has won a completed game of Hex.
-- 
-- * "Algorithms.BF.QuantumIf": Introduces a simple way of defining 
-- \"boolean statements\" acting over qubits.
-- 
-- * "Algorithms.BF.HexBoard": Code for drawing Hex boards in graphical format.
-- 
-- * "Algorithms.BF.Testing": Testing facilities for the boolean
-- formula algorithm, and some auxiliary function definitions.

module Algorithms.BF.Main where

import Quipper

import QuipperLib.Decompose

import qualified Algorithms.BF.BooleanFormula as BooleanFormula
import qualified Algorithms.BF.Hex as Hex
import qualified Algorithms.BF.Testing as Testing
import qualified Algorithms.BF.HexBoard as HexBoard

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

-- $ This module provides a command line interface for the Boolean
-- Formula algorithm. This allows the user, for example, to plug in
-- different oracles, show different parts of the circuit, run a demo,
-- and select different output formats.

-- ----------------------------------------------------------------------
-- * Option processing

-- | An enumeration type for determining the action that should be taken when
-- the executable is run.
data WhatToDo =
  OutputCircuit -- ^ Output the circuit.
  | Demo        -- ^ Run a demo of the circuit, which is different for the
                -- various parts of the algorithm.
  | HexBoard    -- ^ Output a representation of the moves already made for the 
                -- defined oracle, i.e. a partially filled Hex Board.
  deriving Show

-- | An enumeration type for determining what the main function should do.
data WhatPart = 
  WholeCircuit   -- ^ The whole circuit.
  | U            -- ^ Only one iteration of the U from EXP_U circuit.
  | Oracle       -- ^ Only the Oracle circuit.
  | Hex          -- ^ Only the Hex circuit.
  | Checkwin_Red -- ^ Only the Checkwin_Red circuit, i.e. including Flood_Fill.
  | Diffuse      -- ^ Only the Diffuse circuit.
  | Walk         -- ^ Only the Walk circuit.
  | Undo_Oracle  -- ^ Only the Undo_Oracle circuit.
  deriving Show

-- | An enumeration type for selecting an oracle size.
data OracleSize =
  Full -- ^ The oracle for a 9 by 7 Hex board, 
       --   with a 189 qubit phase estimation register.
  | Small  -- ^ The oracle for a 5 by 3 Hex board, 
           --   with a 4 qubit phase estimation register
  | Custom Int Int Int -- ^ A custom oracle.
  deriving Show

-- | A data type to hold values set by command line options.
data Options = Options {
  what :: WhatToDo,          -- ^ What we want to do.
  part :: WhatPart,          -- ^ What part of the algorithm to use.
  format :: Format,          -- ^ The output format of a circuit.
  oracle_size :: OracleSize, -- ^ Which size of oracle to use.
  oracle_init :: [Int],      -- ^ A list of moves already made, 
                             --   which is used to define /s/
  hex :: BooleanFormula.HexCircuit, -- ^ A flag of which HEX circuit to use.
  gatebase :: GateBase       -- ^ What kind of gates to decompose into.
}

-- | The default options, which correspond to a Preview of the entire circuit
-- for the small oracle. 
defaultOptions :: Options
defaultOptions = Options
  { what = OutputCircuit, 
    part = WholeCircuit,
    format = Preview,
    oracle_size = Small, 
    oracle_init = [],
    hex = BooleanFormula.Hex,
    gatebase = Logical
  }

-- | The list of command line options, in the format required by 'getOpt'.
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option ['C'] ["circuit"]  (NoArg (what OutputCircuit)) "output the whole circuit (default)",
    Option ['D'] ["demo"]     (NoArg (what Demo))            "run a demo of the circuit",
    Option ['H'] ["hexboard"] (NoArg (what HexBoard))        "output a representation of the initial state of the given oracle, i.e. the game played so far",
    Option ['p'] ["part"]     (ReqArg part "<part>")         "which part of the circuit to use (default: whole)",
    Option ['o'] ["oracle"]   (ReqArg oracle "<oracle>")     "which oracle to use (default: small)",
    Option ['m'] ["moves"]    (ReqArg oracle_init "<moves>") "which moves have already been made (default: [])",
    Option ['f'] ["format"]   (ReqArg format "<format>")     "output format for circuits (default: _preview)",
    Option ['d'] ["dummy"]    (NoArg setDummy)               "set to only use a dummy HEX gate instead of the full hex circuit",
    Option ['h'] ["help"]     (NoArg help)                   "print usage info and exit",
    Option ['g'] ["gatebase"] (ReqArg gatebase "<gatebase>") "type of gates to decompose the output circuit into (default: logical)"
  ]
    where
      help :: Options -> IO Options
      help o = do
        usage
        exitSuccess

      what :: WhatToDo -> Options -> IO Options
      what w o = return o { what = w }

      part :: String -> Options -> IO Options
      part str opt = do
        case match_enum part_enum str of
          [(_, p)] -> return opt { part = p }
          [] -> optfail ("Unknown part -- " ++ str ++ "\n")
          _ -> optfail ("Ambiguous part -- " ++ str ++ "\n")
      
      oracle :: String -> Options -> IO Options
      oracle str opt = do
        case match_enum oracle_enum str of
          [(_, Just o)] -> return opt {oracle_size = o}
          [] -> case getCustom str of
            Just o -> return opt {oracle_size = o}
            Nothing -> optfail ("Unknown oracle -- " ++ str ++ "\n")
          _ -> case getCustom str of
            Just o -> return opt {oracle_size = o}
            Nothing -> optfail ("Ambiguous oracle -- " ++ str ++ "\n")

      oracle_init :: String -> Options -> IO Options
      oracle_init str opt = case parse_list_int str of
        Nothing -> error "moves should be given as a Haskell list of integers, e.g. [1,2,3,4,5]"
        Just pos -> return opt {oracle_init = pos} 

      format :: String -> Options -> IO Options
      format str opt = do
        case match_enum format_enum str of
          [(_, f)] -> return opt { format = f }
          [] -> optfail ("Unknown format -- " ++ str ++ "\n")
          _ -> optfail ("Ambiguous format -- " ++ str ++ "\n")

      setDummy :: Options -> IO Options
      setDummy o = return o {hex = BooleanFormula.Dummy}

      gatebase :: String -> Options -> IO Options
      gatebase str o = do
        case match_enum gatebase_enum str of
          [(_, f)] -> return o { gatebase = f }
          [] -> optfail ("Unknown gate base -- " ++ str ++ "\n")
          _ -> optfail ("Ambiguous gate base -- " ++ str ++ "\n")

-- | An enumeration of available circuit parts and their names.
part_enum :: [(String, WhatPart)]
part_enum = [
 ("whole",WholeCircuit),
 ("u",U),
 ("oracle",Oracle),
 ("hex",Hex),
 ("checkwin_red",Checkwin_Red),
 ("diffuse",Diffuse),
 ("walk",Walk),
 ("undo_oracle",Undo_Oracle)
  ]
      
-- | An enumeration of available oracles and their names.
oracle_enum :: [(String, Maybe OracleSize)]
oracle_enum = [
  ("9by7", Just Full),
  ("small", Just Small),
  ("custom x y t", Nothing) -- this is a dummy, to show in a help message
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
  putStr (show_enum "part" part_enum)
  putStr (show_enum "oracle" oracle_enum)
  putStr (show_enum "format" format_enum)
  putStr (show_enum "gatebase" gatebase_enum)
    where header = "Usage: bf [OPTION...]"

-- ----------------------------------------------------------------------
-- * The BF main function

-- | Main function: read options, then execute the appropriate task.
main :: IO ()
main = do
  argv <- getArgs
  options <- dopts argv
  case check_options options of
    Options { what = what, part = part, format = format, oracle_size = oracle_size, oracle_init = oracle_init, hex = hex, gatebase = gatebase } -> do
      let bfo = getOracle oracle_size oracle_init
      let bfo' = BooleanFormula.update_hex bfo hex
      let bfo'' = BooleanFormula.update_start_board bfo' (Testing.moves_to_hex bfo' oracle_init) 
      case what of
        OutputCircuit -> output_part part format gatebase bfo''
        Demo -> demo_part part format bfo''
        HexBoard -> do
         let boards = map (Testing.moves_to_hex bfo') (inits oracle_init)
         HexBoard.output_HexBoards format bfo' boards
 
-- | Check that the given options are valid. This currently is only required to
-- check that the list of moves already made, is valid for the given size of oracle.
check_options :: Options -> Options
check_options opts = case length moves > xy of
  True -> error "Too many moves have been given"
  False -> case (filter (\pos -> pos >= xy || pos < 0) moves) of
   [] -> case moves == nub moves of
     True -> opts
     False -> error "Duplicate moves made"
   _ -> error "Move out of bounds"
  where
    moves = oracle_init opts
    xy = x * y 
    (x,y) = case oracle_size opts of
              Full -> (9,7)
              Small -> (5,3)
              (Custom x y t) -> (x,y)

-- | Convert an OracleSize, and a list of played positions, into an actual oracle.
getOracle :: OracleSize -> [Int] -> BooleanFormula.BooleanFormulaOracle
getOracle Full _ = BooleanFormula.full_oracle
getOracle Small _ = BooleanFormula.test_oracle
getOracle (Custom x y t) _ = BooleanFormula.createOracle x y t

-- | This function defines what should be output for each part of the circuit.
output_part :: WhatPart -> Format -> GateBase -> BooleanFormula.BooleanFormulaOracle -> IO ()
output_part WholeCircuit f g o = BooleanFormula.main_circuit f g o
output_part U f g o = BooleanFormula.main_u f g o
output_part Oracle f g o = BooleanFormula.main_oracle f g o
output_part Hex f g o = BooleanFormula.main_hex f g o
output_part Checkwin_Red f g o = BooleanFormula.main_checkwin_red f g o
output_part Diffuse f g o = BooleanFormula.main_diffuse f g o
output_part Walk f g o = BooleanFormula.main_walk f g o
output_part Undo_Oracle f g o = BooleanFormula.main_undo_oracle f g o

-- | This function defines what should be done for a demo of each part of the circuit.
demo_part :: WhatPart -> Format -> BooleanFormula.BooleanFormulaOracle -> IO ()
demo_part WholeCircuit ASCII o = Testing.repeat_odwu_infinite (BooleanFormula.update_hex o BooleanFormula.EmptyHex) (BooleanFormula.createRegister o)
demo_part WholeCircuit f o = do
  let n = (BooleanFormula.oracle_s o) * 2
  boards <- Testing.repeat_odwu_n n (BooleanFormula.update_hex o BooleanFormula.EmptyHex) (BooleanFormula.createRegister o)
  HexBoard.output_HexBoards f o boards
demo_part Hex f o = do
  let o_s = BooleanFormula.oracle_s o
  case o_s of
   0 -> do
     result <- Testing.run_hex_with_input o (BooleanFormula.createRegister o)
     putStrLn ((if result then "Red" else "Blue") ++ " wins.")
   _ -> error "Hex demo requires a moves input that leaves no moves remaining" 
demo_part Checkwin_Red f o = do
  let o_s = BooleanFormula.oracle_s o
  case o_s of
   0 -> do
     let (red_board,_) = BooleanFormula.start_board o
     blue_boards <- Testing.checkwin_trace o
     let boards = map (\x -> (red_board,x)) blue_boards
     HexBoard.output_HexBoards f o boards
   _ -> error "checkwin_red demo requires a moves input that leaves no moves remaining"
demo_part U f o = demo_part WholeCircuit f o
demo_part Oracle f o = demo_part WholeCircuit f o
demo_part Diffuse f o = demo_part WholeCircuit f o
demo_part Walk f o = demo_part WholeCircuit f o
demo_part Undo_Oracle f o = demo_part WholeCircuit f o

----- Custom Sized Oracles -------

-- | An infinite list of all numbers that are one less than an integer power of 2.
valid_sizes :: [Int]
valid_sizes = map (\x -> (2^x) - 1) [1..]

-- | Return True if the given number is one less than an integer power of 2.
valid_size :: Int -> Bool
valid_size s = valid_size' s valid_sizes
  where
    valid_size' s [] = error "Unreachable Error Occurred: valid_sizes is an infinite list"
    valid_size' s (n:ns) = case compare s n of
     LT -> False
     EQ -> True
     GT -> valid_size' s ns

-- | Create a custom sized oracle, by checking the given /x/,/y/, and /t/ sizes are valid.
createCustom :: Int -> Int -> Int -> OracleSize
createCustom x y t = case (x >= y) of
  False -> error "The x dimension must be at least as big as the y dimension"
  True -> case valid_size (x*y) of
    False -> error "The number of squares on the Hex Board (x*y), must be one less than an integer power of 2"
    True -> case (t > 0) of
      False -> error "The size of the phase estimation register must be greater than 0"
      True -> Custom x y t
    
-- | Parse a string defining a custom oracle size.
getCustom :: String -> Maybe OracleSize
getCustom s = 
  case tokens of
    [] -> Nothing
    (s:strs) -> case (isPrefixOf s "custom") of
      False -> Nothing
      True -> case strs of
        [x_str,y_str,t_str] -> Just (createCustom x y t)
          where
           x = case (parse_int x_str) of
                 Just x -> x
                 Nothing -> error "error parsing x argument"
           y = case (parse_int y_str) of
                 Just y -> y
                 Nothing -> error "error parsing y argument"
           t = case (parse_int t_str) of
                 Just t -> t
                 Nothing -> error "error parsing y argument"
        _ -> error "custom size requires x, y, and t arguments"
  where tokens = words s
