-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides some testing facilities for the Boolean
-- Formula algorithm, as well as some auxiliary function definitions.
-- See "Algorithms.BF.Main" for an overview of the boolean formula algorithm.
module Algorithms.BF.Testing where

import Algorithms.BF.BooleanFormula
import Algorithms.BF.Hex
import Algorithms.BF.HexBoard
import Quipper
import QuipperLib.Simulation
import QuipperLib.Unboxing

-- * Auxiliary definitions

-- | Convert  list of moves, into a 'HexBoard'.
moves_to_hex :: BooleanFormulaOracle -> [Int] -> HexBoard
moves_to_hex o moves = fromPos o pos
  where pos = moves_to_pos o moves

-- | Convert a list of moves, into a list of positions.
moves_to_pos :: BooleanFormulaOracle -> [Int] -> [[Bool]]
moves_to_pos o moves = map (int2bools (oracle_m o)) moves

-- | Set the position in board, at the given address, to the given boolean.
set_bool :: [Bool] -> [Bool] -> Bool -> [Bool]
set_bool board address value = (take n board) ++ value:(drop (n+1) board)
    where n = bools2int address

-- | Create the description of a Hex board, from the given classical state
-- of a position register from the Boolean Formula algorithm.
fromPos :: BooleanFormulaOracle -> [[Bool]] -> HexBoard
fromPos o pos = fromPos' pos (start_board o) (odd (oracle_s o))
  where
    fromPos' :: [[Bool]] -> HexBoard -> Bool -> HexBoard
    fromPos' [] rb _ = rb
    fromPos' (p:ps) (red,blue) is_red = fromPos' ps (if is_red then (set_bool red p True,set_bool blue p False) else (set_bool red p False,set_bool blue p True)) (not is_red)

-- * Testing various circuits

-- | A dummy value of type 'Double', to feed the type in the simulator.
double :: Double
double = undefined

-- | Construct the oracle circuit, initialized with the given boolean inputs.
oracle_with_input :: BooleanFormulaOracle -> BoolRegister -> Circ BooleanFormulaRegister 
oracle_with_input o input = do
 reg <- qinit input
 oracle o reg
 return reg

-- | Simulate the oracle circuit with the given boolean inputs, to
-- give boolean outputs.
run_oracle_with_input :: BooleanFormulaOracle -> BoolRegister -> IO BoolRegister
run_oracle_with_input oracle input = do
  run_generic_io double (unbox (oracle_with_input oracle input)) 

-- | Return the diffuse circuit, initialized with the given boolean
-- inputs.
diffuse_with_input :: BoolRegister -> Circ BooleanFormulaRegister 
diffuse_with_input input = do
 reg <- qinit input
 diffuse reg
 return reg

-- | Simulate the diffuse circuit with the given boolean inputs, 
-- to give boolean outputs.
run_diffuse_with_input :: BoolRegister -> IO BoolRegister
run_diffuse_with_input input = do
  run_generic_io double (diffuse_with_input input) 

-- | Return the walk circuit, initialized with the given boolean inputs.
walk_with_input :: BoolRegister -> Circ BooleanFormulaRegister 
walk_with_input input = do
 reg <- qinit input
 walk reg
 return reg

-- | Simulate the walk circuit with the given boolean inputs, to give
-- boolean outputs.
run_walk_with_input :: BoolRegister -> IO BoolRegister
run_walk_with_input input = do
  run_generic_io double (walk_with_input input) 

-- | Return the 'undo_oracle' circuit, initialized with the given
-- boolean inputs.
undo_oracle_with_input :: BooleanFormulaOracle -> BoolRegister -> Circ BooleanFormulaRegister
undo_oracle_with_input o input = do
 reg <- qinit input
 undo_oracle o reg
 return reg

-- | Simulate the 'undo_oracle' circuit with the given boolean inputs,
-- to give boolean outputs.
run_undo_oracle_with_input :: BooleanFormulaOracle -> BoolRegister -> IO BoolRegister
run_undo_oracle_with_input oracle input = do
  run_generic_io double (unbox (undo_oracle_with_input oracle input)) 

-- * Oracle, diffuse, walk, and undo_oracle

-- | Create a register from the given boolean inputs,
-- and then run the oracle circuit, followed by the diffusion step,
-- followed by the walk step, and finally the 'undo_oracle' circuit.
-- 
-- This is really a test of all four parts. The return values when
-- running this step can be fed forward into the next iteration, and
-- the 'undo_oracle' step should have returned the eight work qubits
-- back to the initial 'False' states.
-- 
-- We break the simulation into the four separate steps, so that we are
-- not trying to simulate the walk/undo_oracle steps over a quantum state, as
-- this gives us an overhead.
run_odwu_with_input :: BooleanFormulaOracle -> BoolRegister -> IO BoolRegister
run_odwu_with_input o input = do
  oracle_output <- run_oracle_with_input o input
  diffuse_output <- run_diffuse_with_input oracle_output
  walk_output <- run_walk_with_input diffuse_output
  run_undo_oracle_with_input o walk_output

-- | Simulate the /odwu/ circuit, running it /n/ times and passing the
-- output of each iteration as inputs to the next iteration.
-- The overall return value is a representation of the HexBoard at each step of
-- the simulation.
repeat_odwu_n :: Int -> BooleanFormulaOracle -> BoolRegister -> IO [HexBoard]
repeat_odwu_n n oracle input = repeat_odwu_n' n oracle input []
  where
    repeat_odwu_n' 0 _ _ accum = return (reverse accum)
    repeat_odwu_n' n oracle input accum = do
      output <- run_odwu_with_input oracle input
      let flags = position_flags output
      let pos = position output
      let hexboard = start_board (update_start_board oracle (fromPos oracle (tidy flags pos)))
      repeat_odwu_n' (n-1) oracle output (hexboard:accum)

-- | Simulate the /odwu/ circuit, running it repeatedly and passing
-- the output of each iteration as inputs to the next iteration.
-- Outputs an ASCII representation of the position register/board after each step.
repeat_odwu_infinite :: BooleanFormulaOracle -> BoolRegister -> IO ()
repeat_odwu_infinite oracle input = do
  output <- run_odwu_with_input oracle input
  let flags = position_flags output
  let pos = position output
  putStrLn "Position Register: "
  putStr (show ((\(l,p) -> [if l then 'L' else ' ',if p then 'P' else ' ']) flags))
  putStr " : "
  putStrLn (show (map bools2int pos)) 
  output_start_board ASCII (update_start_board oracle (fromPos oracle (tidy flags pos)))
  repeat_odwu_infinite oracle output

-- | Trim any leading zeroes from a pos register, 
-- and a single leading 1, if we're not at a paraleaf,
-- and a 3, if we're at the root.
tidy :: (Bool,Bool) -> [[Bool]] -> [[Bool]]
tidy flags pos = if pos == (zeroes ++ [three]) then [] else tidy' flags pos
  where
    zeroes = replicate (length pos - 1) (replicate (length (head pos)) False)
    three = (replicate (length (head pos) - 2) False) ++ [True,True]
    tidy' _ [] = []
    tidy' (l,p) (a:as) = case (a == replicate (length a) False) of
      True -> tidy' (l,p) as
      False -> case (a == (replicate (length a - 1) False) ++ [True]) of
        False -> a:as
        True -> if p then (a:as) else as

-- | Return the 'Hex' circuit, initialized for the given oracle, with the given 
-- boolean inputs.
hex_with_input :: BooleanFormulaOracle -> BoolRegister -> Circ Qubit
hex_with_input oracle input = do
    let init = start_board oracle
    let s = oracle_s oracle
    let x_max = oracle_x_max oracle
    reg <- qinit input
    let pos = position reg
    let binary = work_binary reg
    (_,binary') <- hex_oracle init s x_max (pos,binary)
    return binary'

-- | Simulate the running of the 'Hex' circuit, initialized for the given oracle, 
-- with the given boolean inputs.
run_hex_with_input :: BooleanFormulaOracle -> BoolRegister -> IO Bool
run_hex_with_input oracle input = run_generic_io double (hex_with_input oracle input)

-- | Simulate the running of the 'checkwin_red' subroutine for the
-- given oracle, and keep track of the state of certain \"traced\" qubits within that 
-- subroutine, which represent the Hex board at each iteration of the while loop in
-- the 'flood_fill' algorithm.
checkwin_trace :: BooleanFormulaOracle -> IO [[Bool]]
checkwin_trace o = do
 let circuit = hex_with_input o (createRegister o)
 trace <- run_generic_trace_io double circuit 
 --  trace :: [QuantumTrace] = [Vector Double [Bool]] = [Vector [([Bool],Double)]]
 let boards = map (\(Vector [(bs,_)]) -> bs) trace
 return boards


