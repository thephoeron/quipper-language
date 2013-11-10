-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | This module contains the implementation of the various quantum circuits
-- that make up the boolean formula algorithm. Please see "Algorithms.BF.Main"
-- for an overview of the boolean formula algorithm.

module Algorithms.BF.BooleanFormula where

import Quipper
import Quipper.Internal
import Algorithms.BF.QuantumIf
import Algorithms.BF.Hex
import QuipperLib.QFT 
import QuipperLib.Simulation
import QuipperLib.Decompose

import Libraries.Auxiliary (mmap)

import Data.Typeable

-- ----------------------------------------------------------------------
-- * Classical data structures

-- ** Oracle description

-- $ We define a data structure to hold the various parameters that
-- are used to define an oracle.

-- | The input to the BF Algorithm is the description of an oracle to
-- represent a given size of hex board, and a given size for the phase
-- estimation register.
data BooleanFormulaOracle = BFO {
  oracle_x_max :: Int,	 -- ^ The /x/-dimension of hex board.
  oracle_y_max :: Int,	 -- ^ The /y/-dimension of hex board.
  oracle_t :: Int, 	 -- ^ Size of phase estimation register.
        
  -- The number of moves remaining can
  -- depend on the starting state of the HexBoard
  oracle_s :: Int,	 -- ^ Number of moves remaining.
                         -- This should start as /x/⋅/y/, if no moves have been made.
  oracle_m :: Int,	 -- ^ Size of the direction register,
                         -- i.e., size of labels on the BF tree.
                         -- This should be the ceiling of log(/x/⋅/y/).

   
  start_board :: HexBoard, -- ^ A description of the starting state of the
                           -- board, and can be used to calculate /s/.
  oracle_hex :: HexCircuit -- ^ An extra flag that we can use so that different
                           -- HEX circuits can be used instead of the full circuit.

} 

-- | A type to define which Hex circuit to use.
data HexCircuit = Hex      -- ^ The actual Hex circuit.
                | Dummy    -- ^ A Dummy Hex circuit.
                | EmptyHex -- ^ Nothing.

-- | Create an oracle description. This only requires /x/, /y/, and
-- /t/ to be specified, as the remaining values can be calculated. The number of
-- moves remaining, /s/, is calculated as the total number of squares on the board, 
-- and /m/ is calculated as the number of bits required to represent /s/+1.
createOracle :: Int -> Int -> Int -> BooleanFormulaOracle
createOracle x y t = BFO {
	oracle_x_max = x,
	oracle_y_max = y,
 	oracle_t = t,
	oracle_s = s,
	oracle_m = m,
        start_board = (empty,empty),
        oracle_hex = Hex
} where s = x * y
        m = ceiling (log (fromIntegral (s+1)) / log 2)
        empty = replicate s False

-- | A function to set the \"Dummy\" flag in the given oracle to the given 
-- 'HexCircuit' value.
update_hex :: BooleanFormulaOracle -> HexCircuit -> BooleanFormulaOracle
update_hex bfo hex = bfo {oracle_hex = hex}

-- | Update the 'start_board' in the given oracle, with the given 'HexBoard'. This
-- also updates the 'oracle_s' field of the oracle to be in line with
-- the new 'start_board'.
update_start_board :: BooleanFormulaOracle -> HexBoard -> BooleanFormulaOracle
update_start_board bfo start = bfo {
  oracle_s = s,
  start_board = start
 } where
    x = oracle_x_max bfo
    y = oracle_y_max bfo
    s = (x*y) - (moves_made start)

-- | An oracle for a 9 by 7 Hex board, with the parameters:
-- /x/=9, /y/=7, /t/=189. The calculated values are: /s/=63, /m/=6.
full_oracle :: BooleanFormulaOracle
full_oracle = createOracle 9 7 189

-- | A smaller oracle for testing purposes. The numbers should be
-- chosen such that /x/⋅/y/ = 2[sup /n/]−1 for some /n/. Here, we set
-- /x/=3 and /y/=5, to give /x/⋅/y/=15. We arbitrarily set the size of
-- the phase estimation register to /t/=4.
test_oracle :: BooleanFormulaOracle
test_oracle = createOracle 5 3 4

-- ** Hex boards

-- | A hex board is specified by a pair of lists of booleans.  For a
-- board of size /x/ by /y/, each list should contain /x/⋅/y/
-- elements.  The first list is the \"blue\" bitmap, and the second is
-- the \"red\" maskmap.
type HexBoard = ([Bool],[Bool])

-- | A function to determine how many moves have been made on a given HexBoard.
-- This function assumes that the given 'HexBoard' is valid, in the sense that
-- no duplicate moves have been made.
moves_made :: HexBoard -> Int
moves_made (blue,red) = moves blue + moves red
  where moves color = length (filter id color)

-- | A function to determine which spaces are still empty in the given HexBoard.
-- This function assumes that the given 'HexBoard' is valid, in the sense that
-- no duplicate moves have been made. This function will return a list of all the 
-- empty spaces remaining, in strictly increasing order.
empty_spaces :: HexBoard -> [Int]
empty_spaces (blue,red) = empty_spaces' blue red 0
  where
   empty_spaces' [] [] _ = []
   empty_spaces' [] _ _ = error "empty_spaces: Red and Blue boards of different length"
   empty_spaces' _ [] _ = error "empty_spaces: Red and Blue boards of different length"
   empty_spaces' (b:bs) (r:rs) n = if (b || r) then rest else (n:rest)
     where rest = empty_spaces' bs rs (n+1)

-- ----------------------------------------------------------------------
-- * Quantum data structures

-- $ Some data structures to help in defining the algorithm.

-- | The phase estimation register is a simple register of qubits. This is kept
-- separate from the rest of the 'BooleanFormulaRegister' as it is this register
-- which will be measured at the end of the algorithm.
type PhaseEstimationRegister = [Qubit]

-- | The direction register is a simple register of qubits, 
--   made explicit here so we can see that a \"position\" is a list of directions.
type GenericDirectionRegister a = [a]

-- | A type synonym defined as the 'Qubit' instance of a
-- 'GenericDirectionRegister'.
type DirectionRegister = GenericDirectionRegister Qubit

-- | The rest of the boolean formula algorithm requires a register which is 
-- split into 3 main parts.
data GenericBooleanFormulaRegister a = BFR {
     -- | The position register is split into two parts:
     -- the leaf and paraleaf \"flags\".
     position_flags :: (a,a),
       -- | The current position, and how we got there, i.e., directions we followed.
       -- Any position can be reached by at most /x/⋅/y/ directions.
     position :: [GenericDirectionRegister a],
     work_leaf :: a,     
     work_paraleaf :: a, 
     work_binary :: a,        
     work_height :: a,   
     work_r :: a,        
     work_rp :: a,       
     work_rpp :: a,       -- ^ Seven flags that make up the work register.  
     direction :: GenericDirectionRegister a  -- ^ The direction register.
}
  deriving (Typeable, Show)

-- | A type synonym defined as the 'Qubit' instantiation of a 
-- 'GenericBooleanFormulaRegister'.
type BooleanFormulaRegister = GenericBooleanFormulaRegister Qubit

-- | A function to add labels to the wires that make up a 'BooleanFormulaRegister'.
-- These labels correspond to the parts of the register. 
labelBFR :: BooleanFormulaRegister -> Circ ()
labelBFR reg = do
  let tuple = toTuple reg
  label tuple (("pos-leaf","pos-paraleaf"),
               "pos",
               ("leaf","paraleaf","binary","height","r","rp","rpp"),
                "dir")

-- | A type synonym defined as the 'Bool' instantiation of a 
-- 'GenericBooleanFormulaRegister'.
type BoolRegister = GenericBooleanFormulaRegister Bool

-- | Helper function to simplify the 'QCData' instance for 'BooleanFormulaRegister'. 
-- Create a tuple from a 'GenericBooleanFormulaRegister'.
toTuple :: GenericBooleanFormulaRegister a -> ((a,a),[[a]],(a,a,a,a,a,a,a),[a])
toTuple r = (position_flags r,position r,(work_leaf r,work_paraleaf r,work_binary r,work_height r,work_r r,work_rp r,work_rpp r),direction r)

-- | Helper function to simplify the 'QCData' instance for 'BooleanFormulaRegister'. 
-- Create a 'GenericBooleanFormulaRegister' from a tuple.
fromTuple :: ((a,a),[[a]],(a,a,a,a,a,a,a),[a]) -> GenericBooleanFormulaRegister a 
fromTuple (pf,p,(wl,wp,wb,wh,wr,wrp,wrpp),d) = BFR {
  position_flags = pf,
  position = p,
  work_leaf = wl,
  work_paraleaf = wp,
  work_binary = wb,
  work_height = wh,
  work_r = wr,
  work_rp = wrp,
  work_rpp = wrpp,
  direction = d
  }

type instance QCType x y (GenericBooleanFormulaRegister a) = GenericBooleanFormulaRegister (QCType x y a)
type instance QTypeB (GenericBooleanFormulaRegister a) = GenericBooleanFormulaRegister (QTypeB a) 
instance QCData a => QCData (GenericBooleanFormulaRegister a) where
  qcdata_mapM s f g xs = mmap fromTuple $ qcdata_mapM (toTuple s) f g (toTuple xs)
  qcdata_zip s q c q' c' xs ys e = fromTuple $ qcdata_zip (toTuple s) q c q' c' (toTuple xs) (toTuple ys) e
  qcdata_promote a x s = fromTuple $ qcdata_promote (toTuple a) (toTuple x) s
instance (Labelable a String) => Labelable (GenericBooleanFormulaRegister a) String where
  label_rec r s = do
    label_rec (position_flags r) s `dotted_indexed` "posflag"
    label_rec (position r) s       `dotted_indexed` "pos"
    label_rec (work_leaf r) s      `dotted_indexed` "leaf"
    label_rec (work_paraleaf r) s  `dotted_indexed` "paraleaf"
    label_rec (work_binary r) s    `dotted_indexed` "binary"
    label_rec (work_height r) s    `dotted_indexed` "height"
    label_rec (work_r r) s         `dotted_indexed` "r"
    label_rec (work_rp r) s        `dotted_indexed` "rp"
    label_rec (work_rpp r) s       `dotted_indexed` "rpp"
    label_rec (direction r) s      `dotted_indexed` "dir"

-- | Create an initial classical 'BooleanFormulaRegister' for a given oracle description.
-- The /position/ register is initialized in the /zero/ state that represents being
-- at label /zero/, or node /rpp/ in the tree. The work qubits are all initialized to
-- /zero/, as the first call to the /oracle/ circuit will set them accordingly for
-- the /position/ we are currently in. The /direction/ register is also set to /zero/
-- as this is the direction in which the node /rp/ is in. The given
-- 'BooleanFormulaOracle' is used to make sure the registers are of the correct
-- size, i.e., number of qubits.
createRegister :: BooleanFormulaOracle -> BoolRegister
createRegister oracle = BFR {
  position_flags = (False,False),
  position = replicate s (replicate m False),
  work_leaf = False,
  work_paraleaf = False,
  work_binary = False,
  work_height = False,
  work_r = False,
  work_rp = False,
  work_rpp = False,
  direction = replicate m False        
  } where
     s = oracle_s oracle
     m = oracle_m oracle

-- | Create a shape parameter for a 'BooleanFormulaRegister' of the
-- correct size.
registerShape :: BooleanFormulaOracle -> BooleanFormulaRegister     
registerShape oracle = qshape (createRegister oracle)

-- | Initialize a 'BooleanFormulaRegister' from a 'BooleanFormulaOracle'. 
initializeRegister :: BooleanFormulaOracle -> Circ BooleanFormulaRegister
initializeRegister oracle = qinit (createRegister oracle)

-- ======================================================================
-- * Oracle implementation

-- $ The functions in this implementation follow a separation of the boolean
-- formula algorithm into two parts. The first part corresponds to the 
-- algorithms defined in this module. The second part consists of the 
-- algorithms defined in "Algorithms.BF.Hex". This separation relates to the 
-- first part defining the quantum parts of the algorithm, including the 
-- phase estimation, and the quantum walk, whereas the remaining four define 
-- the classical implementation of the circuit for determining which player 
-- has won a completed game of Hex, which is converted to a quantum circuit 
-- using Quipper's \"build_circuit\" keyword.
--
-- Note that the circuits for the algorithms in this module have been tested
-- for performing a quantum walk on the tree defined for a given oracle (but 
-- with a dummy function taking the place of the call to HEX).

-- | The overall Boolean Formula Algorithm. It initializes the
-- phase estimation register into an equal super-position of all 2[sup t] states,
-- and the other registers as defined previously. It then maps the exponentiated
-- version of the unitary /u/, as per phase estimation, before applying the 
-- inverse QFT, and measuring the result.
qw_bf :: BooleanFormulaOracle -> Circ [Bit]
qw_bf oracle = do
    -- initialize the phase estimation register, 
    -- and put it in an equal super-position
    let t = oracle_t oracle
    a <- qinit (replicate t False)
    label a "a"
    a <- mapUnary hadamard a
    -- initialize the other boolean formula registers
    b <- initializeRegister oracle  
    labelBFR b
    -- we can use a separate recursive function to map the exp_u algorithm over a 
    let t = oracle_t oracle  
    map_exp_u oracle a b (t-1)
    -- qft is defined, so we reverse it to get inverse qft 
    a <- (subroutine_inverse_qft oracle) a 
    -- we're only interested in the result of measuring a, 
    -- so we can discard all the qubits in the rest of the register
    qdiscard b 
    measure a

-- | The inverse quantum Fourier transform as a boxed subroutine.
subroutine_inverse_qft :: BooleanFormulaOracle -> [Qubit] -> Circ [Qubit]
subroutine_inverse_qft o = box "QFT*" (reverse_generic_endo qft_little_endian)  

-- | \"Map\" the application of the exponentiated unitary /u/
-- over the phase estimation register. That is, each qubit in the phase estimation
-- register is used as a control over a call to the unitary /u/, exponentiated to
-- the appropriate power.
map_exp_u :: BooleanFormulaOracle -> [Qubit] -> BooleanFormulaRegister -> Int -> Circ ()
map_exp_u _ [] _ _ = return ()
map_exp_u o (a:as) b l = do
    let x_max = oracle_x_max o
    -- we can move the control out of the exp_u function
    exp_u o (2^(l-(length as))) b `controlled` a 
    map_exp_u o as b l

-- | Exponentiate the unitary /u/. In this implementation, this is
-- achieved by repeated application of /u/.
exp_u :: BooleanFormulaOracle -> Integer -> BooleanFormulaRegister -> Circ ()
exp_u _ 0 _ = return ()
exp_u o n_steps b = do
    (subroutine_u o) b
    exp_u o (n_steps-1) b

-- | The unitary /u/ represents a single step in the walk on the NAND tree. A call
-- to the oracle determines what type of node we are at (so we know which directions
-- are valid to step to), the call to diffuse sets the direction register to be a
-- super-position of all valid directions, the call to walk performs the step, and then
-- the call to undo oracle has to clean up the work registers that were set by the
-- call to the oracle. Note that the undo oracle step is not simply the inverse of the
-- oracle, as we have walked since the oracle was called.
u :: BooleanFormulaOracle -> BooleanFormulaRegister -> Circ ()
u o b = do
    comment "U"
    labelBFR b
    (subroutine_oracle o) b
    (subroutine_diffuse o) b
    (subroutine_walk o) b
    (subroutine_undo_oracle o) b 

-- | The circuit for 'u' as a boxed subroutine.
subroutine_u :: BooleanFormulaOracle -> BooleanFormulaRegister -> Circ ()
subroutine_u o = box "U" (u o)

-- | Call the oracle to determine some extra information about where
-- we are in the tree. Essentially, the special cases are when were are at one of
-- the three \"low height\" nodes, or when we are at a node representing a complete 
-- game of Hex, and we need to determine if this is a leaf, by calling the hex circuit,
-- which determines whether the node represents a completed game of hex in which
-- the red player has won.  
oracle :: BooleanFormulaOracle -> BooleanFormulaRegister -> Circ ()
oracle o register = do
    comment "ORACLE"
    labelBFR register
    let init = start_board o
    let x_max = oracle_x_max o
    let (is_leaf,is_paraleaf) = position_flags register  
    with_controls (is_leaf) 
     ( -- if is_leaf
       -- we are at a leaf node, so set "leaf"
      do
      let leaf = work_leaf register
      qnot_at leaf
     )
    with_controls (is_leaf .==. False .&&. is_paraleaf .==. True)
     ( -- else if is_paraleaf
       -- we are at a paraleaf node, so set "paraleaf"                          
      do
      let paraleaf = work_paraleaf register
      qnot_at paraleaf
      let binary = work_binary register
      qnot_at binary
      let pos = position register
      let hex_subroutine = case oracle_hex o of
                            Hex -> box "HEX" (hex_oracle init (oracle_s o) x_max)
                            Dummy -> hex_oracle_dummy 
                            EmptyHex -> \x -> return x 
      -- hex sets "binary" flag depending on whether the paraleaf is attached to a
      -- a leaf, i.e., whether red has won or lost the game of hex.
      hex_subroutine (pos,binary)
      return ()
     )
    with_controls (is_leaf .==. False .&&. is_paraleaf .==. False)
     ( -- else
       -- we're not at a leaf node, or paraleaf node
      do      
      let pos = position register
      -- are we at a "low height" node?
      with_controls (controls is_paraleaf pos)
       ( -- we're at a "low height" node
        do
        let pos'' = pos !! (length pos - 2)
        let pos_m = last pos''
        with_controls pos_m
         ( -- if pos_m == 1
          do
          let height = work_height register
          qnot_at height
         )
        let pos' = last pos 
        let pos_1 = pos' !! (length pos' - 2)
        with_controls (pos_m .==. False .&&. pos_1 .==. True)
         ( -- else if pos_1 == 1
          do
          let r = work_r register
          qnot_at r
         )
        let pos_0 = last pos'
        with_controls (pos_m .==. False .&&. pos_1 .==. False .&&. pos_0 .==. True)
         ( -- else if pos_0 == 1
          do
          let rp = work_rp register
          qnot_at rp
          let binary = work_binary register
          qnot_at binary
         )
        with_controls (pos_m .==. False .&&. pos_1 .==. False .&&. pos_0 .==. False)
         ( -- else
          do
          let rpp = work_rpp register
          qnot_at rpp
         )  
       )
     )

-- | The circuit for the 'oracle' as a boxed subroutine.
subroutine_oracle :: BooleanFormulaOracle -> BooleanFormulaRegister -> Circ ()
subroutine_oracle o = box "Oracle" (oracle o)

-- | The controls to use, to see if we're at a \"low height\" node.
controls :: Qubit -> [DirectionRegister] -> [ControlList]
controls is_paraleaf pos = (is_paraleaf .==. False) : ctrls pos
    where ctrls [] = []
          ctrls [p] = []
          ctrls [p,q] = []
          ctrls (p:ps) = (last p .==. False) : ctrls ps

-- | Diffuse the direction register, to be a super-position of all valid
-- directions from the current node. Note, that this implementation of the boolean
-- formula algorithm does not applying the correct weighting scheme to the NAND graph,
-- which would require this function to diffuse with respect to the weighting scheme.
diffuse :: BooleanFormulaRegister -> Circ ()
diffuse register = do
    comment "DIFFUSE"
    labelBFR register
    let binary = work_binary register
    let dir = direction register
    with_controls binary
     ( -- if binary == 1
      do
      let dir_0 = last dir
      hadamard_at dir_0 
     )
    let leaf = work_leaf register
    let rpp = work_rpp register     
    with_controls (binary .==. False .&&. leaf .==. False .&&. rpp .==. False)
     ( -- else (controlled on binary == 0, leaf == 0, rpp == 0)
      do
      mapUnary hadamard dir
     )
    return ()

-- | The circuit for 'diffuse' as a boxed subroutine.
subroutine_diffuse :: BooleanFormulaOracle -> BooleanFormulaRegister -> Circ ()
subroutine_diffuse o = box "Diffuse" diffuse

-- | A datatype to use instead of passing integers to 'toParent' and 'toChild'
-- to define what needs to be shifted. This is used as only three different
-- shift widths are ever used in the algorithm.
data Where = Width -- ^ corresponds to shifting all qubits.
           | M     -- ^ corresponds to shifting only /m/+1 qubits.
           | M2    -- ^ corresponds to shifting only 2/m/+1 qubits.
      deriving Eq

-- | Define a step on the NAND graph, in the direction specified 
-- by the direction register, and updates the direction register to be where
-- we have stepped from.
-- For this algorithm we have developed the 'if_then_elseQ' construct, which
-- gives us a nice way of constructing if/else statements acting on
-- \"boolean statements\" over qubits (see "Algorithms.BF.QuantumIf").
walk :: BooleanFormulaRegister -> Circ ()
walk register = do
    comment "WALK"
    labelBFR register
    let leaf = work_leaf register
    let paraleaf = work_paraleaf register
    let dir = direction register
    let dir_0 = last dir
    let (is_leaf,is_paraleaf) = position_flags register    
    let pos = position register
    let pos_0 = last (last pos)
    let pos_1 = last (init (last pos))
    let height_1 = work_height register
    let rpp = work_rpp register
    let rp = work_rp register
    let r = work_r register
    let dir_all_1 = foldr1 (\x y -> And x y) (map A dir)
    let boolean_statement_in = Or (A leaf) (And (A paraleaf) (Not (A dir_0)))
    let boolean_statement_out = Or (A leaf) (And (A paraleaf) (A is_leaf))
    if_then_elseQinv boolean_statement_in
     ( -- if leaf == 1 or (paraleaf == 1 and dir_0 == 0)
      do
      qnot_at is_leaf
     )
     ( -- else (leaf == 0 and (paraleaf == 0 or dir_0 == 1))
      do
      let boolean_statement_in = And (A paraleaf) (A dir_0)
      let boolean_statement_out = And (A paraleaf) (Not (dir_all_1))
      if_then_elseQinv boolean_statement_in 
       ( -- if paraleaf == 1 and dir_0 == 1
        toParent Width register
        -- now, dir /= 1..1, so dir_0 could be either 0 or 1
       )
       ( -- else (paraleaf == 0 or dir_0 == 0)
        do
        let boolean_statement_in = Or (A rpp) (And (A rp) (A dir_0))
        let boolean_statement_out = Or (A rpp) (And (A rp) (Not (A dir_0)))
        if_then_elseQinv boolean_statement_in
         ( -- if rpp == 1 or (rp == 1 and dir_0 == 1 )
          do
          qnot_at pos_0
          -- dir_0 should be changed,
          -- as we're moving from rp to rpp, and rpp only has a child at 0
          -- or we're moving from rpp to rp, and dir_0 should be set to 1 as
          -- we have come from a parent 
          qnot_at dir_0
         )
         ( -- else (rpp == 0 and (rp == 0 or dir_0 == 0))
          do
          let boolean_statement_in = Or (And (A rp) (Not (A dir_0))) (And (A r) dir_all_1)
          let pos_m = last (last (init pos))         
          let boolean_statement_out = Or (And (A rp) dir_all_1) (And (A r) (And (Not dir_all_1) (Not (A pos_m))))
          if_then_elseQinv boolean_statement_in
           ( -- if (rp == 1 and dir_0 == 0) or (r == 1 and dir == 1..1)
            do
            qnot_at pos_1
            -- we know that pos_m == 0
            -- dir is should be changed
            -- when we move from rp to r, and when we move from r to rp
            mapUnary qnot dir
            return ()
           )
           ( -- else ((rp == 0 or dir_0 == 1) and (r == 0 or dir /= 1..1))
            do
            let boolean_statement = A r
            if_then_elseQ boolean_statement
             ( -- if r == 1
              do
              qnot_at pos_1
              toChild M register
              -- now dir == 1..1
              -- we also know that pos_m == 1
             )
             ( -- else
              do
              let boolean_statement_in = And (A height_1) (dir_all_1)
              let boolean_statement_out = And (A height_1) (Not dir_all_1)
              if_then_elseQinv boolean_statement_in
               ( -- if height_1 == 1 and dir == 1..1
                do
                toParent M register
                qnot_at pos_1
                -- now, dir /= 1..1
               )
               ( -- else height_1 == 0 or dir /= 1..1
                do
                let boolean_statement = A height_1
                if_then_elseQ boolean_statement
                 ( -- if height_1 == 1    (and dir /= 1..1)
                  do
                  toChild M2 register
                  -- now dir == 1..1
                 )
                 ( -- else (if height_1 == 0)
                  do
                  let boolean_statement_in = dir_all_1
                  let boolean_statement_out = Not dir_all_1
                  if_then_elseQinv boolean_statement_in
                   ( -- if dir = 1..1
                     do
                     toParent Width register
                     -- now dir /= 1..1
                   )
                   ( --else (dir /= 1..1)
                     do
                     toChild Width register
                     -- now dir == 1..1
                   ) boolean_statement_out                   
                 )
               ) boolean_statement_out
             )
           ) boolean_statement_out
         ) boolean_statement_out
       ) boolean_statement_out
     ) boolean_statement_out  
    return ()

-- | The circuit for 'walk' as a boxed subroutine.
subroutine_walk :: BooleanFormulaOracle -> BooleanFormulaRegister -> Circ ()
subroutine_walk o = box "Walk" walk

-- | Uncompute the various flags that were set by the initial call
-- to the oracle. It has to uncompute the flags depending on where we were before
-- the walk step, so isn't just the inverse of the oracle.
undo_oracle :: BooleanFormulaOracle -> BooleanFormulaRegister -> Circ ()
undo_oracle o register = do
    comment "UNDO_ORACLE"
    labelBFR register
    let initHB = start_board o
    let x_max = oracle_x_max o
    let paraleaf = work_paraleaf register
    let (is_leaf,is_paraleaf) = position_flags register
    with_controls paraleaf
     ( do
       let binary = work_binary register
       let pos = position register
       let dir = direction register
       let hex_subroutine = case oracle_hex o of
                             Hex -> box "HEX" (hex_oracle initHB (oracle_s o) x_max)
                             Dummy -> hex_oracle_dummy 
                             EmptyHex -> \x -> return x 
       hex_subroutine (pos,binary) 
       return ()
     )
    let leaf = work_leaf register
    let dir = direction register
    let dir_0 = last dir
    let boolean_statement = And (Not (A is_leaf)) (And (A is_paraleaf) (Not (A dir_0)))
    if_then_elseQ boolean_statement
     ( -- if is_leaf == 0 and is_paraleaf == 1 and dir_0 == 0
       -- we went from a leaf to a paraleaf, so we can unset leaf
      do
      qnot_at leaf
     )
     ( -- else
      do
      let binary = work_binary register
      let pos = position register
      let pos_w_2_m = last (head pos)
      let dir_all_1 = foldr1 (\x y -> And x y) (map A dir)
      let boolean_statement = Or (A is_leaf) (And (Not (A is_leaf)) (And (Not (A is_paraleaf)) (And (A pos_w_2_m) (Not (dir_all_1)))))
      if_then_elseQ boolean_statement
       ( -- if is_leaf == 1 or (is_leaf == 0 and is_paraleaf == 0 and pos_w_2_m == 1 and dir /= 1..1)
        -- we went from a paraleaf to a leaf, so unset binary and paraleaf
        -- or we went from a paraleaf to its parent...
        do
        qnot_at binary
        qnot_at paraleaf
       )
       ( -- else
        do
        with_controls (init (controls is_paraleaf pos))
         ( -- if pos_sm,pos_(s-1)m,...,3. == 00...0
          do
          let height = work_height register
          let r = work_r register
          let rp = work_rp register
          let pos_0 = last (last pos)
          let pos_1 = last (init (last pos))
          let pos_m = last (last (init pos))
          let pos_2m = last (last (init (init pos)))
          let boolean_statement = dir_all_1
          if_then_elseQ boolean_statement
           ( -- if dir = 1...1
            do
            qnot_at height `controlled` pos_2m
            qnot_at r `controlled` (pos_2m .==. False .&&. pos_m .==. True)
            with_controls (pos_2m .==. False .&&. pos_m .==. False .&&. pos_1 .==. True)
             (
              do
              qnot_at rp
              qnot_at binary
             )
           )
           ( -- else
             with_controls (pos_2m .==. False .&&. pos_m .==. False)
             (
              do
              let rpp = work_rpp register 
              qnot_at height `controlled` pos_1
              qnot_at rpp `controlled` (pos_1 .==. False .&&. dir_0 .==. True)
              qnot_at r `controlled` (pos_1 .==. False .&&. dir_0 .==. False .&&. pos_0 .==. True)
              with_controls (pos_1 .==. False .&&. dir_0 .==. False .&&. pos_0 .==. False)
               (
                do
                qnot_at rp
                qnot_at binary
               )
             )
           )
         ) -- end if
       )
     )
    return ()

-- | The circuit for 'undo_oracle' as a boxed subroutine.
subroutine_undo_oracle :: BooleanFormulaOracle -> BooleanFormulaRegister -> Circ ()
subroutine_undo_oracle o = box "Undo Oracle" (undo_oracle o)

-- | Define the circuit that updates the position register to be the
-- parent node of the current position.
toParent :: Where -> BooleanFormulaRegister -> Circ ()
toParent M2 _ = error "TOPARENT should never be called with 2m+1 as width"
toParent w register = do
    let pos = position register :: [[Qubit]] -- of length x*y
    let pos_firstM = last pos :: [Qubit] -- of length m
    let pos_secondM = last (init pos) :: [Qubit] -- of length m  
    let pos_0 = last pos_firstM :: Qubit
    let pos_m = last pos_secondM :: Qubit
    let dir = direction register :: [Qubit] -- of length m
    let (_,is_paraleaf) = position_flags register :: (Qubit,Qubit)
    mapUnary qnot dir
    mapBinary copy_from_to (reverse pos_firstM) (reverse dir)
    if (w == Width) then
     ( do -- width
       -- we need to shift everything to the right by m 
       shift_right pos
       -- we need to shift is_paraleaf to x*y*m
       copy_from_to is_paraleaf (last (head pos))
       return ()
     ) else return ()
    if (w == M) then
     ( do -- m+1
       -- we need to "shift" pos_m to pos_0
       copy_from_to pos_m pos_0
       return ()      
     ) else return ()

-- | @'copy_from_to' a b@: Sets the state of qubit /b/ to be the state of qubit /a/,
--   (and the state of /a/ is lost in the process, so this is not cloning).
--   It falls short of swapping /a/ and /b/, as we're not interested in preserving /a/.
copy_from_to :: Qubit -> Qubit -> Circ (Qubit,Qubit)
copy_from_to from to = do
    qnot_at to `controlled` from
    qnot_at from `controlled` to
    return (from,to)

-- | Define the circuit that updates the position register to be the
-- child node of the current position.
toChild :: Where -> BooleanFormulaRegister -> Circ ()
toChild w register = do
    let pos = position register :: [[Qubit]] -- of length x*y
    let pos_firstM = last pos :: [Qubit] -- of length m
    let pos_secondM = last (init pos) :: [Qubit] -- of length m  
    let pos_thirdM = last (init (init pos)) :: [Qubit] -- of length m
    let pos_0 = last pos_firstM :: Qubit
    let pos_m = last pos_secondM :: Qubit
    let pos_2m = last pos_thirdM :: Qubit
    let dir = direction register :: [Qubit] -- of length m
    let (_,is_paraleaf) = position_flags register :: (Qubit,Qubit)
    if (w == Width) then
     ( do -- width
       -- we need to "shift" x*y*m to is_paraleaf
       copy_from_to (last (head pos)) is_paraleaf
       -- we need to "shift" everything to the left by "m"
       shift_left pos
     ) else return ()
    if (w == M2) then
     ( do -- 2m+1
       -- we need to "shift" pos_m to pos_2m
       copy_from_to pos_m pos_2m
       -- we need to "shift" 0.. to m..  to 
       shift_left [pos_secondM,pos_firstM]
     ) else return ()
    if (w == M) then
     ( do
       -- we need to "shift" pos_0 to pos_m
       copy_from_to pos_0 pos_m
       return ()
     ) else return ()     
    mapBinary copy_from_to dir pos_firstM
    mapUnary qnot dir
    return ()

-- | Shift every qubit in a register to the left by one. 
shift_left :: [DirectionRegister] -> Circ ()
shift_left [] = return ()
shift_left [d] = return ()
shift_left (d:d':ds) = do
    mapBinary copy_from_to d' d
    shift_left (d':ds)

-- | Shift every qubit in a register to the right by one.
shift_right :: [DirectionRegister] -> Circ ()
shift_right [] = return ()
shift_right [d] = return ()
shift_right (d:d':ds) = do
    shift_right (d':ds)
    mapBinary copy_from_to (reverse d) (reverse d')
    -- the arguments are reversed to give a nice symmetry to the circuits
    -- and should be equivalent to if they're not reversed
    return ()

-- ----------------------------------------------------------------------
-- * Possible main functions

-- $ The following functions define various \main\ functions that can be called
-- from an overall \main\ function to display various parts of the
-- overall Boolean Formula Algorithm. The Boolean 
-- Formula Algorithm is split into 13 sub-algorithms, each of which can be
-- displayed separately, or in various combinations.

-- | Displays the overall Boolean Formula circuit for a given oracle description.
main_circuit :: Format -> GateBase -> BooleanFormulaOracle -> IO ()
main_circuit f g oracle = print_simple f (decompose_generic g (qw_bf oracle))

-- | Display just 1 time-step of the given oracle,
--   i.e., one iteration of the 'u' from 'exp_u', with no controls.
main_u :: Format -> GateBase -> BooleanFormulaOracle -> IO ()
main_u f g o = print_generic f (decompose_generic g (u o)) (registerShape o)

-- | Display just 1 time-step of the 'walk' algorithm for the given oracle,
--   i.e., one iteration of /walk/, with no controls.
main_walk :: Format -> GateBase -> BooleanFormulaOracle -> IO ()
main_walk f g o = print_generic f (decompose_generic g walk) (registerShape o)

-- | Display just 1 time-step of the 'diffuse' algorithm for the given oracle,
--   i.e., one iteration of /diffuse/, with no controls.
main_diffuse :: Format -> GateBase -> BooleanFormulaOracle -> IO ()
main_diffuse f g o = print_generic f (decompose_generic g diffuse) (registerShape o)

-- | Display just 1 time-step of the 'oracle' algorithm for the given oracle,
--   i.e., one iteration of /oracle/, with no controls.
main_oracle :: Format -> GateBase -> BooleanFormulaOracle -> IO ()
main_oracle f g o = print_generic f (decompose_generic g (oracle o)) (registerShape o)

-- | Display just 1 time-step of the 'undo_oracle' algorithm for the given oracle,
--   i.e., one iteration of /undo_oracle/, with no controls.
main_undo_oracle :: Format -> GateBase -> BooleanFormulaOracle -> IO ()
main_undo_oracle f g o = print_generic f (decompose_generic g (undo_oracle o)) (registerShape o)

-- | Display the circuit for the Hex algorithm, for the given oracle,
-- i.e., one iteration of 'hex_oracle', with no controls.
main_hex :: Format -> GateBase -> BooleanFormulaOracle -> IO ()
main_hex f g o = print_generic f (decompose_generic g (hex_oracle init s x_max)) (pos,binary)
  where
    init = start_board o
    s = oracle_s o
    x_max = oracle_x_max o
    reg = registerShape o
    pos = position reg
    binary = work_binary reg

-- | Display the circuit for the Checkwin_red algorithm, for the given oracle,
-- i.e., one iteration of 'checkwin_red_circuit', with no controls.
main_checkwin_red :: Format -> GateBase -> BooleanFormulaOracle -> IO ()
main_checkwin_red f g o = print_generic f (decompose_generic g (checkwin_red_circuit x_max)) (qshape redboard,qubit)
  where
    (redboard,_) = start_board o
    x_max = oracle_x_max o  

-- ----------------------------------------------------------------------
-- * Running the Boolean Formula Algorithm

-- $ The following functions define the way that the Boolean Formula Algorithm
-- would be run, if we had access to a quantum computer. Indeed, the functions
-- here interface with the "QuantumSimulation" quantum simulator so that they
-- can be built.

-- | Approximation of how the algorithm would be run if we had a quantum computer:
--   uses QuantumSimulation run_generic_io function. The output of the algorithm will
-- be all False only in the instance that the Blue player wins the game.
main_bf :: BooleanFormulaOracle -> IO Bool
main_bf oracle = do
	output <- run_generic_io (undefined :: Double) (qw_bf oracle)
	let result = if (or output) then True  -- a /= 0 (Red Wins) 
                                    else False -- a == 0 (Blue Wins)
	return result

-- | Display the result of 'main_bf',
--   i.e., either \"Red Wins\", or \"Blue Wins\" is the output.
whoWins :: BooleanFormulaOracle -> IO ()
whoWins oracle = do
	result <- main_bf oracle
	if result then putStrLn "Red Wins"
		  else putStrLn "Blue Wins"

-- | Run 'whoWins' for the given oracle, and its \"initial\" board.
main_whoWins :: BooleanFormulaOracle -> IO ()
main_whoWins o = whoWins o
