-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module contains the implementation of the circuits for determining which 
-- player has won a completed game of Hex. Please see "Algorithms.BF.Main"
-- for an overview of the boolean formula algorithm, or 
-- "Algorithms.BF.BooleanFormula" to see where these circuits are used in the
-- overall implementation of the boolean formula algorithm.
-- The functions defined in this module make heavy use of Quipper's \"build_circuit\" 
-- keyword, to automatically generate quantum circuits.

module Algorithms.BF.Hex where

import Quipper
import Quipper.CircLifting
import QuipperLib.Qram
import QuipperLib.Arith

import Prelude hiding (lookup)

-- | A dummy gate, that when lifted will add a quantum trace to the circuit.
qtrace :: [Bool] -> [Bool]
qtrace bs = bs

-- | A hand-lifted version of qtrace, adds a named \"trace\" gate to the circuit.
template_qtrace :: Circ ([Qubit] -> Circ [Qubit])
template_qtrace = return $ \qs -> do
  named_gate_at "trace" qs
  return qs

-- | A hand-lifted version of the Prelude 'show' function.
template_show :: Show a => Circ (a -> Circ String)
template_show = return $ \a -> return $ show a

-- | A hand-lifted function to get the 'head' of a list.
template_head :: Circ ([a] -> Circ a)
template_head = return $ \q -> return (head q)

-- | A hand-lifted function to get the 'tail' of a list.
template_tail :: Circ ([a] -> Circ [a])
template_tail = return $ \q -> return (tail q)

-- | A hand-lifted function to get the 'length' of a list.
template_length :: Circ ([a] -> Circ Int)
template_length = return $ \as -> return $ length as

-- | A hand-lifted version of the 'take' function, specialized to lists of qubits.
template_take :: Circ (Int -> Circ ([Qubit] -> Circ [Qubit]))
template_take = return $ \n -> return $ \qs -> return (take n qs)

-- | A hand-lifted version of the 'drop' function, specialized to lists of qubits.
template_drop :: Circ (Int -> Circ ([Qubit] -> Circ [Qubit]))
template_drop = return $ \n -> return $ \qs -> return (drop n qs)

-- | A hand-lifted version of the 'replicate' function, specialized to create lists of 'BoolParam'.
template_replicate :: Circ (Int -> Circ (BoolParam -> Circ [BoolParam]))
template_replicate = return $ \n -> return $ \bp -> return (replicate n bp)

-- | A hand-lifted version of the 'map' function.
template_map :: Circ ((a -> Circ a) -> Circ ([a] -> Circ [a]))
template_map = return $ \func -> return $ \qs -> mapM func qs

-- | 'Int' is not changed along the conversion.
template_integer :: Int -> Circ Int
template_integer x = return x

-- | A hand-lifted version of the '-' function, specialized to 'Int'.
template_symb_minus_ :: Circ (Int -> Circ (Int -> Circ Int))
template_symb_minus_ = return $ \x -> return $ \y -> return (x - y)

-- | A hand-lifted version of the '+' function, specialized to 'Int'.
template_symb_plus_ :: Circ (Int -> Circ (Int -> Circ Int))
template_symb_plus_ = return $ \x -> return $ \y -> return (x + y)

-- | A hand-lifted version of the '<' function, specialized to 'Int'.
template_symb_oangle_ :: Circ (Int -> Circ (Int -> Circ Bool))
template_symb_oangle_ = return $ \x -> return $ \y -> return (x < y)

-- | A hand-lifted version of the '<=' function, specialized to 'Int'.
template_symb_oangle_symb_equal_ :: Circ (Int -> Circ (Int -> Circ Bool))
template_symb_oangle_symb_equal_ = return $ \x -> return $ \y -> return (x <= y)

-- | A hand-lifted version of the 'div' function, specialized to 'Int'.
template_div :: Circ (Int -> Circ (Int -> Circ Int))
template_div = return $ \x -> return $ \y -> return (x `div` y)

-- | A function synonym for '&&'.
cand :: Bool -> Bool -> Bool
cand = (&&)

-- | A hand-lifted version of the 'cand' function.
template_cand :: Circ (Bool -> Circ (Bool -> Circ Bool))
template_cand = return $ \x -> return $ \y -> return (x && y)

-- | A hand-lifted version of the '>' function, specialized to 'Int'.
template_symb_cangle_ :: Circ (Int -> Circ (Int -> Circ Bool))
template_symb_cangle_ = return $ \x -> return $ \y -> return (x > y)

-- | A hand-lifted version of the '!!' function.
template_symb_exclamation_symb_exclamation_ :: Circ ([a] -> Circ (Int -> Circ a))
template_symb_exclamation_symb_exclamation_ = return $ \as -> return $ \i -> return (as !! i)

-- | A hand-lifted version of the 'mod' function, specialized to 'Int'.
template_mod :: Circ (Int -> Circ (Int -> Circ Int))
template_mod = return $ \x -> return $ \y -> return (x `mod` y)

-- | A hand-lifted version of the 'zip' function, specialized to lists of qubits.
template_zip :: Circ ([Qubit] -> Circ ([Qubit] -> Circ [(Qubit,Qubit)]))
template_zip = return $ \as -> return $ \bs -> return $ zip as bs

-- | A hand-lifted version of the 'unzip' function, specialized to a list of pairs of qubits.
template_unzip :: Circ ([(Qubit,Qubit)] -> Circ ([Qubit],[Qubit]))
template_unzip = return $ \abs -> return $ unzip abs

-- | A hand-lifted version of the 'or' function, specialized to a list of qubits.
template_or :: Circ ([Qubit] -> Circ Qubit)
template_or = return $ \bs -> do
  q <- qinit True
  qnot q `controlled` [ b .==. 0 | b <- bs ]

-- | The Hex board consists of boolean parameters.
type HexBoardParam = ([BoolParam],[BoolParam])

-- | Convert a list of boolean parameters into a list of boolean inputs.
newBools :: [BoolParam] -> [Bool]
newBools = map newBool

-- | A hand-lifted function to convert a list of boolean parameters
-- into a list of qubits initialized as ancillas is the given states.
template_newBools :: Circ ([BoolParam] -> Circ [Qubit])
template_newBools = return $ \bps -> do
  let bs = map newBool bps
  mapM qinit bs

-- | Convert a little-endian list of booleans into an integer by
-- reversing the list and calling the big-endian conversion function
-- 'bools2int''.
bools2int :: [Bool] -> Int
bools2int bs = bools2int' (reverse bs)

-- | Convert a big-endian list of booleans into an integer. This is
-- mainly used for displaying a \"position\" register.
bools2int' :: [Bool] -> Int
bools2int' [] = 0
bools2int' (x:xs) = 2*(bools2int' xs) + (if x then 1 else 0)

-- | Convert an integer into a little-endian list of booleans of length /n/
-- by reversing the big-endian list created by the 'int2bools'' function.
int2bools :: Int -> Int -> [Bool]
int2bools n x = reverse (int2bools' n x)

-- | Convert an integer into a big-endian list of booleans of length /n/.
-- | Note that the behavior when /x/ is greater than 2[sup /n/] - 1 is erroneous.
int2bools' :: Int -> Int -> [Bool]
int2bools' n x = take n (int2bools'' x ++ repeat False)

-- | Convert an integer into a big-endian list of booleans of minimal length.
int2bools'' :: Int -> [Bool]
int2bools'' 0 = [False]
int2bools'' 1 = [True]
int2bools'' x = (odd x):(int2bools'' (x `div` 2)) 

-- | This function is a stub, because a hand lifted version is given
-- for creating the circuits.
lookup :: [Bool] -> [Bool] -> Bool
lookup board address = board !! (bools2int address)

-- | Hand-lifted version of lookup that uses 'addressed_perform' to look up a qubit at the given address.
template_lookup :: Circ ([Qubit] -> Circ ([Qubit] -> Circ Qubit))
template_lookup = return $ \board -> return $ \address -> do
  addressed_perform board address $ \q -> do   -- q is board[address]
    anc <- qinit False
    qnot_at anc `controlled` q
    return anc

-- | Update the board, by negating the boolean in board, at the given address.
update :: [Bool] -> [Bool] -> [Bool]
update board address = (take n board) ++ b:(drop (n+1) board)
    where n = bools2int address
          b = not (board !! n)

-- | Hand-lifted version of update that uses 'addressed_perform' to negate a qubit at the given address.
template_update :: Circ ([Qubit] -> Circ ([Qubit] -> Circ [Qubit]))
template_update = return $ \board -> return $ \address -> do
  addressed_perform board address $ \q -> do  -- q is board[address]
    qnot_at q 
  return board

-- | An unencapsulated version of 'template_update', for testing purposes.
test_update :: [Qubit] -> [Qubit] -> Circ [Qubit]
test_update board address = do
 qcqcq <- template_update
 qqcq <- qcqcq board
 qqcq address

-- | Perform a given operation on a quantum-addressed element of an array of 
-- quantum data. 
addressed_perform :: QData qa => 
  [qa]                 -- ^ Array of quantum data.
  -> [Qubit]           -- ^ Index into the array.
  -> (qa -> Circ b)    -- ^ An operation to be performed.
  -> Circ b
addressed_perform qs idx f = do
  with_computed (indexed_access qs i) $ \x -> do
    f x
  where i = qdint_of_qulist_bh idx

-- | Update the boolean value at the given position, to the given value.
build_circuit
update_pos :: Int -> [Bool] -> Bool -> [Bool]
update_pos n bs b = (take n bs) ++ b:(drop (n+1) bs)

-- ======================================================================
-- * Oracle implementation

-- $ The functions in this implementation follow a separation of the boolean
-- formula algorithm into two parts. The first part consists of the  
-- algorithms defined in "Algorithms.BF.BooleanFormula". The second part 
-- consists of the algorithms defined in this module. This separation relates 
-- to the first part defining the quantum parts of the algorithm, including the 
-- phase estimation, and the quantum walk, whereas the remaining four define 
-- the classical implementation of the circuit for determining which player 
-- has won a completed game of Hex, which is converted to a quantum circuit 
-- using Quipper's \"build_circuit\" keyword.

-- | A helper function, used by the 'flood_fill' function, that
-- checks whether a given board position is currently vacant.
build_circuit
testpos :: Int -> [Bool] -> [Bool] -> [Bool] -> Int -> [Bool]
testpos pos maskmap bitmap newmap xy_max = case (0 <= pos) `cand` (pos < xy_max) of
 True -> if not (maskmap !! pos) && not (bitmap !! pos) && not (newmap !! pos)
	 then update_pos pos newmap True
	 else newmap
 False -> newmap

-- | Given a board position, this function will call 
-- 'testpos' for each of its neighboring board positions.
build_circuit
test_positions :: Int -> Int -> Int -> [Bool] -> [Bool] -> [Bool] -> ([Bool],[Bool])
test_positions ii x_max xy_max bitmap newmap maskmap =
 let bitmap' = update_pos ii bitmap True in
 let newmap' = testpos (ii + x_max) maskmap bitmap' newmap xy_max in
 let newmap'' = testpos (ii - x_max) maskmap bitmap' newmap' xy_max in
 let newmap''' = case (ii `mod` x_max > 0) of
		  True -> testpos (ii - 1) maskmap bitmap' newmap'' xy_max
		  False -> newmap''
                 in
 let newmap'''' = case (ii `mod` x_max > 0) of
		   True -> testpos (ii + x_max - 1) maskmap bitmap' newmap''' xy_max
		   False -> newmap'''
                  in
 let newmap''''' = case (ii `mod` x_max < x_max - 1) of
		    True -> testpos (ii + 1) maskmap bitmap' newmap'''' xy_max
		    False -> newmap''''
                   in
 let newmap'''''' = case (ii `mod` x_max < x_max - 1) of
		     True -> testpos (ii - x_max + 1) maskmap bitmap' newmap''''' xy_max
		     False -> newmap'''''
                    in
 let newmap''''''' = update_pos ii newmap'''''' False in
 (newmap''''''',bitmap')
   


-- | This function calls 'test_positions' for every board position in strictly 
-- increasing order.
build_circuit
while_for :: Int -> Int -> Int -> [Bool] -> [Bool] -> [Bool] -> ([Bool],[Bool])
while_for counter xy_max x_max bitmap newmap maskmap = case counter of
  0 -> let bitmap' = qtrace bitmap in
       (bitmap',newmap)
  n -> let ii = xy_max - n in
       let (newmap',bitmap') = if newmap !! ii 
                               then test_positions ii x_max xy_max bitmap newmap maskmap
                               else (newmap,bitmap) in 
       while_for (n-1) xy_max x_max bitmap' newmap' maskmap

-- | This function is used by 'flood_fill' to perform an approximation of a while loop.
-- This starts with /newmap/ containing only the blue pieces from the top row of the 
-- Hex board, and fills in all contiguous regions, i.e., areas bounded by red pieces. 
-- The resulting bitmap will only have blue pieces in the bottom row of the Hex board, 
-- if blue has won. The number of times the loop will repeat is bounded by the size of 
-- the Hex board.
build_circuit
while :: Int -> Int -> [Bool] -> [Bool] -> [Bool] -> [Bool]
while counter x_max bitmap newmap maskmap = case counter of
 0 -> bitmap
 n -> let counter' = length bitmap in
      let (bitmap',newmap') = while_for counter' counter' x_max bitmap newmap maskmap in
      while (n-1) x_max bitmap' newmap' maskmap

-- | Swap the position of two boolean values within a pair.
swapBool :: (Bool,Bool) -> (Bool,Bool)
swapBool (a,b) = (b,a)

-- | A hand-lifted version of the 'swapBool' function, which uses a 'swap' operation
-- to swap the state of two qubits within a pair.
template_swapBool :: Circ ((Qubit,Qubit) -> Circ (Qubit,Qubit))
template_swapBool = return $ \(a,b) -> do
  swap a b
  return (a,b)

-- | Implements a 'flood_fill' algorithm on a representation of a Hex
-- board. Returning the \"flooded\" version of the board.
build_circuit
flood_fill :: Int -> [Bool] -> [Bool] -> [Bool]
flood_fill x_max bitmap maskmap =
 let newmap = newBools (replicate (length bitmap) PFalse) in
 let (bitmap',newmap') = unzip (map (\(a,b) -> if a then swapBool (a,b) else (a,b)) (zip bitmap newmap)) in
 let newmap'' = qtrace newmap' in
 let counter = ((length bitmap) `div` 4) + 1 in 
 -- The worst case scenario in our case as we know only half the pieces 
 -- can be blue, and only half those can be left or above in a flood_fill path 
 while counter x_max bitmap' newmap'' maskmap 

-- | A sub-algorithm of the 'checkwin_red' algorithm, which is given the bottom row of
-- booleans after the 'flood_fill' algorithm has been run, and checks to see if any of 
-- them are 'True'.
build_circuit
checkwin_red' :: [Bool] -> Bool
checkwin_red' bs = not (or bs) 

-- | Given a description of a valid Hex board, i.e., a board
-- that represents a finished game, with a single piece on each square, will return 
-- a boolean value stating whether the red player has won.
build_circuit
checkwin_red :: Int -> [Bool] -> Bool
checkwin_red x_max redboard = 
  let begin_blueboard = map not (take x_max redboard) in
  let n = length redboard - x_max in
  let tail_blueboard = newBools (replicate n PFalse) in
  let blueboard = begin_blueboard ++ tail_blueboard in
  let blueboard' = flood_fill x_max blueboard redboard in
  checkwin_red' (drop n blueboard')

-- | An unencapsulated version of the 'checkwin_red' circuit.
checkwin_red_c :: Int -> [Qubit] -> Circ Qubit
checkwin_red_c i qs = do
  icqscq <- template_checkwin_red
  cqscq <- icqscq i
  cqscq qs

-- | A recursive sub-algorithm of 'hex' that goes through each direction in the 
-- position register and recursively updates the ancilla register representing 
-- the /blueboard/ and /redboard/ depending on which player's turn it is. If a 
-- position is already set in one of the ancilla registers, then the current player 
-- has played an invalid move, and therefore loses. If we pass through the entire 
-- position register, then we have a valid description of a Hex board split between 
-- the /redboard/ and /blueboard/ registers, which can then be passed to 'checkwin_red'
-- to see who has won (we actually only pass the /redboard/ to 'checkwin_red' as every 
-- square is now either a red piece or a blue piece, so no extra information is held 
-- in the /blueboard/ register).
build_circuit
movesT :: Int -> [[Bool]] -> [Bool] -> [Bool] -> BoolParam -> Bool
movesT x_max pos redboard blueboard player = 
 case pos of
  [] -> checkwin_red x_max redboard 
  (address:pos') -> 
   if lookup redboard address 
    then (newBool player) 
    else 
    ( if lookup blueboard address 
       then (newBool player) 
       else 
       ( case player of
          PFalse -> movesT x_max pos' (update redboard address) blueboard PTrue -- Red played, so Blue is next
          PTrue -> movesT x_max pos' redboard (update blueboard address) PFalse -- Blue played, so Red is next
       )
    )

-- | The overall hex function. This initializes two ancilla registers 
-- to represent the /redboard/ and the /blueboard/, and passes these to the recursive 
-- 'movesT' function to determine which color has won the game of Hex.
build_circuit
hexT :: HexBoardParam -> BoolParam -> Int -> [[Bool]] -> Bool
hexT (init_r,init_b) next_player x_max pos = 
    let redboard = newBools init_r in
    let blueboard = newBools init_b in
    let result = movesT x_max pos redboard blueboard next_player in 
    -- next_player: PFalse = Red, PTrue = Blue.
    result

-- | A function to convert a boolean to a boolean parameters
newBoolParam :: Bool -> BoolParam
newBoolParam x = if x then PTrue else PFalse

-- | A function to convert a list of booleans to a list of boolean
-- parameters.
newBoolParams :: [Bool] -> [BoolParam]
newBoolParams = map newBoolParam

-- | An interface to the lifted version of 'hexT' (i.e.,
-- 'template_hexT'), which unbinds the inputs from the 'Circ' monad.
hex_oracle_c :: ([Bool],[Bool]) -> Int -> Int -> [[Qubit]] -> Circ Qubit
hex_oracle_c (init_r,init_b) s x_max pos = do
    let params = (newBoolParams init_r,newBoolParams init_b)
    let next_player = newBoolParam (even s) -- the size of the board is always 1 less
                                            -- than an integer power of 2, therefore
                                            -- an odd number. Red goes first, and
                                            -- players alternate, so if the number of
                                            -- moves remaining is odd, then the next
                                            -- player is Red.
    template_hexT_bp <- template_hexT
    template_hexT_int <- template_hexT_bp params
    template_hexT_int' <- template_hexT_int next_player
    template_hexT_qs <- template_hexT_int' x_max
    template_hexT_qs pos

-- | An embedding of 'hex_oracle_c' into a reversible circuit, where all
-- ancillas are uncomputed automatically.
hex_oracle :: ([Bool],[Bool]) -> Int -> Int -> ([[Qubit]],Qubit) -> Circ ([[Qubit]],Qubit)
hex_oracle init s x_max pb = do
  comment "HEX"
  label pb ("pos","binary")
  (classical_to_quantum . classical_to_reversible) (hex_oracle_c init s x_max) pb

-- | A dummy oracle is just a gate named "HEX" applied to the input qubits.
hex_oracle_dummy :: ([[Qubit]],Qubit) -> Circ ([[Qubit]],Qubit)
hex_oracle_dummy qs = named_gate "HEX" qs

-- | An embedding of 'checkwin_red_c' into a reversible circuit, where all
-- ancillas are uncomputed automatically.  
checkwin_red_circuit :: Int -> ([Qubit],Qubit) -> Circ ([Qubit],Qubit)
checkwin_red_circuit x_max = (classical_to_quantum . classical_to_reversible) (checkwin_red_c x_max)
