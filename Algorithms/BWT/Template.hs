-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}

-- | The BWT Oracle, written in a classical, functional manner and
-- automatically transformed to a quantum circuit using Quipper's
-- \"build_circuit\" mechanism.
module Algorithms.BWT.Template where

import Quipper

import Control.Monad (sequence)
import Algorithms.BWT.Alternative

import Libraries.Auxiliary
import QuipperLib.ClassicalOptim

-- ----------------------------------------------------------------------
-- * Circuit building functions

-- $BUILDING
-- 
-- This section contains an implementation of the oracle as a
-- collection of ordinary functional programs. Each function in this
-- section is decorated with the @build_circuit@ keyword (see
-- "Quipper.CircLifting#build_circuit"). Therefore, circuits are
-- automatically generated; for example, the circuit corresponding to
-- the function 'bwt_oracle' is automatically built and given the name
-- 'template_bwt_oracle'.

----------------------------------------------------------------------
-- ** General operations on booleans

-- | Exclusive /or/ operation on bit vectors. 
build_circuit
boollist_xor :: [Bool] -> [Bool] -> [Bool]
boollist_xor x y = zipWith bool_xor x y


-- | 'bit_adder' 'False' is a one-bit adder, and 'bit_adder' 'True' is a
-- one-bit subtracter (i.e., add the 2's complement of /y/).
build_circuit
bit_adder :: Bool -> (Bool,Bool,Bool) -> (Bool,Bool)
bit_adder sign (carry, x,y) =
      let majority a b c =
             if (a `bool_xor` b) then c else a in
      let y' = y `bool_xor` sign in
      let z = carry `bool_xor` x `bool_xor` y' in
      let carry' = majority carry x y' in
      (carry', z)


----------------------------------------------------------------------
-- ** Encoding the BWT oracle on booleans and lists of booleans

-- | Input a node /a/ and return the parent of /a/. We assume that /a/
-- is not a root or invalid.
build_circuit
parent :: Node -> Node
parent (x,y) = (x, False:(init y))

-- | Input a node /a/ and return the left or right child of /a/
-- (depending on whether the /childbit/ is 'False' or 'True',
-- respectively). Assumes that /a/ is not a leaf.
build_circuit
childintree :: Node -> Bool -> Node
childintree (t,l) c = 
      case l of
        []   -> error "childintree"
        h:aa -> (t, aa ++ [c])


-- | Input an /n/+1-bit leaf node /a/:/aa/ (without the tree bit; /a/
-- is the highest bit and /aa/ is the remaining /n/ bits) and a sign
-- /s/ (where 'True' = negative, 'False' = positive).  Return
-- /a/:(/aa/ + /s/ * /f/). The first input is the /n/-bit welding
-- vector /f/ (a parameter to the oracle). Note that /f/ is a
-- parameter and /s/, /aa/ are inputs.
build_circuit
doweld1 :: Boollist -> Bool -> [Bool] -> [Bool]
doweld1 f s l = 
      case l of
        [] -> error "doweld1"
        a:aa -> a : (snd (fold_right_zip (bit_adder s) (s, aa, f)))


-- | Input an /n/+1-bit leaf node /a/:/aa/ (without the tree bit), and
-- return /a/:(/aa/ ⊕ /g/). The first input is the /n/-bit welding
-- vector /g/ (a parameter to the oracle).
build_circuit
doweld0 :: Boollist -> [Bool] -> [Bool]
doweld0 g l =
      case l of
          [] -> error "doweld0"
          a:aa -> a : (g `boollist_xor` aa)


-- | Input a leaf node /a/ and return the left or right weld of /a/ in
-- the other tree (depending on whether the /weldbit/ is 'False' or
-- 'True').  Assumes that /a/ is a leaf.
build_circuit
weld :: Boollist -> Boollist -> Node -> Bool -> Node
weld f g (t,aa) weldBit =
      if weldBit then (not t, doweld1 g t aa) 
      else (not t, doweld0 f aa)


-- | Input a node /a/ and return the left or right child of /a/
-- (depending on whether the /childbit/ is 'False' or 'True'. This
-- works for leaf and non-leaf nodes.
build_circuit
child :: Boollist -> Boollist -> Node -> Bool -> Node
child f g (t,aa) childBit =
      case aa of
        [] -> error "child"
        h:tt -> if h then weld f g (t, aa) childBit
                else childintree (t, aa) childBit


-- | Input a node address (without the tree bit) and return the parity
-- of the node level expressed as a boolean either 'False' or
-- 'True'. Leaves have parity 'False', and other levels have
-- alternating parities. In other words: count the number of leading
-- zeros modulo 2.
build_circuit
level_parity :: [Bool] -> Bool
level_parity l = foldl (\a b -> not (a || b)) False (reverse l)


-- | Input a node address (without the tree bit) and return 'True' iff
-- the node address is invalid. In other words, return 'True' iff the
-- list consists of all 0's.
build_circuit
is_zero :: [Bool] -> Bool
is_zero l = foldl (\a b -> a && (not b)) True l


-- | Input a node address (without the tree bit) and return 'True' iff
-- the node is a root or invalid. In other words, check whether all
-- digits but the last are 0's.
build_circuit
is_root :: [Bool] -> Bool
is_root l = case (reverse l) of
              []    -> True
              (h:t) -> is_zero t



-- | @'v_function' f g c a@: returns /v/[sub /c/](/a/), the label of the
-- node connected to /a/ by an edge of color /c/, or 'Nothing' if
-- there is no such node. The parameters /f/ and /g/ encode the
-- welding functions, and are lists of length /n/. /c/ is a color in
-- the range 0..3, and /a/ is an (/n/+2)-bit node label.
build_circuit
v_function :: BoolParam -- ^First color bit.
           -> BoolParam -- ^Second color bit.
           -> Boollist  -- ^Vector /f/ from Equation (26).
           -> Boollist  -- ^Vector /g/ from Equation (27).
           -> Node      -- ^Entry node /a/.
           -> (Bool,Node) -- ^('True', exit node) or ('False', garbage).
v_function c_hi c_lo f g a =
      let aa = snd a in
      let cbc_hi = newBool c_hi `bool_xor` level_parity aa in
      let cbc_lo = newBool c_lo in
         if (not (is_root aa) && cbc_hi && not (cbc_lo `bool_xor` (last aa))) then 
           (False, parent a)
         else 
           let res = child f g a cbc_lo in
           (is_zero aa || cbc_hi, res)

-- ----------------------------------------------------------------------
-- * Wrapping it into the Oracle data type

-- $PACKAGE The following functions package the circuit generated by
-- 'v_function' into a data structure of type 'Oracle'.

-- ----------------------------------------------------------------------
-- ** Colors

-- | A color is a number between 0 and 3.
type Color = Int

-- | Convert an integer representation of a color into the two-bit representation.
colorToBoolParam :: Color -> (BoolParam,BoolParam)
colorToBoolParam 0 = (PFalse,PFalse)
colorToBoolParam 1 = (PFalse,PTrue)
colorToBoolParam 2 = (PTrue,PFalse)
colorToBoolParam 3 = (PTrue,PTrue)
colorToBoolParam _ = error "color out of range"

-- ----------------------------------------------------------------------
-- ** Functions for using the generated oracle

-- | This is the /irreversible/ classical circuit generated from
-- 'v_function'. This is basically the same as 'template_v_function',
-- except that excessive uses of 'Circ' are removed from the type, and
-- the inputs and outputs have been reorganized.
classical_BWT_oracle :: Color      -- ^ The color.
      -> ([Qubit],[Qubit], QNode)  -- ^ The two welding vectors and a node /a/.
      -> Circ (Qubit, QNode)       -- ^ Output /(r,b)/.
classical_BWT_oracle col (f,g,xs)  = 
  unpack template_v_function b1 b2 f g xs
  where
    (b1,b2) = colorToBoolParam col

-- | This is the /reversible/ circuit automatically generated from 'classical_BWT_oracle'. 
reversible_BWT_oracle :: 
  Color  -- ^ Color.
  -> (([Qubit], [Qubit], QNode), (Qubit, QNode)) -- ^ /(f, g, a, r, b)/.
  -> Circ (([Qubit], [Qubit], QNode), (Qubit, QNode)) -- ^ Output /(f, g, a, r, b)/.
reversible_BWT_oracle color ((f, g, a), (r, b)) = do
  comment_with_label "ENTER: reversible_BWT_oracle" ((f, g, a), (r, b)) (("f", "g", "a"), ("r", "b"))
  ((f, g, a), (r, b)) <- classical_to_reversible (classical_BWT_oracle color) ((f, g, a), (r, b))
  comment_with_label "EXIT: reversible_BWT_oracle" ((f, g, a), (r, b)) (("f", "g", "a"), ("r", "b"))
  return ((f, g, a), (r, b))

-- | This is the /reversible/ circuit automatically generated from 'classical_BWT_oracle', and optimized with peep-hole optimization.
reversible_BWT_oracle_optim :: 
  Color  -- ^ Color.
  -> (([Qubit], [Qubit], QNode), (Qubit, QNode)) -- ^ /(f, g, a, r, b)/.
  -> Circ (([Qubit], [Qubit], QNode), (Qubit, QNode)) -- ^ Output /(f, g, a, r, b)/.
reversible_BWT_oracle_optim color ((f, g, a), (r, b)) = do
  comment_with_label "ENTER: reversible_BWT_oracle" ((f, g, a), (r, b)) (("f", "g", "a"), ("r", "b"))
  ((f, g, a), (r, b)) <- classical_to_reversible_optim (classical_BWT_oracle color) ((f, g, a), (r, b))
  comment_with_label "EXIT: reversible_BWT_oracle" ((f, g, a), (r, b)) (("f", "g", "a"), ("r", "b"))
  return ((f, g, a), (r, b))


-- | The template oracle, packaged into the 'Oracle' abstraction. Note
-- that this circuit is automatically generated from the classical
-- functions above, but is completely unoptimized. This oracle has two
-- parameters, namely the welding vectors /f/ and /g/.
oracle_template :: [Bool] -> [Bool] -> Oracle
oracle_template f g =
  Oracle {
    n = n,
    m = m,
    k = 4,
    entrance = boollist_of_int_bh m 1,
    oraclefun = \c (as,bs,r) -> do qf <- qinit f
                                   qg <- qinit g
				   let (a:aa) = as
				   let (b:bb) = bs
                                   reversible_BWT_oracle c ((qf, qg, (a,aa)), (r, (b,bb)))
				   qterm g qg
				   qterm f qf
  }
  where n = length f
	m = n+2


-- | The template oracle, optimized.
oracle_template_optim :: [Bool] -> [Bool] -> Oracle
oracle_template_optim f g =
  Oracle {
    n = n,
    m = m,
    k = 4,
    entrance = boollist_of_int_bh m 1,
    oraclefun = \c (as,bs,r) -> do qf <- qinit f
                                   qg <- qinit g
				   let (a:aa) = as
				   let (b:bb) = bs
                                   reversible_BWT_oracle_optim c ((qf, qg, (a,aa)), (r, (b,bb)))
				   qterm g qg
				   qterm f qf
  }
  where n = length f
	m = n+2

