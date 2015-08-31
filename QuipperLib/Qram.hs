-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | A custom qRAM algorithm for fetching and storing quantum data
-- from a quantum array, addressed by a quantum integer.

module QuipperLib.Qram (
  indexed_access,
  indexed_fetch_at,
  indexed_store_at,
  indexed_swap_at,
  ) where

import Quipper
import QuipperLib.Arith

-- | Inputs a list /a/ of quantum data and a quantum integer /i/, and
-- returns the /i/th element of /a/. This is done with controlled swap
-- operations, but without ancillas, i.e., the output is the only copy
-- of that quantum data. Note that the remaining elements of the array
-- may be swapped around, so they are not useable until
-- 'indexed_access' has been reversed.
-- 
-- Suggested usage:
-- 
-- > with_computed (indexed_access i a) $ \x -> do
-- >   <<<operate on x>>>
-- 
-- If the index is out of bound, return an unpredictable element of
-- /a/. If /a/ is of length 0, raise an error.
indexed_access :: (QData qa) => [qa] -> QDInt -> Circ qa
indexed_access as i = indexed_access_qulist as (qulist_of_qdint_bh i)

-- | Auxiliary function: like 'indexed_access', but uses a qubit list
-- instead of a quantum integer. The list is big-headian, i.e., the
-- head of the list holds the most significant bit.
indexed_access_qulist :: (QData qa) => [qa] -> [Qubit] -> Circ qa
indexed_access_qulist [] i = error "indexed_access: cannot address length-0 register"
indexed_access_qulist (a:as) [] = return a
indexed_access_qulist as (i:is) = do
  let n = 2 ^ length is
      r = max 0 $ min n (length as - n)
      -- r: number of wires that need swapping if head qdigit is set
  for (r-1) 0 (-1) $ \j -> do
    swap_at (as !! j) (as !! (j+n)) `controlled` i
  a <- indexed_access_qulist as is
  return a

-- | @'indexed_fetch_at' /a/ /i/ /q/@: 
-- Perform /q/ ⊕= /a/[/i/].
indexed_fetch_at :: (QData qa) => [qa] -> QDInt -> qa -> Circ ()
indexed_fetch_at as i q = do
  with_computed (indexed_access as i) $ \x -> do
    controlled_not_at q x

-- | @'indexed_store_at' /a/ /i/ /q/@:
-- Perform /a/[/i/] ⊕= /q/.
indexed_store_at :: (QData qa) => [qa] -> QDInt -> qa -> Circ ()
indexed_store_at as i q = do
  with_computed (indexed_access as i) $ \x -> do
    controlled_not_at x q

-- | @'indexed_swap_at' /a/ /i/ /q/@:
-- Swap /a/[/i/] and /q/.
indexed_swap_at :: (QData qa) => [qa] -> QDInt -> qa -> Circ ()
indexed_swap_at as i q = do
  with_computed (indexed_access as i) $ \x -> do
    swap_at x q
