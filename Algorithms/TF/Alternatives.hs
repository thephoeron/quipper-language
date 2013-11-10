-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module contains various supplementary functions related 
-- to the Triangle Finding algorithm: alternatives to and/or 
-- generalizations of the various routines in 
-- 'Algorithms.TF.Oracle' and 'Algorithms.TF.QWTFP'.

module Algorithms.TF.Alternatives where

import Quipper
import Algorithms.TF.Definitions
import QuipperLib.Qram
import QuipperLib.Arith

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

-- ======================================================================
-- * Arithmetic functions

-- | Increment a 'QIntTF' (i.e., little-endian, mod 2[sup /l/] – 1) 
-- in place.
--
-- This and 'decrement_TF' assume as precondition that the input is never 
-- 11…11, and preserve this condition, by fixing 11…11.  This means these
--  are /not/ correct if 'IntTF' is treated as a formal quotient of 
-- 2[sup /l/] ; with that approach, incrementing/decrementing in place 
-- cannot be a quantum operation (since it must map 00…00 and 11…11 both 
-- to 00…01, so would have nonzero kernel).  These are however correct if 
-- 'IntTF' is considered as a formal /subspace/ of 2[sup /l/] (in which 
-- case the other arithmetic routines are unsound, since they may break 
-- the precondition).
increment_TF :: QIntTF -> Circ QIntTF
increment_TF l1 = do
  let l = qulist_of_qinttf_lh l1
  -- mark whether /l/ is initially in forbidden state “all true”:
  is_bad <- qinit False
  is_bad <- qnot is_bad `controlled` [ q .==. 1 | q <- l ]
  -- now, increment /l/ treating it mod 2^/n/:
  l' <- increment_big (reverse l)
  l <- return $ reverse l'
  -- now mark if the /incremented/ /l/ is “all true”:
  needs_rollover <- qinit False 
  needs_rollover <- qnot needs_rollover `controlled` [ q .==. 1 | q <- l ]
  -- if it’s now “all true”, roll it over; or if it initially was, roll it back: 
  l <- mapM (\q -> do
              q <- qnot q `controlled` is_bad
              q <- qnot q `controlled` needs_rollover
              return q)
            l
  -- finally, uncompute the ancillas:
  needs_rollover <- qnot needs_rollover `controlled` [ q .==. 0 | q <- l ]
  qterm False needs_rollover
  is_bad <- qnot is_bad `controlled` [ q .==. 1 | q <- l ]
  qterm False is_bad
  return (qinttf_of_qulist_lh l)


-- | Decrement a 'QIntTF' in place.
decrement_TF :: QIntTF -> Circ QIntTF
decrement_TF l1 = do
  let l = qulist_of_qinttf_lh l1
  -- mark whether /l/ is initially in forbidden state “all true”:
  with_ancilla $ \is_bad -> do
    is_bad <- qnot is_bad `controlled` [ q .==. 1 | q <- l ]
  -- also mark if /l/ is “all false”:
    l <- with_ancilla $ \needs_rollover -> do
      needs_rollover <- qnot needs_rollover `controlled` [ q .==. 0 | q <- l ]
  -- exchange these two states:
      l <- mapM (\q -> do
                  q <- qnot q `controlled` is_bad
                  q <- qnot q `controlled` needs_rollover
                  return q) 
                l
  -- uncompute @needs_rollover@
      needs_rollover <- qnot needs_rollover `controlled` [ q .==. 1 | q <- l ]
      return l
  -- now, decrement /l/ treating it mod 2^/n/:
    l' <- decrement_big (reverse l)
  -- finally, uncompute is_bad:
    is_bad <- qnot is_bad `controlled` [ q .==. 1 | q <- l' ]
    return (qinttf_of_qulist_lh (reverse l'))

-- | An alternative to 'o5_MOD3' for reducing mod-3, conceptually 
-- simpler and not size-limited: uses the fact that 2-bit 'QIntTF's
--  give us true mod-3 arithmetic.
-- 
-- Has same complexity /O(l)/ as 'o5_MOD3', with (probably) a 
-- slightly higher leading coefficient, due to difference in size 
-- between 'increment_TF' and 'increment_little'.
o5_MOD3_alt :: QIntTF -> Circ (QIntTF,QIntTF)
o5_MOD3_alt x1 =  do
  let x = qulist_of_qinttf_lh x1
  let l = length x

  m <- qinit (inttf 2 0)
  (x,m) <- loop_with_indexM l (x,m) (\i (x,m) -> do
    m <- if (even i)  
         then increment_TF m `controlled` (x !! i)
         else decrement_TF m `controlled` (x !! i)
    return (x,m))
  return (qinttf_of_qulist_lh x, m)
  
-- ======================================================================
-- * Efficient qRAM

-- $ We provide an efficient qRAM implementation in "QuipperLib.Qram".
-- The following turns it into a 'Qram' object for the Triangle
-- Finding algorithm.

-- | Efficient qRAM \"fetch\" operation. @'indexed_fetch' /i/ /m/ /q/@
-- performs the operation /q/ ⊕= /m/[/i/].
indexed_fetch :: (QData qa) => QDInt -> IntMap qa -> qa -> Circ (QDInt, IntMap qa, qa)
indexed_fetch i m q = do
  indexed_fetch_at qs i q
  return (i,m,q)
  where
    qs = IntMap.elems m
    
-- | Efficient qRAM \"store\" operation. @'indexed_store' /i/ /m/ /q/@
-- performs the operation /m/[/i/] ⊕= /q/.
indexed_store :: (QData qa) => QDInt -> IntMap qa -> qa -> Circ (QDInt, IntMap qa, qa)
indexed_store i m q = do
  indexed_store_at qs i q
  return (i,m,q)
  where
    qs = IntMap.elems m
    
-- | Efficient qRAM \"swap\" operation. @'indexed_swap' /i/ /m/ /q/@
-- swaps /q/ and /m/[/i/].
indexed_swap :: (QData qa) => QDInt -> IntMap qa -> qa -> Circ (QDInt, IntMap qa, qa)
indexed_swap i m q = do
  indexed_swap_at qs i q
  return (i,m,q)
  where
    qs = IntMap.elems m
    
-- | Our efficient qRAM implementation wrapped in a 'Qram' object.    
alt_qram :: Qram
alt_qram = Qram {
  qram_fetch = indexed_fetch,
  qram_store = indexed_store,
  qram_swap = indexed_swap
}
