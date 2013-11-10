-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module defines quantum analogues of some Haskell type
-- classes. For instance, Haskell’s @'Eq' a@ has one method
-- 
-- > (==) :: a -> a -> Bool.  
-- 
-- Correspondingly, our @'QEq' a qa ca@ has a method
-- 
-- > q_is_equal :: qa -> qa -> Circ (qa,qa,Qubit).  
-- 
-- All quantum type classes assume that their instance types are
-- 'QData' (or sometimes 'QCData').
-- 
-- Quantum type classes are designed to play nicely with the
-- translation of "Quipper.CircLifting". 

module Quipper.QClasses where

import Quipper.Generic
import Quipper.QData
import Quipper.Monad

-- ----------------------------------------------------------------------
-- * The type class QEq

-- | This is a quantum analogue of Haskell’s 'Eq' type class. Default
-- implementations are provided; by default, equality is bitwise
-- equality of the underlying data structure. However, specific
-- instances can provide custom implementations. In this case,
-- 'q_is_equal' is a minimal complete definition.
class (QCData qc) => QEq qc where
  
  -- | Test for equality. 
  q_is_equal :: qc -> qc -> Circ (qc, qc, Qubit)
  q_is_equal qx qy = do
    (qx,qy) <- controlled_not qx qy
    test <- qinit False
    test <- qnot test `controlled` qx .==. qc_false qx
    (qx,qy) <- reverse_generic_endo controlled_not qx qy
    return (qx,qy,test)
  
  -- | Test for inequality.
  q_is_not_equal :: qc -> qc -> Circ (qc, qc, Qubit)
  q_is_not_equal qx qy = do
    (qx,qy,test) <- q_is_equal qx qy
    qnot_at test
    return (qx,qy,test)

-- Right now we make all QCData an instance of 'QEq', and the equality
-- is always physical equality. In the future we will probably want to
-- replace this by instances for specific types. 
instance (QCData qc) => QEq qc

-- ----------------------------------------------------------------------
-- * The type class QOrd

-- | This is a quantum analogue of Haskell's 'Ord' type class. Its
-- purpose is to define a total ordering on each of its instances. The
-- functions in this class are assumed dirty in the sense that they do
-- not uncompute ancillas, and some of the inputs may be returned as
-- outputs. The functions are also assumed to be non-linear safe,
-- i.e., they apply no gates to their inputs except as control
-- sources. Minimal complete definition: 'q_less' or 'q_greater'. The default
-- implementations of 'q_max' and 'q_min' assume that both arguments
-- are of the same shape (for example, numbers of the same length).
class (QEq qa, QData qa) => QOrd qa where
  -- | Test for less than.  
  q_less :: qa -> qa -> Circ Qubit
  q_less x y = q_greater y x

  -- | Test for greater than.
  q_greater :: qa -> qa -> Circ Qubit
  q_greater x y = q_less y x
    
  -- | Test for less than or equal.
  q_leq :: qa -> qa -> Circ Qubit
  q_leq x y = do
    s <- q_greater x y
    r <- qinit False   
    qnot_at r `controlled` s .==. False
    return r

  -- | Test for greater than or equal.
  q_geq :: qa -> qa -> Circ Qubit
  q_geq x y = q_leq y x
    
  -- | Compute the maximum of two values.
  q_max :: qa -> qa -> Circ qa
  q_max x y = do
    q <- q_greater x y
    z <- qinit $ qc_false x
    (z,x) <- controlled_not z x `controlled` q .==. True
    (z,y) <- controlled_not z y `controlled` q .==. False
    return z
    
  -- | Compute the minimum of two values.
  q_min :: qa -> qa -> Circ qa
  q_min x y = do
    q <- q_less x y
    z <- qinit $ qc_false x
    (z,x) <- controlled_not z x `controlled` q .==. True
    (z,y) <- controlled_not z y `controlled` q .==. False
    return z

-- ===========================================
-- * Functionally-typed wrappers for 'QOrd' methods

-- | @'q_lt' /qx/ /qy/@: test whether /qx/ < /qy/.  A functionally typed wrapper for 'q_less'.
q_lt :: (QOrd qa) => qa -> qa -> Circ (qa,qa,Qubit)
q_lt qx qy = do
  test <- q_less qx qy
  return (qx,qy,test)
 
-- | @'q_gt' /qx/ /qy/@: test whether /qx/ > /qy/. A functionally typed wrapper for 'q_greater'.
q_gt :: (QOrd qa) => qa -> qa -> Circ (qa,qa,Qubit)
q_gt qx qy = do
  test <- q_greater qx qy
  return (qx,qy,test)

-- | @'q_le' /qx/ /qy/@: test whether /qx/ ≤ /qy/. A functionally typed wrapper for 'q_leq'.
q_le :: (QOrd qa) => qa -> qa -> Circ (qa,qa,Qubit)
q_le qx qy = do
  test <- q_leq qx qy
  return (qx,qy,test)

-- | @'q_ge' /qx/ /qy/@: test whether /qx/ ≥ /qy/. A functionally typed wrapper for 'q_geq'.
q_ge :: (QOrd qa) => qa -> qa -> Circ (qa,qa,Qubit)
q_ge qx qy = do
  test <- q_geq qx qy
  return (qx,qy,test)
