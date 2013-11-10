-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE Rank2Types #-}

-- | This library provides functions for “unboxing” hierarchical circuits,
-- replacing calls to named subroutines by inlined copies of the subroutines
-- themselves.

module QuipperLib.Unboxing where

import Quipper
import Quipper.Internal
import Quipper.Circuit (BoxId (..), RepeatFlag (..))
import Quipper.Monad (endpoints_of_wires_in_arity)
import Quipper.Generic (inline_subroutine, transform_unary)

-- | A transformer to peel away one level of boxing. Transforms any
-- top-level subroutine gate into its corresponding circuit.
unbox_transformer :: Transformer Circ Qubit Bit
unbox_transformer (T_Subroutine name inv ncf _ _ _ ws2 a2 (RepeatFlag reps) f) = f $
  \namespace ws c -> do
    outputs <- loopM reps ws
      ((without_controls_if ncf) .
       (with_controls c) .
       ((if inv then flip reverse_generic (endpoints_of_wires_in_arity a2 ws2) else id)
        (inline_subroutine name namespace)))
    return (outputs, c)
unbox_transformer x = identity_transformer x

-- | Peel away one level of boxing from a circuit. Transforms any
-- top-level subroutine gate into its corresponding circuit.
unbox_unary :: (QCData x, QCData y) => (x -> Circ y) -> (x -> Circ y)
unbox_unary circ = transform_unary unbox_transformer circ 

-- | Peel away one level of boxing from a circuit. Transforms any
-- top-level subroutine gate into its corresponding circuit.
--   
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types:
-- 
-- > unbox :: (QCData x) =>  Circ x -> Circ x
-- > unbox :: (QCData x, QCData y) =>  (x -> Circ y) -> (x -> Circ y)
-- > unbox :: (QCData x, QCData y, QCData z) => (x -> y -> Circ z) -> (x -> y -> Circ z)
-- 
-- and so forth.
unbox :: (QCData x, QCData y, QCurry qfun x y) => qfun -> qfun
unbox = qcurry . unbox_unary . quncurry

-- | A transformer to recursively unbox some specified class of boxed subroutines.
unbox_recursive_filtered_transformer :: (BoxId -> Bool) -> Transformer Circ Qubit Bit
unbox_recursive_filtered_transformer p b@(T_Subroutine boxid inv ncf _ _ _ ws2 a2 (RepeatFlag reps) f) = 
  if not (p boxid)
  then identity_transformer b
  else f $
    \namespace ws c -> do
    outputs <- loopM reps ws
      ((without_controls_if ncf) .
       (with_controls c) .
       ((if inv then flip reverse_generic (endpoints_of_wires_in_arity a2 ws2) else id) $
        (unbox_recursive_filtered p) $
        (inline_subroutine boxid namespace)))
    return (outputs, c)
unbox_recursive_filtered_transformer _ x = identity_transformer x

-- | Recursively unbox all subroutines satisfying a given predicate.
unbox_recursive_filtered_unary :: (QCData x, QCData y) => (BoxId -> Bool) -> (x -> Circ y) -> (x -> Circ y)
unbox_recursive_filtered_unary p = transform_unary (unbox_recursive_filtered_transformer p)

-- | Recursively unbox all subroutines satisfying a given predicate.
--   
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types:
-- 
-- > unbox_recursive_filtered :: (QCData x) => (BoxId -> Bool) -> Circ x -> Circ x
-- > unbox_recursive_filtered :: (QCData x, QCData y) => (BoxId -> Bool) -> (x -> Circ y) -> (x -> Circ y)
-- 
-- and so forth.
unbox_recursive_filtered :: (QCData x, QCData y, QCurry qfun x y) => (BoxId -> Bool) -> qfun -> qfun
unbox_recursive_filtered p = qcurry . (unbox_recursive_filtered_unary p) . quncurry

-- | Recursively unbox all subroutines of a circuit.
--   
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types:
-- 
-- > unbox_recursive :: (QCData x) =>  Circ x -> Circ x
-- > unbox_recursive :: (QCData x, QCData y) =>  (x -> Circ y) -> (x -> Circ y)
-- > unbox_recursive :: (QCData x, QCData y, QCData z) => (x -> y -> Circ z) -> (x -> y -> Circ z)
-- 
-- and so forth.
unbox_recursive :: (QCData x, QCData y, QCurry qfun x y) => qfun -> qfun
unbox_recursive = unbox_recursive_filtered (const True)
