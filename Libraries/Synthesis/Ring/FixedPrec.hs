-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides ring instances for "Data.Number.FixedPrec".

module Libraries.Synthesis.Ring.FixedPrec where

import Libraries.Synthesis.Ring

import Data.Number.FixedPrec

instance Precision e => RootHalfRing (FixedPrec e) where
  roothalf = sqrt 0.5

instance Precision e => RootTwoRing (FixedPrec e) where
  roottwo = sqrt 2

instance Precision e => HalfRing (FixedPrec e) where
  half = 0.5

instance Precision e => Adjoint (FixedPrec e) where
  adj x = x
  
instance Precision e => Adjoint2 (FixedPrec e) where
  adj2 x = x

instance Precision e => Floor (FixedPrec e) where
  floor_of = floor
  ceiling_of = ceiling
