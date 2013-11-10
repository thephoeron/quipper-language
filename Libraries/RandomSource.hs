-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

-- | This module provides a container type for sources of
-- randomness. This makes it possible for a source of randomness (any
-- instance of the 'RandomGen' class) to be stored in a data structure
-- without having to specify its type explicitly.

module Libraries.RandomSource where

import System.Random

-- | A container type to hold a source of randomness. This can hold
-- any instance of the 'RandomGen' class.
data RandomSource where
  RandomSource :: forall g.(RandomGen g) => g -> RandomSource

instance Show RandomSource where
  show x = "g"
