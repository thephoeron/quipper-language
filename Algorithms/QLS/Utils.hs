-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}


-- | This module defines some auxiliary machinery required for the QLS algorithm.
module Algorithms.QLS.Utils where

import Quipper
import Control.Monad
import Data.List

import Quipper.Control

import qualified Data.Map as Map


-- * Hard-coded default sizes for quantum numbers

-- | Default size of a register 'QSignedInt' (not counting the sign).
fixed_int_register_length :: Int
fixed_int_register_length = 32

-- | Default size for the /xxx/ part of the 'QDouble' /xxx.yyy/.
before_radix_length :: Int
before_radix_length = 32

-- | Default size for the /yyy/ part of the 'QDouble' /xxx.yyy/.
after_radix_length :: Int
after_radix_length = 32



-- * Miscellaneous utilities

-- | Compose a function with itself /n/ times. 
ncompose :: Int -> (a -> a) -> a -> a
ncompose 0 f x = x
ncompose n f x = ncompose (n-1) f (f x)

-- | Specialized 'map' for lists of pairs.
listpair_fmap :: (a -> b) -> [(a,a)] -> [(b,b)]
listpair_fmap f t = map (\(x,y) -> (f x,f y)) t


