-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module exposes interfaces that are internal to Quipper, and
-- are not intended for use by user-level code, but may be useful in
-- libraries that extend Quipper's functionality.
-- 
-- This module must not be imported directly by user-level code. It
-- may, however, be imported by libraries. A typical use of this
-- module is in a library that defines a new kind of 'QCData'.

module Quipper.Internal (
  -- * Quantum data
  -- $QData
  module Quipper.QData,
  -- * Currying
  QCurry(..),
  -- * Error handlers
  ErrMsg,
  -- * The Labelable class
  Labelable (..),
  with_index,
  with_dotted_index,
  indexed,
  dotted_indexed,  
  -- * Functions for IntMaps
  intmap_zip,
  intmap_zip_errmsg,
  intmap_map,
  intmap_mapM,
  -- * Identity types                                                          
  Identity,
  reflexivity,
  symmetry,
  transitivity,
  identity,
  ) where

import Libraries.Auxiliary
import Quipper.QData
import Quipper.Labels
import Quipper.Generic

-- $QData
-- 
-- The module "Quipper.QData" provides type classes for dealing with
-- various "shaped" quantum and classical data structures. Please see
-- "Quipper.QData" for documentation.
