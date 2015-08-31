-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | Functions to decompose circuits into various gate bases.

module QuipperLib.Decompose ( 
  -- * Precision
  Precision,
  bits,
  digits,
  -- * Phase
  KeepPhase,
  -- * Gate bases
  GateBase (..),
  gatebase_enum,
  -- * Generic decomposition
  decompose_generic,
) where

import QuipperLib.Decompose.CliffordT
import QuipperLib.Decompose.GateBase
import QuipperLib.Decompose.Legacy
import QuipperLib.Synthesis
