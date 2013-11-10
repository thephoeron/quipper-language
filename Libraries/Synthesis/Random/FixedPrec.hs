-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides a 'Random' instance for
-- "Data.Number.FixedPrec".

module Libraries.Synthesis.Random.FixedPrec where

import Data.Number.FixedPrec
import System.Random

instance Precision e => Random (FixedPrec e) where
  randomR (lo, hi) g = (x, g1) where
    n = getprec x  -- precision in decimal digits
    lo_n = floor (lo * 10^n)
    hi_n = floor (hi * 10^n)
    (x_n, g1) = randomR (lo_n, hi_n) g
    x = 0.1^n * fromInteger x_n
    
  random = randomR (0, 1)
