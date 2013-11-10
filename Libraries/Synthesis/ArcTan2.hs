-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides a replacement for Haskell's 'atan2'. The
-- problem is that Haskell's standard implementation of 'atan2'
-- depends on the 'RealFloat' class, which limits its applicability.
-- So we provide a new 'ArcTan2' class with an 'arctan2' function.
-- 
-- Unlike Haskell's 'atan2', the 'arctan2' function may not take
-- signed zeros and signed infinities into account. But it works at
-- fixed-precision types such as 'FixedPrec'.

module Libraries.Synthesis.ArcTan2 where

import Data.Number.FixedPrec

-- ----------------------------------------------------------------------
-- * The arctan2 function

-- | We provide a replacement for Haskell's 'atan2', because the
-- latter depends on the 'RealFloat' class, which limits its
-- applicability.
class ArcTan2 a where
  arctan2 :: a -> a -> a
  
instance ArcTan2 Double where
  arctan2 = atan2

instance ArcTan2 Float where
  arctan2 = atan2

instance (Precision e) => ArcTan2 (FixedPrec e) where
  arctan2 y x
    | x == 0 && y == 0 = 0
    | abs y <= x       = atan (y/x)
    | abs x <= y       = pi/2 - atan (x/y)
    | abs x <= -y      = -pi/2 - atan (x/y)
    | y >= 0           = pi + atan (y/x)
    | otherwise        = -pi + atan (y/x)
