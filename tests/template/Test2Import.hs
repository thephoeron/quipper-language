-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

module Test2Import where

import Data.Map as Map
import Language.Haskell.TH as TH

boolMap :: Map.Map String (TH.Q TH.Exp)
boolMap = Map.fromList [("not", varE (TH.mkName "myNot")),
                        ("&&", varE (TH.mkName "myAnd"))]

