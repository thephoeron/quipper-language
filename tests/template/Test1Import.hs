-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

module Test1Import where

import Data.Map as Map
import Language.Haskell.TH as TH

template_integer :: (Monad m) => Int -> m Integer
template_integer x = return $ fromIntegral x

intMap :: Map.Map String (TH.Q TH.Exp)
intMap = Map.fromList [
       ("tick", varE (TH.mkName "do_tick")),
       ("*", varE (TH.mkName "mult")),
       ("-", varE (TH.mkName "subs"))]

