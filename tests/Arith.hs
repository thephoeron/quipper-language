-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper
import QuipperLib.Arith

main :: IO ()
main = print_generic Preview labelled_add (qdint_shape 3) (qdint_shape 3)


labelled_add :: QDInt -> QDInt -> Circ (QDInt, QDInt,QDInt)
labelled_add x y = do
  label (x,y) ("x","y")
  xy <- q_add x y
  label xy ("x","y","x+y")
  return xy