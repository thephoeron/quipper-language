-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================


import Quipper
import QuipperLib.Qram
import QuipperLib.Arith

test_qram :: [Qubit] -> QDInt -> Circ ()
test_qram list index = do
  label (list,index) ("list","index")
  with_computed (indexed_access list index) $ \element -> do
    label element "element"
    hadamard_at element


main :: IO ()
main = print_generic Preview test_qram (replicate 8 qubit) (qdint_shape 3)