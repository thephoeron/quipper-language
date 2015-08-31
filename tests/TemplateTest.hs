-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This file illustrates the most basic use of Template Haskell.

import Quipper

-- | A classical implementation of some boolean function.
build_circuit
example1 :: Bool -> Bool -> Bool
example1 a b = (a && b) || not a

-- $ The keyword \"build_circuit\" causes an equivalent quantum function
-- to be built automatically. It will have the following name and
-- type:
-- 
-- > template_example1 :: Circ (Qubit -> Circ (Qubit -> Circ Qubit))
-- 
-- The various nested 'Circ' applications are an artifact, and can and
-- should be removed using the 'unpack' operator:
-- 
-- > (unpack template_example1) :: Qubit -> Qubit -> Circ Qubit

-- | This main function prints the circuit generated from 'example1'.
main1 :: IO ()
main1 =
  print_simple Preview (unpack template_example1)

-- | Here is some other boolean function. We do not use the
-- \"build_circuit\" keyword.
fake :: Bool -> Bool
fake b = not b

-- $ Suppose we want to use the function 'fake' as a subroutine
-- elsewhere:
{-
build_circuit
example2 :: Bool -> Bool -> Bool
example2 a b = fake (a && b) || not a
-}

-- | This will fail, because build_circuit does not know how to
-- translate the 'fake' function. 
-- 
-- We can fix this by manually providing a template. This is useful in
-- two situations:
-- 
-- 1. To provide a template for a Haskell built-in function;
-- 
-- 2. To provide a more efficient template for some function than the
-- one build_circuit can build automatically.
template_fake :: Circ (Qubit -> Circ Qubit)
template_fake = return f where
  f q = do
    qnot_at q
    return q

-- | Now that a template for 'fake' has been defined, the definition
-- of 'example2' works:
build_circuit
example2 :: Bool -> Bool -> Bool
example2 a b = fake (a && b) || not a


-- | This main function prints the circuit generated from 'example2'. 
main2 :: IO ()
main2 =
  print_simple Preview (unpack template_example2)

main = main2
