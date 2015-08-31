-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module introduces a simple way of defining \"boolean statements\"
-- acting over qubits. See "Algorithms.BF.Main" for an overview of the boolean 
-- formula algorithm.
module Algorithms.BF.QuantumIf where

import Quipper

-- ----------------------------------------------------------------------
-- * Quantum \"if then else\" statements


-- $ This section introduces a simple way of defining \"boolean statements\"
-- acting over qubits, that can then be used as the control in a quantum \"If
-- Then Else\" statement. The idea is that an ancilla is initialized that is in 
-- the state represented by the boolean statement, and is then used to control the
-- two branches of the \"If Then Else\", before being uncomputed. The boolean 
-- statements can contain \"and\", \"or\", and \"not\".

-- | We can use @(Boolean Qubit)@ to build up \"boolean statements\" over qubits
-- and use the \"boolean statement\" in an 'if_then_elseQ' construct.
--
-- > Example (for qubits a, b, c, d):
-- > (a and b) or !(c and !d) is written as:
-- > Or (And (A a) (A b)) (Not (And (A c) (Not (A d)))) 
data Boolean a = A a                         -- ^ 'A' /q/ means if /q/ == 'True'. 
               | Not (Boolean a)             -- ^ 'Not' /b/ means the negation of the boolean statement /b/.
               | And (Boolean a) (Boolean a) -- ^ 'And' /a/ /b/ means the and of the boolean statements /a/ and /b/.
               | Or (Boolean a) (Boolean a)  -- ^ 'Or' /a/ /b/ means the or of the boolean statements /a/ and /b/
     deriving Show

-- Set the precedence for infix operators 'And' and 'Or'.
infixr 3 `And` -- same precedence as (&&)
infixr 2 `Or`  -- same precedence as (||)

-- | Allow 'And' and 'Or' to be used as infix operators, with the same
-- precedences.

-- | Internally, a \"boolean statement\" is converted into a statement
--   that doesn't use /or/ (e.g., using De Morgan's laws).
data BooleanAnd a = AA a                               -- ^ 'AA' /q/ means if /q/ == 'True'.
                  | NotA (BooleanAnd a)                -- ^ 'NotA' /b/ means the negation of the boolean statement /b/.
                  | AndA (BooleanAnd a) (BooleanAnd a) -- ^ 'AndA' /a/ /b/ means the and of the boolean statements /a/ and /b/.

-- | Convert any boolean formula to a formula using just /and/ and /not/. This conversion function uses De Morgan's law,
--   i.e., 
-- 
-- > A or B = !( !A and !B ),
-- 
-- but does not remove double negations. For a version that also
-- removes double negations, see 'booleanToAnd'.
booleanToAnd' :: Boolean a -> BooleanAnd a
booleanToAnd' (A a) = AA a
booleanToAnd' (Not ba) = NotA (booleanToAnd' ba)
booleanToAnd' (And ba ba') = AndA (booleanToAnd' ba) (booleanToAnd' ba')
booleanToAnd' (Or ba ba') = NotA (AndA (NotA (booleanToAnd' ba)) (NotA (booleanToAnd' ba')))

-- | Strip any redundant double negations,
--   i.e., in this context @!!A = A@.
stripDoubleNot :: BooleanAnd a -> BooleanAnd a
stripDoubleNot (AA a) = AA a
stripDoubleNot (NotA (NotA ba)) = stripDoubleNot ba
stripDoubleNot (NotA ba) = NotA (stripDoubleNot ba)
stripDoubleNot (AndA ba ba') = AndA (stripDoubleNot ba) (stripDoubleNot ba')

-- | Convert any boolean formula to a formula using just /and/ and
-- /not/, removing double negations.
booleanToAnd :: Boolean a -> BooleanAnd a
booleanToAnd ba = stripDoubleNot (booleanToAnd' ba)

-- | Create a circuit from the \"boolean statement\".
booleanAnd' :: BooleanAnd Qubit -> Qubit -> Circ ()
booleanAnd' (AA q') q = do
    qnot_at q `controlled` q'
    return ()
booleanAnd' (NotA ba) q = do
    anc <- qinit False
    qnot_at anc
    booleanAnd' ba anc
    qnot_at q `controlled` anc
booleanAnd' (AndA ba ba') q = do
    anc0 <- qinit False
    booleanAnd' ba anc0
    anc1 <- qinit False
    booleanAnd' ba' anc1
    qnot_at q `controlled` [anc0,anc1]

-- | Create a circuit from the \"boolean statement\", passing in an ancilla.
booleanAnd :: BooleanAnd Qubit -> Circ Qubit
booleanAnd baq = do
  anc <- qinit False
  booleanAnd' baq anc
  return anc 

-- | The definition of a quantum if_then_else structure
-- uses a \"boolean statement\" to create a single ancilla in the state defined by
-- the boolean statement, and uses this as a control for the two branches of the
-- if statement. The ancilla then needs to be uncomputed, this is achieved using
-- the other given \"boolean statement\", i.e., a new boolean statement that would
-- produce the state of the control ancilla, from the output state of the two
-- branches.This allows the branches to update the state of qubits used in the 
-- original \"boolean statement\" as long as it is done in a 
-- (reversible) known-manner.
-- This is useful for the WALK algorithm, where TOPARENT and TOCHILD are controlled
-- by the state of the direction register, but also change the state of the
-- direction register.   
if_then_elseQinv :: Boolean Qubit -> Circ () -> Circ () -> Boolean Qubit -> Circ ()
if_then_elseQinv b_in i e b_out = do
  with_ancilla $ \if_control -> do
    with_computed (booleanAnd (booleanToAnd b_in)) $ \anc -> do
      qnot_at if_control `controlled` anc
    with_controls if_control $ do
      i
    with_controls (if_control .==. False) $ do
       e
    with_computed (booleanAnd (booleanToAnd b_out)) $ \anc -> do
      qnot_at if_control `controlled` anc    

-- | Like 'if_then_elseQinv', but where the original \"boolean statement\" still
-- holds after the branches have taken place.
if_then_elseQ :: Boolean Qubit -> Circ () -> Circ () -> Circ ()
if_then_elseQ b i e = do
  with_computed (booleanAnd (booleanToAnd b)) $ \if_control -> do
    with_controls if_control $ do
      i
    with_controls (if_control .==. False) $ do
      e     
