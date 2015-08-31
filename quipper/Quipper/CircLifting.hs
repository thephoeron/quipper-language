-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module provides a user-friendly interface to building
-- quantum circuits out of classical functions on booleans. It is
-- based on lower-level functionality provided by
-- "Libraries.Template".
-- 
-- Technically, the only functions to be used in this module are
-- @'decToCircMonad'@, a specialized version of @'decToMonad'@, and
-- @'unpack'@. The only useful datatype here is @'BoolParam'@.
-- 
-- One should not have to directly use the other things: they are only
-- for the internal use of Template Haskell to build quantum circuits
-- out of classical computation on booleans.
-- 
-- Note: in the following, we write circuits in ASCII form. The
-- following conventions are used. They are extended in obvious ways
-- when applicable (e.g. when writing a ternary gate).
-- 
-- > ---- : wire
-- > 
-- > 0 |-- : initialize an ancilla |0>
-- > 
-- > --| 0 : terminate an ancilla, asserting it was |0>
-- > 
-- >   +--+
-- >  -|  |- : a unary gate
-- >   +--+
-- > 
-- >   +--+
-- >  -|  |- 
-- >   |  |  : a binary gate
-- >  -|  |- 
-- >   +--+
-- >
-- >  -- --
-- >    X   : swap gate
-- >  -- --
-- > 
-- >  --x-- 
-- >    |   : controlled-not, applying NOT on the bottom wire if the top one is |1>
-- >  --N-- 
-- >
-- >  --o-- 
-- >    |   : controlled-not, applying NOT on the bottom wire if the top one is |0>
-- >  --N-- 

-- NOTE: They are only available because Template Haskell requires
-- them to be in a separate module and exported.

module Quipper.CircLifting (
  -- * Overview
  -- $ROLE 

  -- * A type of boolean parameters
  -- $BOOLPARAM 
  BoolParam(PTrue,PFalse),
  newBool,
  template_PFalse,
  template_PTrue,
    
  -- * Lifting classical functions to circuits
  -- $TH
  decToCircMonad,
  
-- $BUILDTEMPLATE_ANCHOR #build_circuit#
  
  -- * Syntactic sugar
  -- $BUILDTEMPLATE


  -- * Circuits for specific operations
  -- ** Boolean parameters
  
  template_newBool,

  -- ** Boolean constants
  template_False,
  template_True,
  -- ** Unary boolean operations
  template_not,
  -- ** Binary boolean operations
  template_symb_ampersand_symb_ampersand_,
  template_symb_vbar_symb_vbar_,
  template_bool_xor,
  -- ** The if-then-else operation
  -- $IF
  template_if,
  -- ** Equality test
  template_symb_equal_symb_equal_,

  -- * Generic unpacking
  CircLiftingUnpack(..)
  
) where

import Prelude
import Language.Haskell.TH as TH
import Data.Map as Map
import qualified Data.List

import Quipper.Monad
import qualified Quipper.Monad
import Quipper.Circuit
import Quipper.Generic
import Quipper.QData
import Libraries.Auxiliary (list_of_blist,blist_empty)
import Quipper.Control
import Quipper.QClasses

import Libraries.Template



----------------------------------------------------------------------
-- * Overview

-- $ROLE Using the tool @'decToMonad'@ designed in "Libraries.Template", we
-- can easily generate quantum circuits. Indeed, suppose that we are given the classical oracle 
-- 
-- > toyOracle :: Bool -> Bool
-- > toyOracle a = f (g a) (h a)
-- 
-- for some @g,h :: Bool -> Bool@ and @f :: Bool -> Bool -> Bool@. If
-- /g/ and /h/ are given by quantum circuits of the form
--
-- >          +-----+
-- > input ---|     |-- input wire, assumed to be not modified by the box
-- >          |     |
-- >      0 |-|     |--- output (was ancilla wire)
-- >          +-----+
--
-- and if /f/ is given by
--
-- >          +-----+
-- > input ---|     |-- was input 1, assumed to be not modified
-- >          |     | 
-- > input ---|     |-- was input 2, assumed to be not modified
-- >          |     |
-- >     0 |--|     |-- output (was ancilla wire),
-- >          +-----+
--
-- we can compositionally generate a circuit @C@ for /toyOracle/ as follows.
-- 
-- >          +---+                    +---+
-- > input ---|   |-- -----------------|   |-- (output of g)
-- >          | g |  X  +---+          |   |
-- >     0 |--|   |-- --|   |--- ------| f |-- (output of h)
-- >          +---+     | h |   X      |   |                   (I)
-- >     0 |------------|   |--- - ----|   |-- (output of f)
-- >                    +---+     X    +---+
-- >                          0 |- ----------- (input of g)
-- >
--
-- Note that the resulting circuit is a classical, reversible circuit
-- (more precisely, the circuit defines a one-to-one function). In
-- order to obtain a reversible quantum circuit, one should then apply
-- the function @'Quipper.Classical.classical_to_reversible'@ to get the following (we
-- keep the same convention of wires as in the definition of @C@):
--
-- >        +---+     +---+
-- > input--|   |-----|   |-- still the input
-- >        |   |     |   |
-- >   0 |--|   |-----|   |--| 0
-- >        | C |     | D |                                    (II)
-- >   0 |--|   |--x--|   |--| 0
-- >        |   |  |  |   |
-- >   0 |--|   |--|--|   |--| 0
-- >        +---+  |  +---+
-- >               |
-- > output wire---N--------------.
--
-- Here @D@ is the inverse of @C@. We now have a circuit of the
-- canonical form, computing and then uncomputing its ancillas:
--
-- >     +-----------+
-- > a --|           |- a
-- >     | toyOracle |
-- > z --|           |- z + (f (g a) (h a))
-- >     +-----------+
--
----------------------------------------------------------------------
-- * A type of boolean parameters

-- $BOOLPARAM During the construction of a quantum circuit from
-- classical code, the type 'Bool' is mapped to the type
-- 'Qubit'. However, it is also sometimes useful to specify boolean
-- parameters to be used during circuit generation (for example, in
-- the BWT algorithm, the color is a parameter). For this purpose, we
-- provide a new type 'BoolParam', which is identical to 'Bool' in
-- most respects, except that it is not mapped to 'Qubit' during
-- circuit generation.

-- | A custom-design boolean type, not modified by circuit generation.
data BoolParam = PTrue | PFalse
  deriving (Eq, Show)

-- | Type-cast from BoolParam to Bool
newBool :: BoolParam -> Bool
newBool PTrue = True
newBool PFalse = False


-- | Lifted version of PFalse.
template_PFalse :: Circ BoolParam
template_PFalse = return PFalse

-- | Lifted version of PTrue.
template_PTrue :: Circ BoolParam
template_PTrue = return PTrue


----------------------------------------------------------------------
-- * Lifting classical functions to circuits

-- $TH The main tool for transforming a classical computation into a
-- quantum circuit is the function @'decToCircMonad'@. It inputs the
-- syntax tree of a classical function, and outputs the syntax tree of
-- a corresponding quantum circuit. The type 'Bool' is mapped to
-- 'Qubit'; the type 'BoolParam' is unchanged; and each function /f/ :
-- /a/ → /b/ is mapped to a function /f'/ : /a'/ → 'Circ' /b'/,
-- where /a'/ and /b'/ are the translations of the types /a/ and /b/,
-- respectively.
-- 
-- Most of the work is done by the lower-level function 
-- @'decToMonad'@ from the module "Libraries.Template". 
-- This lower-level function knows how to deal with many usual
-- constructs of the Haskell language, such as function applications,
-- lambda-abstractions, let-assignments, case-distinctions, and so
-- on. However, @'decToMonad'@ does not by default know how to deal
-- with the base cases, i.e., how to extract quantum circuits from
-- specific term constants such as @'&&'@, @'||'@, etc.
-- 
-- The purpose of the remainder of this module is to do just that. For
-- every constant or function @XXX@ that one may want to use in a
-- classical program, we provide an implementation @template_XXX@ as a
-- quantum circuit.  We refer to @template_XXX@ as the \"lifted\"
-- version of @XXX@.  The function @'decToCircMonad'@ is a version of
-- @'decToMonad'@ that knows about these liftings.



-- | Input the syntax tree of a classical function, and output the
-- syntax tree of a corresponding quantum function. The type 'Bool' is
-- mapped to 'Qubit'; the type 'BoolParam' is unchanged; and and each
-- function /f/ : /a/ → /b/ is mapped to a function /f'/ : /a'/ →
-- 'Circ' /b'/, where /a'/ and /b'/ are the translations of the types
-- /a/ and /b/, respectively. The function 'decToCircMonad' knows
-- about many built-in operations such as @'&&'@ and @'||'@, whose
-- circuit translations are defined below.
decToCircMonad :: Q [Dec] -> Q [Dec]
decToCircMonad x = decToMonad "Circ" x

-- $BUILDTEMPLATE_ANCHOR #build_circuit#

---------------------------------------------------------------------
-- * Syntactic sugar

-- $BUILDTEMPLATE Quipper comes equipped with syntactic sugar to ease
-- the use of the @'decToCircMonad'@ function.
-- 
-- Although the code
-- 
-- > $( decToCircMonad [d| f x = ... |] )
-- 
-- is valid, it is possible to use the special keyword
-- @build_circuit@, as follows:
-- 
-- > build_circuit
-- > f x = ...
-- 
-- This code is equivalent to
-- 
-- > f x = ...
-- > $( decToCircMonad [d| f x = ... |] )
-- 
-- In other words, it generates both a function @f@ of type @a -> ...@
-- and an object @template_f@ of type @Circ (a -> Circ ...)@.
-- 
-- The following spellings are recognized:
--
-- > build_circuit f x y z = ...
--
-- > build_circuit
-- > f x y z = ...
--
-- > build_circuit
-- > f :: a -> ...
-- > f x y z = ...

-- ----------------------------------------------------------------------
-- * Circuits for specific operations

-- ** Boolean parameters

-- | Lifted version of 'newBool':
-- 
-- > newBool :: BoolParam -> Bool.
--
-- Depending on the boolean parameter, the circuit is either 
-- 
-- > 0 |--
-- 
-- or
-- 
-- > 1 |--
template_newBool ::  Circ (BoolParam -> Circ Qubit)
template_newBool =  return $ \b -> case b of 
                             PTrue  -> qinit_qubit True
                             PFalse -> qinit_qubit False

----------------------------------------------------------------------
-- ** Boolean constants

-- | Lifted version of 'False':
-- 
-- > False :: Bool.
-- 
-- The circuit is
--
-- > 0 |--   output: quantum bit in state |0>
template_False :: Circ Qubit
template_False = qinit_qubit False

-- | Lifted version of 'True':
-- 
-- > True :: Bool.
-- 
-- The circuit is
--
-- > 1 |--   output: quantum bit in state |1>
template_True :: Circ Qubit
template_True = qinit_qubit True



----------------------------------------------------------------------
-- ** Unary boolean operations

-- | Lifted version of 'not':
-- 
-- > not :: Bool -> Bool.
-- 
-- The circuit is 
-- 
-- > a -----x--
-- >        |
-- >   1 |--N------- output: not a.
template_not ::  Circ (Qubit -> Circ Qubit)
template_not  = return $ \b -> do
	  r <- qinit_qubit True;
          qnot_at r `controlled` b
	  return r


----------------------------------------------------------------------
-- ** Binary boolean operations

-- | Lifted version of '&&':
-- 
-- > (&&) :: Bool -> Bool -> Bool.
-- 
-- The circuit is
-- 
-- > a -----x---
-- >        |
-- > b -----x---
-- >        |
-- >   0 |--N------- output: a and b.
template_symb_ampersand_symb_ampersand_ ::  Circ (Qubit -> Circ (Qubit -> Circ Qubit))
template_symb_ampersand_symb_ampersand_ =
  return $ \b1 -> return $ \b2 -> do 
         r <- qinit_qubit False;
         qnot_at r `controlled` [b1,b2];
         return r

-- | Lifted version of '||':
-- 
-- > (||) :: Bool -> Bool -> Bool.
-- 
-- The circuit is
-- 
-- > a -----o---
-- >        |
-- > b -----o---
-- >        |
-- >   1 |--N------- output: a or b.
template_symb_vbar_symb_vbar_ ::  Circ (Qubit -> Circ (Qubit -> Circ Qubit))
template_symb_vbar_symb_vbar_ = return $ \b1 -> return $ \b2 -> do 
         r <- qinit_qubit True; 
         qnot_at r `controlled` b1 .==. 0 .&&. b2 .==. 0;
	 return r


-- | Lifted version of 'bool_xor':
-- 
-- > bool_xor :: Bool -> Bool -> Bool.
-- 
-- The circuit is
-- 
-- > a -----x-------
-- >        |
-- > b -----|---x---
-- >        |   |
-- >   0 |--N---N------ output: a xor b.
template_bool_xor ::  Circ (Qubit -> Circ (Qubit -> Circ Qubit))
template_bool_xor = return $ \b1 -> return $ \b2 -> do 
         r <- qinit_qubit False
	 qnot_at r `controlled` b1
         qnot_at r `controlled` b2
         return r


----------------------------------------------------------------------
-- ** The if-then-else operation

-- $IF The last term we need to build is @'template_if'@, a term
-- describing the if-then-else construct as a circuit.

-- | Lifted version of the @if-then-else@ construction: 
-- 
-- > if-then-else :: Bool -> b -> b -> b         
-- 
-- We only allow first-order terms in the \"then\" and \"else\"
-- clauses.  The circuit is:
--
-- > q -----x---o---
-- >        |   |
-- > a -----x---|---
-- >        |   |
-- > b -----|---x---
-- >        |   |
-- >   0 |--N---N-------- wire output of the function.
template_if :: (QData b) => Circ Qubit -> Circ b -> Circ b -> Circ b
template_if x a b = do
   x' <- x; a' <- a; b' <- b; map2Q (testOnQubit x') (a',b')
   where
   testOnQubit :: Qubit -> (Qubit,Qubit) -> Circ Qubit
   testOnQubit x (a,b) = do
       r <- qinit_qubit False
       qnot_at r `controlled` x .==. 1 .&&. a .==. 1
       qnot_at r `controlled` x .==. 0 .&&. b .==. 1
       return r

-- ----------------------------------------------------------------------
-- * Operations of the Eq class
       
-- | Lifted version of the '==' operator:
-- 
-- > (==) :: Eq a => a -> a -> Bool
template_symb_equal_symb_equal_ :: (QEq qa) => Circ (qa -> Circ (qa -> Circ Qubit))
template_symb_equal_symb_equal_ = return $ \qx -> return $ \qy -> do (qx,qy,test) <- q_is_equal qx qy; return test

-- ----------------------------------------------------------------------
-- * Generic unpacking

-- $ The 'decToCircMonad' function produces (and also requires)
-- functions with somewhat unwieldy types. We define generic functions
-- for unpacking these types into a more useable format, and for
-- packing them back.
-- 
-- For example, @'Circ' (qa -> 'Circ' (qb -> 'Circ' qd))@ unpacks
-- into the type @qa -> qb -> 'Circ' qd@.
-- 
-- The class 'CircLiftingUnpack' keeps track of the unpacked and
-- packed versions of types; so it will have an instance
-- 
-- > @'CircLiftingUnpack' ('Circ' (qa -> 'Circ' (qb -> 'Circ' qd))) (qa -> qb -> 'Circ' qd)@, 
-- 
-- and provide functions 'unpack', 'pack' going back and forth between
-- these.
-- 
-- Note that 'pack' and 'unpack' do not in general form an
-- isomorphism, just a retraction of the packed type onto the unpacked
-- type.
-- 
-- Unfortunately the class cannot (in the current implementation) be
-- defined in full generality once and for all: whenever a user wishes
-- to use a new type @QFoo@ in circuit-building functions, she must
-- define an additional base case @'CircLiftingUnpack' ('Circ' QFoo)
-- ('Circ' QFoo)@ (with 'pack' and 'unpack' the identity) to use this
-- class with types involving @QFoo@.
-- 
-- The crucial case is 
-- 
-- > instance ('CircLiftingUnpack' ('Circ' b) b') => 'CircLiftingUnpack' ('Circ' (a -> 'Circ' b)) (a -> b')@.
-- 
-- Unfortunately, this requires @-XUndecidableInstances@, for somewhat
-- subtle reasons (see
-- <http://hackage.haskell.org/trac/haskell-prime/wiki/FunctionalDependencies#Restrictionsoninstances>,
-- <http://hackage.haskell.org/trac/haskell-prime/wiki/FunctionalDependencies#Modifiedcoveragecondition>).
-- 
-- The current implementation is fairly restricted, working
-- essentially only for cases like the examples above.  One can define
-- the unpacking more generally; but this restriction keeps the
-- definition much simpler, and suffices for most (all?) of the
-- circuit-generation functions we use.

-- | The 'decToCircMonad' function produces (and also requires)
-- functions with somewhat unwieldy types. The 'CircLiftingUnpack'
-- class defines generic functions for unpacking these types into a
-- more useable format, and for packing them back.
-- 
-- For example, @'Circ' (qa -> 'Circ' (qb -> 'Circ' qd))@ unpacks into
-- the type @qa -> qb -> 'Circ' qd@.
-- 
-- Note that 'pack' and 'unpack' do not in general form an
-- isomorphism, just a retraction of the packed type onto the unpacked
-- type.
class CircLiftingUnpack packed unpacked | packed -> unpacked, unpacked -> packed where
  unpack :: packed -> unpacked
  pack :: unpacked -> packed

instance (CircLiftingUnpack (Circ b) b') => CircLiftingUnpack (Circ (a -> Circ b)) (a -> b') where
  unpack cf x = unpack $ do f <- cf; f x
  pack f = return $ \x -> pack (f x)

instance CircLiftingUnpack (Circ Qubit) (Circ Qubit) where
  pack x = x
  unpack x = x

instance CircLiftingUnpack (Circ [a]) (Circ [a]) where
  pack x = x
  unpack x = x

instance CircLiftingUnpack (Circ ()) (Circ ()) where
  pack x = x
  unpack x = x

instance CircLiftingUnpack (Circ (a,b)) (Circ (a,b)) where
  pack x = x
  unpack x = x

instance CircLiftingUnpack (Circ (a,b,c)) (Circ (a,b,c)) where
  pack x = x
  unpack x = x

instance CircLiftingUnpack (Circ (a,b,c,d)) (Circ (a,b,c,d)) where
  pack x = x
  unpack x = x

instance CircLiftingUnpack (Circ (a,b,c,d,e)) (Circ (a,b,c,d,e)) where
  pack x = x
  unpack x = x

instance CircLiftingUnpack (Circ (a,b,c,d,e,f)) (Circ (a,b,c,d,e,f)) where
  pack x = x
  unpack x = x

instance CircLiftingUnpack (Circ (a,b,c,d,e,f,g)) (Circ (a,b,c,d,e,f,g)) where
  pack x = x
  unpack x = x
