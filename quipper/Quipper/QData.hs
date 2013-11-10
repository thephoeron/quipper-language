-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS -fcontext-stack=50 #-}

-- -O0 is needed for this file, because -O1 triggers a compiler bug in
-- ghc 7.2.2 (see http://hackage.haskell.org/trac/ghc/ticket/6168),
-- and -O2 triggers a different compiler bug in ghc 7.2.2

{-# OPTIONS_GHC -O0 #-}

-- | This module provides type classes for dealing with various
-- \"shaped\" quantum and classical data structures. Examples of data
-- structures are tuples, lists, records, registers, arrays, indexed
-- arrays, etc. Is it convenient to extend certain operations to
-- arbitrary quantum data structures; for example, instead of
-- measuring a single qubit and obtaining a bit, one may measure an
-- /n/-tuple of qubits and obtain an /n/-tuple of bits. We call an
-- operation \"generic\" if it can act on arbitrary data structures. 
-- 
-- This module provides shaped types and low-level combinators, in
-- terms of which higher-level generic quantum operations can be
-- defined. 
-- 
-- The low-level combinators provided by this module (with names
-- /qcdata_*/ and /qdata_*/) should never be used directly in user
-- code (and for this reason, they are not re-exported by
-- "Quipper"). Instead, they are intended as building blocks for
-- user-level generic functions (in "Quipper.Generic" and related
-- modules). The only exception is that the functions may be used in
-- libraries or user-level code to define new quantum data
-- constructors. Modules that contain such definitions should import
-- 'Quipper.Internal'.

module Quipper.QData where

-- import other Quipper stuff
import Quipper.Monad
import Libraries.Auxiliary
import Libraries.Tuple
import Quipper.Labels
import Quipper.Transformer
import Quipper.Control

import Data.Typeable
import Libraries.Typeable
import Control.Monad.State

-- ======================================================================
-- * Introduction

-- $ The data types we consider here come in two varieties:
-- /homogeneous/ and /heterogeneous/ types.
-- 
-- A /homogeneous/ data type describes a data structure that is built
-- up from only one kind of basic data (for example, only qubits, only
-- classical bits, or only boolean parameters). The following are
-- typical examples of homogeneous types:
-- 
-- > qa = (Qubit, Qubit, [Qubit])
-- > ca = (Bit, Bit, [Bit])
-- > ba = (Bool, Bool, [Bool]).
-- 
-- An important feature of homogeneous types is that they can be
-- related to each other by shape. For example, /ca/ above is the
-- \"classical version\" of /qa/. We say that the above types /qa/,
-- /ca/, and /ba/ all share the same /shape type/. On the other hand,
-- they differ in their /leaf types/, which are 'Qubit', 'Bit', and
-- 'Bool', respectively.
-- 
-- When naming types, variables, and operations related to homogeneous
-- data structures, we often use letters such as /q/, /c/, and /b/ to
-- denote, respectively, the quantum, classical, and boolean versions
-- of some concept.
-- 
-- Homogeneous types are made available to Quipper programs via the
-- 'QData' and 'QShape' type classes.
-- 
-- A /heterogeneous/ data type describes a data structure that may
-- contain both classical and quantum bits. A typical example of a
-- heterogeneous type is:
-- 
-- > qc = (Qubit, Bit, [Qubit]).
-- 
-- Heterogeneous types are often used to represent sets of
-- endpoints of a circuit, or the inputs or outputs to some circuit
-- building function. We often use the letters /qc/ in connection with
-- heterogeneous types.
-- 
-- Heterogeneous types are made available to Quipper programs via the
-- 'QCData' and 'QCDataPlus' type classes.

-- ======================================================================
-- * Primitive definitions

-- $ The type classes of this module are all derived from four
-- primitive items, which must be defined by induction on types:
-- 
-- * A type class 'QCData' /qc/, representing structured data types
-- made up from classical and quantum leaves.
-- 
-- * A type family 'QCType' /x/ /y/ /qc/, representing the type-level
-- substitution operation [nobr /qc/ [/x/ \/ 'Qubit', /y/ \/ 'Bit']].
-- 
-- * A type family 'QTypeB' /ba/, representing the type-level substitution
-- [nobr /ba/ ['Qubit' \/ 'Bool']].
-- 
-- * A type class 'SimpleType' /qc/, representing \"simple\" data
-- types. We say that a data type /t/ is \"simple\" if any two
-- elements of /t/ have the same number of leaves. For example, tuples
-- are simple, but lists are not.
-- 
-- An instance of 'QCData', 'QCType' and 'QTypeB' must be defined for
-- each new kind of quantum data. If the quantum data is simple, an
-- instance of 'SimpleType' must also be defined.
-- 
-- All other notions in this module are defined in terms of the above
-- four, and therefore need not be defined on a per-type basis.

-- ----------------------------------------------------------------------
-- ** The QCType operation

-- | The type 'QCType' /x/ /y/ /a/ represents the substitution
-- [nobr /a/ [/x/ \/ 'Qubit', /y/ \/ 'Bit']]. For example:
-- 
-- > QCType x y (Qubit, Bit, [Qubit]) = (x, y, [x]).
-- 
-- An instance of this must be defined for each new kind of quantum
-- data.
type family QCType x y a
type instance QCType x y Qubit = x
type instance QCType x y Bit = y

type instance QCType x y () = ()
type instance QCType x y (a,b) = (QCType x y a, QCType x y b)
type instance QCType x y (a,b,c) = (QCType x y a, QCType x y b, QCType x y c)
type instance QCType x y (a,b,c,d) = (QCType x y a, QCType x y b, QCType x y c, QCType x y d)
type instance QCType x y (a,b,c,d,e) = (QCType x y a, QCType x y b, QCType x y c, QCType x y d, QCType x y e)
type instance QCType x y (a,b,c,d,e,f) = (QCType x y a, QCType x y b, QCType x y c, QCType x y d, QCType x y e, QCType x y f)
type instance QCType x y (a,b,c,d,e,f,g) = (QCType x y a, QCType x y b, QCType x y c, QCType x y d, QCType x y e, QCType x y f, QCType x y g)
type instance QCType x y (a,b,c,d,e,f,g,h) = (QCType x y a, QCType x y b, QCType x y c, QCType x y d, QCType x y e, QCType x y f, QCType x y g, QCType x y h)
type instance QCType x y (a,b,c,d,e,f,g,h,i) = (QCType x y a, QCType x y b, QCType x y c, QCType x y d, QCType x y e, QCType x y f, QCType x y g, QCType x y h, QCType x y i)
type instance QCType x y (a,b,c,d,e,f,g,h,i,j) = (QCType x y a, QCType x y b, QCType x y c, QCType x y d, QCType x y e, QCType x y f, QCType x y g, QCType x y h, QCType x y i, QCType x y j)
type instance QCType x y [a] = [QCType x y a]
type instance QCType x y (B_Endpoint a b) = B_Endpoint (QCType x y a) (QCType x y b)
type instance QCType x y (Signed a) = Signed (QCType x y a)

-- ----------------------------------------------------------------------
-- ** The QTypeB operation

-- | The type 'QTypeB' /ba/ represents the substitution
-- [nobr /ba/ ['Qubit' \/ 'Bool']]. For example: 
-- 
-- > QTypeB (Bool, Bool, [Bool]) = (Qubit, Qubit, [Qubit]).
-- 
-- An instance of this must be defined for each new kind of quantum data.
type family QTypeB a
type instance QTypeB Bool = Qubit
type instance QTypeB () = ()
type instance QTypeB (a,b) = (QTypeB a, QTypeB b)
type instance QTypeB (a,b,c) = (QTypeB a, QTypeB b, QTypeB c)
type instance QTypeB (a,b,c,d) = (QTypeB a, QTypeB b, QTypeB c, QTypeB d)
type instance QTypeB (a,b,c,d,e) = (QTypeB a, QTypeB b, QTypeB c, QTypeB d, QTypeB e)
type instance QTypeB (a,b,c,d,e,f) = (QTypeB a, QTypeB b, QTypeB c, QTypeB d, QTypeB e, QTypeB f)
type instance QTypeB (a,b,c,d,e,f,g) = (QTypeB a, QTypeB b, QTypeB c, QTypeB d, QTypeB e, QTypeB f, QTypeB g)
type instance QTypeB (a,b,c,d,e,f,g,h) = (QTypeB a, QTypeB b, QTypeB c, QTypeB d, QTypeB e, QTypeB f, QTypeB g, QTypeB h)
type instance QTypeB (a,b,c,d,e,f,g,h,i) = (QTypeB a, QTypeB b, QTypeB c, QTypeB d, QTypeB e, QTypeB f, QTypeB g, QTypeB h, QTypeB i)
type instance QTypeB (a,b,c,d,e,f,g,h,i,j) = (QTypeB a, QTypeB b, QTypeB c, QTypeB d, QTypeB e, QTypeB f, QTypeB g, QTypeB h, QTypeB i, QTypeB j)
type instance QTypeB [a] = [QTypeB a]
type instance QTypeB (B_Endpoint a b) = B_Endpoint (QTypeB a) (QTypeB b)
type instance QTypeB (Signed a) = Signed (QTypeB a)

-- ----------------------------------------------------------------------
-- ** The QCData class

-- $ The 'QCData' class provides only three primitive combinators:
-- 'qcdata_mapM', 'qcdata_zip', and 'qcdata_promote'. These are
-- sufficient to define all other shape-generic operations.
-- 
-- An instance of this must be defined for each new kind of quantum data.
-- 
-- The functions 'qcdata_mapM' and 'qcdata_zip' require \"shape type
-- parameters\". These are dummy arguments whose /value/ is ignored,
-- but whose /type/ is used to determine the shape of the data to map
-- over. The dummy terms @'qubit' :: 'Qubit'@ and @'bit' :: 'Bit'@ may
-- be used to represent leaves in shape type arguments.
-- 
-- Note to programmers defining new 'QCData' instances: Instances
-- /must/ ensure that the functions 'qcdata_mapM' and 'qcdata_zip'
-- do not evaluate their dummy arguments. These arguments will often
-- be 'undefined'. In particular, if using a pattern match on this
-- argument, only a variable or a /lazy/ pattern can be used.

-- | The 'QCData' type class contains heterogeneous data types built
-- up from leaves of type 'Qubit' and 'Bit'. It is the basis for
-- several generic operations that apply to classical and quantum
-- data, such as copying, transformers, simulation, and heterogeneous
-- versions of qterm and qdiscard.
-- 
-- 'QCData' and 'QData' are interrelated, in the sense that the
-- following implications hold:
-- 
-- > QData qa   implies   QCData qa
-- > CData ca   implies   QCData ca
--  
-- Implications in the converse direction also hold whenever /qc/ is a
-- fixed known type:
-- 
-- > QCData qc   implies   QData (QType qc)
-- > QCData qc   implies   CData (CType qc)
-- > QCData qc   implies   BData (BType qc)
-- 
-- However, the type checker cannot prove the above implication in the
-- case where /qc/ is a type variable; for this, the more flexible
-- (but more computationally expensive) 'QCDataPlus' class can be used.

class (Labelable qc String, 
       Typeable qc,
       Show qc,
       Show (LType qc),
       qc ~ QCType Qubit Bit qc,
       CType (QType qc) ~ CType qc,
       BType (CType qc) ~ BType qc,
       QCType Int Bool (CType qc) ~ BType qc
      ) => QCData qc where
  -- | Map two functions /f/ and /g/ over all the leaves of a
  -- heterogeneous data structure. Apply /f/ to all the leaves at
  -- 'Qubit' positions, and 'g' to all the leaves at 'Bit' positions.
  -- The first argument is a shape type parameter.
  -- 
  -- Example (ignoring the monad for the sake of simplicity):
  -- 
  -- > qcdata_mapM (qubit, bit, [qubit]) f g (x,y,[z,w]) = (f x, g y, [f z, f w]).
  -- 
  -- For data types that have a sense of direction, the mapping should
  -- preferably be performed from left to right, but this property is
  -- not guaranteed and may change without notice. 
  qcdata_mapM :: (Monad m) => qc -> (q -> m q') -> (c -> m c') -> QCType q c qc -> m (QCType q' c' qc)
  
  -- | Zip two heterogeneous data structures together, to obtain a new
  -- data structure of the same shape, whose elements are pairs of the
  -- corresponding elements of the input data structures. The zipping
  -- is /strict/, meaning that both input data structure must have
  -- exactly the same shape (same length of lists, etc). The first
  -- five arguments are shape type parameters, representing the shape
  -- of the data structure, the two leaf types of the first data
  -- structure, and the two leaf types of the second data structure,
  -- respectively.
  -- 
  -- Example:
  -- 
  -- > qcdata_zip (bit, [qubit]) int bool char string (True, [2,3]) ("b", ['c', 'd']) = ((True, "b"), [(2,'c'), (3,'d')])
  -- > where the shape parameters are:
  -- >   int = dummy :: Int
  -- >   bool = dummy :: Bool
  -- >   char = dummy :: Char
  -- >   string = dummy :: String  
  -- 
  -- The 'ErrMsg' argument is a stub error message to be used in
  -- case of failure.
  qcdata_zip :: qc -> q -> c -> q' -> c' -> QCType q c qc -> QCType q' c' qc -> ErrMsg -> QCType (q, q') (c, c') qc
  
  -- | It is sometimes convenient to have a boolean parameter with
  -- some aspect of its shape indeterminate. The function
  -- 'qcdata_promote' takes such a boolean parameter, as well as a
  -- piece of 'QCData', and attempts to set the shape of the former to
  -- that of the latter.
  -- 
  -- The kinds of promotions that are allowed depend on the data type.
  -- For example, for simple types, 'qcdata_promote' has no work to
  -- do and should just return the first argument. For types that are
  -- not simple, but where no promotion is desired (e.g. 'Qureg'),
  -- 'qcdata_promote' should check that the shapes of the first and
  -- second argument agree, and throw an error otherwise. For lists,
  -- we allow a longer list to be promoted to a shorter one, but not
  -- the other way around. For quantum integers, we allow an integer
  -- of indeterminate length to be promoted to a determinate length,
  -- but we do not allow a determinate length to be changed to another
  -- determinate length.
  -- 
  -- The 'ErrMsg' argument is a stub error message to be used in
  -- case of failure.
  qcdata_promote :: BType qc -> qc -> ErrMsg -> BType qc

instance QCData Qubit where
  qcdata_mapM shape f g = f
  qcdata_zip shape q c q' c' x y e = (x, y)
  qcdata_promote a x e = a

instance QCData Bit where
  qcdata_mapM shape f g = g
  qcdata_zip shape q c q' c' x y e = (x, y)
  qcdata_promote a x e = a

instance QCData () where
  qcdata_mapM shape f g x = return ()
  qcdata_zip shape q c q' c' x y e = ()
  qcdata_promote a x e = a
  
instance (QCData a, QCData b) => QCData (a,b) where
  qcdata_mapM ~(a,b) f g (x,y) = do
    x' <- qcdata_mapM a f g x
    y' <- qcdata_mapM b f g y
    return (x', y')
  qcdata_zip ~(a,b) q c q' c' (x1, x2) (y1, y2) e = (z1, z2) where
    z1 = qcdata_zip a q c q' c' x1 y1 e
    z2 = qcdata_zip b q c q' c' x2 y2 e
  qcdata_promote (a,b) (x,y) e = (qcdata_promote a x e, qcdata_promote b y e)

instance (QCData a, QCData b, QCData c) => QCData (a,b,c) where
  qcdata_mapM s f g xs = mmap tuple $ qcdata_mapM (untuple s) f g (untuple xs)
  qcdata_zip s q c q' c' xs ys e = tuple $ qcdata_zip (untuple s) q c q' c' (untuple xs) (untuple ys) e
  qcdata_promote a x s = tuple $ qcdata_promote (untuple a) (untuple x) s
  
instance (QCData a, QCData b, QCData c, QCData d) => QCData (a,b,c,d) where
  qcdata_mapM s f g xs = mmap tuple $ qcdata_mapM (untuple s) f g (untuple xs)
  qcdata_zip s q c q' c' xs ys e = tuple $ qcdata_zip (untuple s) q c q' c' (untuple xs) (untuple ys) e
  qcdata_promote a x s = tuple $ qcdata_promote (untuple a) (untuple x) s
  
instance (QCData a, QCData b, QCData c, QCData d, QCData e) => QCData (a,b,c,d,e) where
  qcdata_mapM s f g xs = mmap tuple $ qcdata_mapM (untuple s) f g (untuple xs)
  qcdata_zip s q c q' c' xs ys e = tuple $ qcdata_zip (untuple s) q c q' c' (untuple xs) (untuple ys) e
  qcdata_promote a x s = tuple $ qcdata_promote (untuple a) (untuple x) s
  
instance (QCData a, QCData b, QCData c, QCData d, QCData e, QCData f) => QCData (a,b,c,d,e,f) where
  qcdata_mapM s f g xs = mmap tuple $ qcdata_mapM (untuple s) f g (untuple xs)
  qcdata_zip s q c q' c' xs ys e = tuple $ qcdata_zip (untuple s) q c q' c' (untuple xs) (untuple ys) e
  qcdata_promote a x s = tuple $ qcdata_promote (untuple a) (untuple x) s
  
instance (QCData a, QCData b, QCData c, QCData d, QCData e, QCData f, QCData g) => QCData (a,b,c,d,e,f,g) where
  qcdata_mapM s f g xs = mmap tuple $ qcdata_mapM (untuple s) f g (untuple xs)
  qcdata_zip s q c q' c' xs ys e = tuple $ qcdata_zip (untuple s) q c q' c' (untuple xs) (untuple ys) e
  qcdata_promote a x s = tuple $ qcdata_promote (untuple a) (untuple x) s
  
instance (QCData a, QCData b, QCData c, QCData d, QCData e, QCData f, QCData g, QCData h) => QCData (a,b,c,d,e,f,g,h) where
  qcdata_mapM s f g xs = mmap tuple $ qcdata_mapM (untuple s) f g (untuple xs)
  qcdata_zip s q c q' c' xs ys e = tuple $ qcdata_zip (untuple s) q c q' c' (untuple xs) (untuple ys) e
  qcdata_promote a x s = tuple $ qcdata_promote (untuple a) (untuple x) s
  
instance (QCData a, QCData b, QCData c, QCData d, QCData e, QCData f, QCData g, QCData h, QCData i) => QCData (a,b,c,d,e,f,g,h,i) where
  qcdata_mapM s f g xs = mmap tuple $ qcdata_mapM (untuple s) f g (untuple xs)
  qcdata_zip s q c q' c' xs ys e = tuple $ qcdata_zip (untuple s) q c q' c' (untuple xs) (untuple ys) e
  qcdata_promote a x s = tuple $ qcdata_promote (untuple a) (untuple x) s

instance (QCData a, QCData b, QCData c, QCData d, QCData e, QCData f, QCData g, QCData h, QCData i, QCData j) => QCData (a,b,c,d,e,f,g,h,i,j) where
  qcdata_mapM s f g xs = mmap tuple $ qcdata_mapM (untuple s) f g (untuple xs)
  qcdata_zip s q c q' c' xs ys e = tuple $ qcdata_zip (untuple s) q c q' c' (untuple xs) (untuple ys) e
  qcdata_promote a x s = tuple $ qcdata_promote (untuple a) (untuple x) s

instance (QCData a) => QCData [a] where
  qcdata_mapM ~[a] f g xs = do
    sequence [ qcdata_mapM a f g x | x <- xs]
  qcdata_zip ~[a] q c q' c' xs ys e = zs where
    zs = [ qcdata_zip a q c q' c' x y e | (x, y) <- zip_strict_errmsg xs ys errmsg]
    errmsg = e ("lists differ in length: " ++ show (length xs) ++ " " ++ show (length ys))
  qcdata_promote as xs e = 
    [ qcdata_promote a x e | (a,x) <- zip_rightstrict_errmsg as xs errmsg ]
    where
      errmsg = e "list too short"

instance (QCData a, QCData b) => QCData (B_Endpoint a b) where
  qcdata_mapM ~(Endpoint_Qubit a) f g (Endpoint_Qubit x) = do
    x' <- qcdata_mapM a f g x
    return (Endpoint_Qubit x')
  qcdata_mapM ~(Endpoint_Bit b) f g (Endpoint_Bit y) = do
    y' <- qcdata_mapM b f g y
    return (Endpoint_Bit y')
  qcdata_zip ~(Endpoint_Qubit a) q c q' c' (Endpoint_Qubit x) (Endpoint_Qubit y) e = (Endpoint_Qubit z) where
    z = qcdata_zip a q c q' c' x y e
  qcdata_zip ~(Endpoint_Bit b) q c q' c' (Endpoint_Bit x) (Endpoint_Bit y) e = (Endpoint_Bit z) where
    z = qcdata_zip b q c q' c' x y e
  qcdata_zip shape q c q' c' x y e = error errmsg where
    errmsg = e "mismatching endpoint"
  qcdata_promote ~(Endpoint_Qubit a) (Endpoint_Qubit x) e = Endpoint_Qubit z where
    z = qcdata_promote a x e
  qcdata_promote ~(Endpoint_Bit b) (Endpoint_Bit y) e = Endpoint_Bit z where
    z = qcdata_promote b y e

instance (QCData a) => QCData (Signed a) where
  qcdata_mapM ~(Signed a _) f g ~(Signed x b) = do
    x' <- qcdata_mapM a f g x
    return (Signed x' b)
  qcdata_zip ~(Signed a _) q c q' c' (Signed x1 b1) (Signed x2 b2) e = (Signed z b) where
    z = qcdata_zip a q c q' c' x1 x2 e
    b = if b1 == b2 then b1 else error (e "signs of controls do not match")
  qcdata_promote ~(Signed a _) (Signed x b) e = (Signed x' b) where
    x' = qcdata_promote a x e
  
-- ----------------------------------------------------------------------
-- Parameter types
    
-- Parameter types (such as Int) are also instances of QCData. 
-- These should be regarded as quantum types that are "all shape" and
-- "no qubits".
  
-- Integers are parameters

type instance QCType x y Integer = Integer 

type instance QTypeB Integer = Integer

instance QCData Integer where
  qcdata_mapM shape f g n = return n
  qcdata_zip shape q c a' c' n m e 
    | n == m = n 
    | otherwise = error errmsg 
    where
      errmsg = e "mismatching Integer parameter"
  qcdata_promote a x e
    | a == x = a
    | otherwise = error errmsg
    where
      errmsg = e "mismatching Integer parameter"

-- Ints are parameters

type instance QCType x y Int = Int 

type instance QTypeB Int = Int

instance QCData Int where
  qcdata_mapM shape f g n = return n
  qcdata_zip shape q c a' c' n m e 
    | n == m = n 
    | otherwise = error errmsg 
    where
      errmsg = e "mismatching Int parameter"
  qcdata_promote a x e
    | a == x = a
    | otherwise = error errmsg
    where
      errmsg = e "mismatching Int parameter"

-- Doubles are parameters

type instance QCType x y Double = Double 

type instance QTypeB Double = Double

instance QCData Double where
  qcdata_mapM shape f g n = return n
  qcdata_zip shape q c a' c' n m e 
    | n == m = n 
    | otherwise = error errmsg 
    where
      errmsg = e "mismatching Double parameter"
  qcdata_promote a x e
    | a == x = a
    | otherwise = error errmsg
    where
      errmsg = e "mismatching Double parameter"

-- Floats are parameters

type instance QCType x y Float = Float 

type instance QTypeB Float = Float

instance QCData Float where
  qcdata_mapM shape f g n = return n
  qcdata_zip shape q c a' c' n m e 
    | n == m = n 
    | otherwise = error errmsg 
    where
      errmsg = e "mismatching Float parameter"
  qcdata_promote a x e
    | a == x = a
    | otherwise = error errmsg
    where
      errmsg = e "mismatching Float parameter"

-- Chars are parameters

type instance QCType x y Char = Char 

type instance QTypeB Char = Char

instance QCData Char where
  qcdata_mapM shape f g n = return n
  qcdata_zip shape q c a' c' n m e 
    | n == m = n 
    | otherwise = error errmsg 
    where
      errmsg = e "mismatching Char parameter"
  qcdata_promote a x e
    | a == x = a
    | otherwise = error errmsg
    where
      errmsg = e "mismatching Char parameter"


-- ----------------------------------------------------------------------
-- ** The SimpleType class

-- | 'SimpleType' is a subclass of 'QCData' consisting of simple
-- types. We say that a data type /t/ is \"simple\" if any two
-- elements of /t/ have the same number of leaves. For example, tuples
-- are simple, but lists are not.

class QCData qc => SimpleType qc where
  -- | Produce a term of the given shape. This term will contain
  -- well-defined data constructors, but may be 'undefined' at the
  -- leaves.
  fs_shape :: qc
  
instance SimpleType Qubit where
  fs_shape = qubit
  
instance SimpleType Bit where
  fs_shape = bit

instance SimpleType () where
  fs_shape = ()
  
instance (SimpleType a, SimpleType b) => SimpleType (a,b) where
  fs_shape = (fs_shape, fs_shape)

instance (SimpleType a, SimpleType b, SimpleType c) => SimpleType (a,b,c) where
  fs_shape = tuple fs_shape

instance (SimpleType a, SimpleType b, SimpleType c, SimpleType d) => SimpleType (a,b,c,d) where
  fs_shape = tuple fs_shape

instance (SimpleType a, SimpleType b, SimpleType c, SimpleType d, SimpleType e) => SimpleType (a,b,c,d,e) where
  fs_shape = tuple fs_shape

instance (SimpleType a, SimpleType b, SimpleType c, SimpleType d, SimpleType e, SimpleType f) => SimpleType (a,b,c,d,e,f) where
  fs_shape = tuple fs_shape

instance (SimpleType a, SimpleType b, SimpleType c, SimpleType d, SimpleType e, SimpleType f, SimpleType g) => SimpleType (a,b,c,d,e,f,g) where
  fs_shape = tuple fs_shape

instance (SimpleType a, SimpleType b, SimpleType c, SimpleType d, SimpleType e, SimpleType f, SimpleType g, SimpleType h) => SimpleType (a,b,c,d,e,f,g,h) where
  fs_shape = tuple fs_shape

instance (SimpleType a, SimpleType b, SimpleType c, SimpleType d, SimpleType e, SimpleType f, SimpleType g, SimpleType h, SimpleType i) => SimpleType (a,b,c,d,e,f,g,h,i) where
  fs_shape = tuple fs_shape

instance (SimpleType a, SimpleType b, SimpleType c, SimpleType d, SimpleType e, SimpleType f, SimpleType g, SimpleType h, SimpleType i, SimpleType j) => SimpleType (a,b,c,d,e,f,g,h,i,j) where
  fs_shape = tuple fs_shape

-- ======================================================================
-- * Type conversions
  
-- $ We define convenient abbreviations for conversions to, or
-- between, homogeneous types.

-- | The type operator 'QType' converts a classical or heterogeneous
-- type to a homogeneous quantum type. More precisely, the type
-- 'QType' /a/ represents the substitution [nobr /a/ ['Qubit' \/ 'Bit']]. 
-- It can be applied to both homogeneous and heterogeneous types, and
-- always yields a homogeneous type. For example:
-- 
-- > QType (Bit, [Bit]) = (Qubit, [Qubit])
-- > QType (Qubit, Bit) = (Qubit, Qubit)
type QType a = QCType Qubit Qubit a

-- | The type operator 'CType' converts a classical or heterogeneous
-- type to a homogeneous quantum type. More precisely, the type
-- 'CType' /a/ represents the substitution [nobr /a/ ['Bit' \/ 'Qubit']]. It
-- can be applied to both homogeneous and heterogeneous types, and
-- always yields a homogeneous type. For example:
-- 
-- > CType (Qubit, [Qubit]) = (Bit, [Bit])
-- > CType (Qubit, Bit) = (Bit, Bit)
type CType a = QCType Bit Bit a

-- | The type operator 'BType' converts a classical, quantum, or
-- heterogeneous type to a homogeneous boolean type. More precisely,
-- the type 'BType' /a/ represents the substitution
-- [nobr /a/ ['Bool' \/ 'Qubit', 'Bool' \/ 'Bit']]. It can be applied to
-- both homogeneous and heterogeneous types, and always yields a
-- homogeneous type. For example:
-- 
-- > BType (Qubit, [Qubit]) = (Bool, [Bool])
-- > BType (Qubit, Bit) = (Bool, Bool)
type BType a = QCType Bool Bool a

-- | The type operator 'HType' /x/ converts a classical, quantum, or
-- boolean type to a homogeneous type with leaves /x/. More precisely,
-- the type 'HType' /x/ /a/ represents the substitution
-- [nobr /a/ [/x/ \/ 'Qubit', /x/ \/ 'Bit']].
-- For example:
-- 
-- > HType x (Qubit, [Qubit]) = (x, [x])
-- > HType x (Qubit, Bit) = (x, x)
-- 
-- There is a very subtle difference between 'HType' /x/ /a/ and
-- 'QCType' /x/ /x/ /a/. Although these two types are equal for all
-- /x/ and /a/, the type checker cannot actually prove that 'QCType'
-- /x/ /x/ /a/ is homogeneous from the assumption 'QCData' /a/. It
-- can, however, prove that 'HType' /x/ /a/ is homogeneous. Therefore
-- 'HType' (or the slightly more efficient special cases 'QType',
-- 'CType', 'BType') should always be used to create a homogeneous
-- type from a heterogeneous one.
type HType leaf qa = QCType leaf leaf (QType qa)

-- | Construct the shape of a classical type.
--type CShape ca = HShape Bit ca

-- ======================================================================
-- * Shape parameters

-- $ Several operations, such as 'qcdata_mapM' and 'qcdata_zip',
-- require a \"shape type parameter\". The purpose of such a parameter
-- is only to fix a type; its value is completely unused. 
-- 
-- [Introduction to shape type parameters]
-- 
-- $ The need for shape type parameters arises when dealing with a
-- data structure whose leaves are of some arbitrary type, rather than
-- 'Qubit', 'Bit', or 'Bool'. For example, consider the data structure
-- 
-- > [(1, 2), (3, 4)]
-- 
-- This could be parsed in several different ways:
-- 
-- * as a data structure [(/leaf/, /leaf/), (/leaf/, /leaf/)], where each leaf
-- is an integer;
--
-- * as a data structure [/leaf/, /leaf/], where each leaf is a pair of
-- integers;
-- 
-- * as a data structure /leaf/, where each leaf is a list of pairs of
-- integers.
-- 
-- The purpose of a shape type is to disambiguate this situation. In
-- shape types, the type 'Qubit' (and sometimes 'Bit', in the case of
-- heterogeneous types) takes the place of a leaf. In the three
-- situations of the above example, the shape type would be [('Qubit',
-- 'Qubit')] in the first case; ['Qubit'] in the second case, the
-- 'Qubit' in the third case.
-- 
-- [Difference between shape type parameters and shape term parameters]
-- 
-- A shape type parameter exists only to describe a type; its value is
-- irrelevant and often undefined. A shape type parameter describes
-- the location of leaves in a type. On the other hand, the purpose of
-- a shape term parameter is used to fix the number and locations of
-- leaves in a data structure (for example, to fix the length of a
-- list). Shape term parameters are also often just called \"shape
-- parameters\" in Quipper.
--
-- The distinction is perhaps best illustrated in an example.
-- A typical shape type parameter is
-- 
-- > undefined :: (Qubit, [Qubit], [[Bit]])
-- 
-- A typical shape term parameter is
-- 
-- > (qubit, [qubit, qubit, qubit], [[bit, bit], []]) :: (Qubit, [Qubit], [[Bit]])
-- 
-- Both of them have the same type. The shape type parameter specifies
-- that the data structure is a triple consisting of a qubit, a list
-- of qubits, and a list of lists of bits.  The shape term parameter
-- moreover specifies that the first list consists of exactly three
-- qubits, and the second lists consists of a list of two bits and a
-- list of zero bits.
-- 
-- Note that the value of the shape type parameter is undefined (we
-- often use the term 'dummy' instead of 'undefined', to get more
-- meaningful error messages). On the other hand, the value of the
-- shape term parameter is partially defined; only the /leaves/ are
-- of undefined value.
-- 
-- [Functions for specifying shape type parameters]
-- 
-- Since it is not possible, in Haskell, to pass a type as an argument
-- to a function, we provide some terms whose only purpose is to
-- represent types. All of them have value 'undefined'.  Effectively,
-- a shape type parameter is a type \"written as a term\".
-- 
-- The following terms can also be combined in data structures to
-- represent composite types. For example:
-- 
-- > (qubit, [bit]) :: (Qubit, [Bit])

-- | A dummy term of any type. This term is 'undefined' and must never
-- be evaluated. Its only purpose is to hold a type.
dummy :: a
dummy = error "attempted evaluation of dummy term"

-- | A dummy term of type 'Qubit'. It can be used in shape parameters
-- (e.g., 'qc_init'), as well as shape type parameters (e.g.,
-- 'qcdata_mapM').
qubit :: Qubit
qubit = dummy

-- | A dummy term of type 'Bit'. It can be used in shape parameters
-- (e.g., 'qc_init'), as well as shape type parameters (e.g.,
-- 'qcdata_mapM').
bit :: Bit
bit = dummy

-- | A dummy term of type 'Bool'.
bool :: Bool
bool = dummy

-- | Convert a piece of homogeneous quantum data to a shape type
-- parameter. This is guaranteed to never evaluate /x/, and returns an
-- undefined value.
shapetype_q :: (QData qa) => QType qa -> qa
shapetype_q x = dummy

-- | Convert a piece of homogeneous classical data to a shape type
-- parameter. This is guaranteed to never evaluate /x/, and returns an
-- undefined value.
shapetype_c :: (QData qa) => CType qa -> qa
shapetype_c x = dummy

-- | Convert a piece of homogeneous boolean data to a shape type
-- parameter. This is guaranteed to never evaluate /x/, and returns an
-- undefined value. Do not confuse this with the function 'qshape',
-- which creates a shape value.
shapetype_b :: (QData qa) => BType qa -> qa
shapetype_b x = dummy

-- | A dummy term of the same type as the given term. If /x/ :: /a/,
-- then 'dummy' /x/ :: /a/. This is guaranteed not to evaluate /x/,
-- and returns an undefined value.
shape :: a -> a
shape x = dummy

-- ======================================================================
-- * Homogeneous types

-- ----------------------------------------------------------------------
-- ** The QData class

-- $ The 'QData' type class contains homogeneous data types built up
-- from leaves of type 'Qubit'. It contains no methods; all of its
-- functionality is derived from 'QCData'. It does, however, contain
-- a number of equations that help the type checker figure out how to
-- convert heterogeneous type to homogeneous ones and vice versa.

-- | The 'QData' type class contains homogeneous data types built up
-- from leaves of type 'Qubit'.
class (qa ~ QType (CType qa),
       qa ~ QTypeB (BType qa), 
       qa ~ QCType Qubit Bool qa,
       qa ~ QType qa,
       QCData qa,
       QCData (CType qa)
      ) => QData qa
  
instance (qa ~ QType (CType qa),
       qa ~ QTypeB (BType qa), 
       qa ~ QCType Qubit Bool qa,
       qa ~ QType qa,       
       QCData qa,
       QCData (CType qa)
      ) => QData qa

-- ----------------------------------------------------------------------
-- ** Derived combinators on QData

-- $ This section provides several convenient combinators for the
-- 'QData' class. All of them are definable from those of
-- 'QCData'.

-- | Map a function /f/ over all the leaves of a data structure.  The
-- first argument is a dummy shape parameter: its value is ignored, but
-- its /type/ is used to determine the shape of the data to map over.
-- 
-- Example (ignoring the monad for the sake of simplicity):
-- 
-- > qdata_mapM (leaf, [leaf]) f (x,[y,z,w]) = (f x, [f y, f z, f w]).
-- 
-- For data types that have a sense of direction, the mapping should
-- preferably be performed from left to right, but this property is
-- not guaranteed and may change without notice.
qdata_mapM :: (QData qa, Monad m) => qa -> (x -> m y) -> HType x qa -> m (HType y qa)
qdata_mapM qa f xa = qcdata_mapM qa f f xa where

-- | Zip two data structures with leaf types /x/ and /y/ together, to
-- obtain a new data structure of the same shape with leaf type (/x/,
-- /y/).  The first three arguments are dummy shape type parameters, representing
-- the shape type and the two leaf types, respectively.
-- 
-- The 'ErrMsg' argument is a stub error message to be used in case
-- of failure.
qdata_zip :: (QData qa) => qa -> x -> y -> HType x qa -> HType y qa -> ErrMsg -> HType (x, y) qa
qdata_zip qa x y xs ys errmsg = qcdata_zip qa x x y y xs ys errmsg

-- | Sometimes, it is possible to have a boolean parameter with some
-- aspect of its shape indeterminate. The function 'qdata_promote'
-- takes such a boolean parameter, as well as a piece of quantum data,
-- and sets the shape of the former to that of the latter.
-- 
-- Indeterminate shapes can be used with certain operations, such as
-- controlling and terminating, where some aspect of the shape of the
-- parameter can be determined from the context in which it is
-- used. This is useful, e.g., for quantum integers, where one may
-- want to specify a control condition by an integer literal such as
-- 17, without having to specify the number of bits. Thus, we can
-- write, e.g.,
-- 
-- > gate `controlled` qi .==. 17
-- 
-- instead of the more cumbersome
-- 
-- > gate `controlled` qi .==. (intm (qdint_length qi) 17).
-- 
-- Another useful application of this arises in the use of infinite
-- lists of booleans (such as @['False'..]@), to specify a control
-- condition for a finite list of qubits.
-- 
-- Because this function is used as a building block, we also pass
-- an error message to be used in case of failure. This will
-- hopefully make it clearer to the user which operation caused the
-- error.

qdata_promote :: (QData qa) => BType qa -> qa -> ErrMsg -> BType qa
qdata_promote ba qa errmsg = qcdata_promote ba qa errmsg

-- | The inverse of 'qdata_zip': Take a data structure with leaf type
-- (/x/, /y/), and return two data structures of the same shape with
-- leaf types /x/ and /y/, respectively. The first three arguments are
-- dummy shape type parameters, analogous to those of 'qdata_zip'.
qdata_unzip :: (QData s) => s -> x -> y -> HType (x, y) s -> (HType x s, HType y s)
qdata_unzip s (sx :: x) (c :: y) z = (x, y) where
  x = qdata_map s (fst :: (x, y) -> x) z
  y = qdata_map s (snd :: (x, y) -> y) z

-- | Map a function over every leaf in a data structure. Non-monadic
-- version of 'qdata_mapM'.
qdata_map :: (QData s) => s -> (x -> y) -> HType x s -> HType y s
qdata_map shape f xs =
  getId $ qdata_mapM shape (return . f) xs
  
-- | Visit every leaf in a data structure, updating an accumulator.
qdata_fold :: (QData s) => s -> (x -> w -> w) -> HType x s -> w -> w
qdata_fold shape f xs w =
  getId $ qdata_foldM shape (\x w -> return $ f x w) xs w

-- | Map a function over every leaf in a data structure, while also
-- updating an accumulator. This combines the functionality of
-- 'qdata_fold' and 'qdata_map'.
qdata_fold_map :: (QData s) => s -> (x -> w -> (y, w)) -> HType x s -> w -> (HType y s, w)
qdata_fold_map shape f xs w =
  getId $ qdata_fold_mapM shape (\x w -> return $ f x w) xs w

-- | Monadic version of 'qdata_fold': Visit every leaf in a data
-- structure, updating an accumulator.
qdata_foldM :: (QData s, Monad m) => s -> (x -> w -> m w) -> HType x s -> w -> m w
qdata_foldM shape f xs w = do
  (ys, w) <- qdata_fold_mapM shape f' xs w
  return w
    where
      f' x w = do
        w <- f x w
        return ((), w)

-- | Monadic version of 'qdata_fold_map': Map a function over every
-- leaf in a data structure, while also updating an accumulator. This
-- combines the functionality of 'qdata_foldM' and 'qdata_mapM'.
qdata_fold_mapM :: (QData s, Monad m) => s -> (x -> w -> m (y, w)) -> HType x s -> w -> m (HType y s, w)
qdata_fold_mapM shape f xs w = do
  (ys, w) <- runStateT computation w
  return (ys, w)
  where
    -- m' = StateT w m
    computation = qdata_mapM shape map_leaf xs
    map_leaf x = do
              w <- get
              (y, w') <- lift $ f x w
              put w'
              return y

-- | Return a list of leaves of the given homogeneous data structure.
-- The first argument is a dummy shape type parameter, and is only used
-- for its type.
-- 
-- The leaves are ordered in some deterministic, but arbitrary way. It
-- is guaranteed that when two data structures of the same shape type
-- and shape (same length of lists etc) are sequentialized, the leaves
-- will be ordered the same way. No other property of the order is
-- guaranteed, In particular, it might change without notice. 
qdata_sequentialize :: (QData s) => s -> HType x s -> [x]
qdata_sequentialize shape xs = xlist where
  blist = qdata_fold shape do_leaf xs blist_empty
  xlist = list_of_blist blist
  
  do_leaf :: x -> BList x -> BList x
  do_leaf x blist = blist +++ blist_of_list [x]

-- | Take a specimen homogeneous data structure to specify the \"shape\"
-- desired (length of lists, etc); then reads the given list of leaves
-- in as a piece of homogeneous data of the same shape. The ordering
-- of the leaves is assumed to be the same as that which
-- 'qdata_sequentialize' produces for the given shape.
-- 
-- A \"length mismatch\" error occurs if the list does not have
-- exactly the required length.
--           
-- Please note that, by contrast with the function
-- 'qdata_sequentialize', the first argument is a shape term
-- parameter, not a shape type parameter. It is used to decide where
-- the qubits should go in the data structure.
qdata_unsequentialize :: (QData s) => s -> [x] -> HType x s
qdata_unsequentialize shape xlist = xs where
  xs = case qdata_fold_map shape do_leaf shape xlist of
    (xs, []) -> xs
    (xs, _) -> error "qdata_unsequentialize: length mismatch"
    
  -- first argument of do_leaf is dummy
  do_leaf :: Qubit -> [x] -> (x, [x])
  do_leaf x (h:t) = (h, t)
  do_leaf x [] = error "qdata_unsequentialize: length mismatch"

-- | Combine a shape type argument /q/, a leaf type argument /a/, and
-- a shape size argument /x/ into a single shape argument /qx/. Note:
-- 
-- * /q/ captures only the type, but not the size of the data. Only
-- the type of /q/ is used; its value can be undefined. This is
-- sufficient to determine the depth of leaves in a data structure,
-- but not their number.
-- 
-- * /x/ captures only the size of the data, but not its type. In
-- particular, /x/ may have leaves of non-atomic types. /x/ must
-- consist of well-defined constructors up to the depth of leaves of
-- /q/, but the values at the actual leaves of /x/ may be undefined. 
-- 
-- * The output /qx/ combines the type of /q/ with the size of /x/,
-- and can therefore be used both as a shape type and a shape value.
-- Note that the actual leaves of /qx/ will be 'qubit' and 'bit',
-- which are synonyms for 'undefined'. 
-- 
-- Example:
-- 
-- > q = undefined :: ([Qubit], [[Qubit]])
-- > x = ([undefined, 0], [[undefined], [0, 1]])
-- > qdata_makeshape qc a x = ([qubit, qubit], [[qubit], [qubit, qubit]])
-- 
-- where /a/ :: @Int@.
qdata_makeshape :: (QData qa) => qa -> a -> HType a qa -> qa
qdata_makeshape q (a::a) x = qdata_map q map_qubit x where
  map_qubit = const qubit :: a -> Qubit

-- | Like 'qdata_mapM', except the leaves are visited in exactly the
-- opposite order. This is used primarily for cosmetic reasons: For
-- example, when initializing a bunch of ancillas, and then
-- terminating them, the circuit will look more symmetric if they are
-- terminated in the opposite order.
qdata_mapM_op :: (QData s, Monad m) => s -> (x -> m y) -> HType x s -> m (HType y s)
qdata_mapM_op shapetype (f :: x -> m y) xs = do
  let shapeterm = qdata_makeshape shapetype (dummy :: x) xs
  let xlist = qdata_sequentialize shapeterm xs
  ylist <- sequence_right [ f x | x <- xlist ]
  let ys = qdata_unsequentialize shapeterm ylist
  return ys

-- | Like 'qdata_promote', except take a piece of classical data.
qdata_promote_c :: (QData s) => BType s -> CType s -> ErrMsg -> BType s
qdata_promote_c b c s = qdata_promote b q s where
  q = qdata_map (shapetype_c c) map_qubit c
      
  map_qubit :: Bit -> Qubit
  map_qubit = const qubit

-- ----------------------------------------------------------------------
-- ** The CData and BData classes
  
-- | The 'CData' type class contains homogeneous data types built up
-- from leaves of type 'Bit'.
class (QData (QType ca), CType (QType ca) ~ ca) => CData ca
instance (QData (QType ca), CType (QType ca) ~ ca) => CData ca

-- | The 'BData' type class contains homogeneous data types built up
-- from leaves of type 'Bool'.
class (QData (QTypeB ba), BType (QTypeB ba) ~ ba) => BData ba
instance (QData (QTypeB ba), BType (QTypeB ba) ~ ba) => BData ba

-- ----------------------------------------------------------------------
-- ** The QShape class
              
-- $ By definition, 'QShape' /ba/ /qa/ /ca/ means that /ba/, /qa/, and
-- /ca/ are, respectively, boolean, quantum, and classical homogeneous
-- data types of the same common shape. The 'QShape' class directly
-- defined in terms of the 'QData' class. In fact, the two classes are
-- interchangeable in the following sense:
-- 
-- > QShape ba qa ca   implies   QData qa, 
-- 
-- and conversely,
-- 
-- > QData qa        implies   QShape (BType qa) qa (CType qa).
-- 
-- Moreover, the functional dependencies @/ba/ -> /qa/, /qa/ -> /ca/,
-- /ca/ -> /ba/@ ensure that each of the three types determines the
-- other two. Therefore, in many ways, 'QShape' is just a convenient
-- notation for functionality already present in 'QData'.
  
-- | The 'QShape' class allows the definition of generic functions that
-- can operate on quantum data of any \"shape\", for example, nested
-- tuples or lists of qubits.
-- 
-- In general, there are three kinds of data: quantum inputs (such as
-- 'Qubit'), classical inputs (such as 'Bit'), and classical
-- parameters (such as 'Bool'). For example, a 'Qubit' can be
-- initialized from a 'Bool'; a 'Qubit' can be measured, resulting in
-- a 'Bit', etc. For this reason, the type class 'QShape' establishes a
-- relation between three types:
-- 	
-- [@qa@] A data structure having 'Qubit' at the leaves.
-- 
-- [@ca@] A data structure of the same shape as @qa@, having 'Bit' at
-- the leaves.
-- 
-- [@ba@] A data structure of the same shape as @qa@, having 'Bool' at
-- the leaves.
-- 
-- Some functions input a classical parameter for the sole purpose of
-- establishing the \"shape\" of a piece of data. The shape refers to
-- qualities of a data structure, such as the length of a list, which
-- are not uniquely determined by the type. For example, two different
-- lists of length 5 have the same shape. When performing a generic
-- operation, such as reversing a circuit, it is often necessary to
-- specify the shape of the inputs, but not the actual inputs.
-- 
-- In the common case where one only needs to declare one of the types
-- /qa/, /ca/, or /ba/, one of the simpler type classes 'QData',
-- 'CData', or 'BData' can be used.

class (QData qa, 
       CType qa ~ ca,
       BType qa ~ ba
      ) => QShape ba qa ca | ba -> qa, qa -> ca, ca -> ba

instance (QData qa, BType qa ~ ba, CType qa ~ ca) => QShape ba qa ca

-- ======================================================================
-- * Heterogeneous types
           
-- $ A heterogeneous type describes a data structure built up from
-- leaves of type 'Qubit' and 'Bit'. Such types are used, for example,
-- to represent sets of endpoints in circuits, parameters to
-- subroutines and circuit building functions. A typical example is:
-- 
-- > (Bit, Qubit, [Qubit]).

-- ----------------------------------------------------------------------
-- ** Derived combinators on QCData

-- $ The 'QCData' type class only contains the three primitive
-- combinators 'qcdata_mapM', 'qcdata_zip', and 'qcdata_promote'.
-- Many other useful combinators are definable in terms of these, and
-- we provide several of them here.

-- | The inverse of 'qcdata_zip': Take a data structure whose leaves
-- are pairs, and return two data structures of the same shape,
-- collecting all the left components and all the right components,
-- respectively. The first five arguments are shape type parameters,
-- analogous to those of 'qcdata_zip'.
qcdata_unzip :: (QCData qc) => qc -> q -> c -> q' -> c' -> QCType (q, q') (c, c') qc -> (QCType q c qc, QCType q' c' qc)
qcdata_unzip s (q :: q) (c :: c) (q' :: q') (c' :: c') z = (x, y) where
  x = qcdata_map s (fst :: (q, q') -> q) (fst :: (c, c') -> c) z
  y = qcdata_map s (snd :: (q, q') -> q') (snd :: (c, c') -> c') z

-- | Map two functions /f/ and /g/ over the leaves of a heterogeneous
-- data structure. Apply /f/ to all the leaves at 'Qubit' positions,
-- and 'g' to all the leaves at 'Bit' positions. Non-monadic version
-- of 'qcdata_mapM'.
qcdata_map :: (QCData qc) => qc -> (q -> q') -> (c -> c') -> QCType q c qc -> QCType q' c' qc
qcdata_map shape f g xs =
  getId $ qcdata_mapM shape (return . f) (return . g) xs

-- | Visit every leaf in a data structure, updating an
-- accumulator. This function requires two accumulator functions /f/
-- and /g/, to be used at 'Qubit' positions and 'Bit' positions,
-- respectively.
qcdata_fold :: (QCData qc) => qc -> (q -> w -> w) -> (c -> w -> w) -> QCType q c qc -> w -> w
qcdata_fold shape f g xs w =
  getId $ qcdata_foldM shape (\x w -> return $ f x w) (\y w -> return $ g y w) xs w

-- | Map a function over every leaf in a data structure, while also
-- updating an accumulator. This combines the functionality of
-- 'qcdata_fold' and 'qcdata_map'.
qcdata_fold_map :: (QCData qc) => qc -> (q -> w -> (q', w)) -> (c -> w -> (c', w)) -> QCType q c qc -> w -> (QCType q' c' qc, w)
qcdata_fold_map shape f g xs w =
  getId $ qcdata_fold_mapM shape (\x w -> return $ f x w) (\x w -> return $ g x w) xs w
  
-- | Monadic version of 'qcdata_fold': Visit every leaf in a data
-- structure, updating an accumulator. This function requires two
-- accumulator functions /f/ and /g/, to be used at 'Qubit' positions
-- and 'Bit' positions, respectively.
qcdata_foldM :: (QCData qc, Monad m) => qc -> (q -> w -> m w) -> (c -> w -> m w) -> QCType q c qc -> w -> m w
qcdata_foldM shape f g xs w = do
  (ys, w) <- qcdata_fold_mapM shape (map_leaf f) (map_leaf g) xs w
  return w
  where
    map_leaf :: (Monad m) => (x -> w -> m w) -> (x -> w -> m ((), w))
    map_leaf f x w = do
              w <- f x w
              return ((), w)

-- | Monadic version of 'qcdata_fold_map': Map a function over every
-- leaf in a data structure, while also updating an accumulator. This
-- combines the functionality of 'qcdata_foldM' and 'qcdata_mapM'.
qcdata_fold_mapM :: (QCData qc, Monad m) => qc -> (q -> w -> m (q', w)) -> (c -> w -> m (c', w)) -> QCType q c qc -> w -> m (QCType q' c' qc, w)
qcdata_fold_mapM shape f g xs w = do
  (ys, w) <- runStateT computation w
  return (ys, w)
  where
    -- m' = StateT w m
    computation = qcdata_mapM shape (map_leaf f) (map_leaf g) xs

    map_leaf :: (Monad m) => (a -> s -> m (b, s)) -> a -> StateT s m b
    map_leaf f a = StateT (f a)

-- | Return a list of leaves of the given heterogeneous data
-- structure. The first argument is a dummy shape type parameter, and
-- is only used for its type. Leaves in qubit positions and bit
-- positions are returned, respectively, as the left or right
-- components of a disjoint union.
-- 
-- The leaves are ordered in some deterministic, but arbitrary way. It
-- is guaranteed that when two data structures of the same shape type
-- and shape (same length of lists etc) are sequentialized, the leaves
-- will be ordered the same way. No other property of the order is
-- guaranteed, In particular, it might change without notice.
qcdata_sequentialize :: (QCData qc) => qc -> QCType q c qc -> [B_Endpoint q c]
qcdata_sequentialize shape xs = xlist where
  blist = qcdata_fold shape do_qubit do_bit xs blist_empty
  xlist = list_of_blist blist
  
  do_qubit :: q -> BList (B_Endpoint q c) -> BList (B_Endpoint q c)
  do_qubit q blist = blist +++ blist_of_list [Endpoint_Qubit q]

  do_bit :: c -> BList (B_Endpoint q c) -> BList (B_Endpoint q c)
  do_bit c blist = blist +++ blist_of_list [Endpoint_Bit c]

-- | Take a specimen heterogeneous data structure to specify the
-- \"shape\" desired (length of lists, etc); then reads the given list
-- of leaves in as a piece of heterogeneous data of the same
-- shape. The ordering of the leaves, and the division of the leaves
-- into qubit and bit positions, is assumed to be the same as that
-- which 'qcdata_sequentialize' produces for the given shape.
-- 
-- A \"length mismatch\" error occurs if the list does not have
-- exactly the required length. A \"shape mismatch\" error occurs if
-- the list contains an 'Endpoint_Bit' entry corresponding to a
-- 'Qubit' position in the shape, or an 'Endpoint_Qubit' entry
-- corresponding to a 'Bit' position.
--           
-- Please note that, by contrast with the function
-- 'qcdata_sequentialize', the first argument is a shape term
-- parameter, not a shape type parameter. It is used to decide where
-- the qubits and bits should go in the data structure.
qcdata_unsequentialize :: (QCData qc) => qc -> [B_Endpoint q c] -> QCType q c qc
qcdata_unsequentialize shape xlist = xs where
  xs = case qcdata_fold_map shape do_qubit do_bit shape xlist of
    (xs, []) -> xs
    (xs, _) -> error "qcdata_unsequentialize: length mismatch"
    
  -- first argument of do_qubit and do_bit is dummy
  do_qubit :: Qubit -> [B_Endpoint q c] -> (q, [B_Endpoint q c])
  do_qubit x (Endpoint_Qubit h : t) = (h, t)
  do_qubit x (Endpoint_Bit h : t) = error "qcdata_unsequentialize: shape mismatch"
  do_qubit x [] = error "qcdata_unsequentialize: length mismatch"

  do_bit :: Bit -> [B_Endpoint q c] -> (c, [B_Endpoint q c])
  do_bit x (Endpoint_Bit h : t) = (h, t)
  do_bit x (Endpoint_Qubit h : t) = error "qcdata_unsequentialize: shape mismatch"
  do_bit x [] = error "qcdata_unsequentialize: length mismatch"

-- | Combine a shape type argument /q/, two leaf type arguments /a/
-- and /b/, and a shape size argument /x/ into a single shape argument
-- /qx/. Note:
-- 
-- * /q/ captures only the type, but not the size of the data. Only
-- the type of /q/ is used; its value can be undefined. This is
-- sufficient to determine the depth of leaves in a data structure,
-- but not their number.
-- 
-- * /x/ captures only the size of the data, but not its type. In
-- particular, /x/ may have leaves of non-atomic types. /x/ must
-- consist of well-defined constructors up to the depth of leaves of
-- /q/, but the values at the actual leaves of /x/ may be undefined. 
-- 
-- * The output /qx/ combines the type of /q/ with the size of /x/,
-- and can therefore be used both as a shape type and a shape value.
-- Note that the actual leaves of /qx/ will be 'qubit' and 'bit',
-- which are synonyms for 'undefined'. 
-- 
-- Example:
-- 
-- > qc = undefined :: ([Qubit], [[Bit]])
-- > x = ([undefined, (0,False)], [[undefined], [Just 2, Nothing]])
-- > qcdata_makeshape qc a b x = ([qubit, qubit], [[bit], [bit, bit]])
-- 
-- where /a/ :: @(Int,Bool)@, /b/ :: @(Maybe Int)@.
qcdata_makeshape :: (QCData qc) => qc -> a -> b -> QCType a b qc -> qc
qcdata_makeshape q (a::a) (b::b) x = qcdata_map q map_qubit map_bit x where
  map_qubit = const qubit :: a -> Qubit
  map_bit = const bit :: b -> Bit

-- | Like 'qcdata_mapM', except the leaves are visited in exactly the
-- opposite order. This is used primarily for cosmetic reasons: For
-- example, when initializing a bunch of ancillas, and then
-- terminating them, the circuit will look more symmetric if they are
-- terminated in the opposite order.
qcdata_mapM_op :: (QCData qc, Monad m) => qc -> (q -> m q') -> (c -> m c') -> QCType q c qc -> m (QCType q' c' qc)
qcdata_mapM_op shapetype (f :: q -> m q') (g :: c -> m c') xs = do
  let shapeterm = qcdata_makeshape shapetype (dummy::q) (dummy::c) xs 
  let xlist = qcdata_sequentialize shapeterm xs
  ylist <- sequence_right [ map_endpointM f g x | x <- xlist ]
  let ys = qcdata_unsequentialize shapeterm ylist
  return ys
  where
    map_endpointM f g (Endpoint_Qubit x) = do
      x' <- f x
      return (Endpoint_Qubit x')
    map_endpointM f g (Endpoint_Bit y) = do
      y' <- g y
      return (Endpoint_Bit y')

-- ----------------------------------------------------------------------  
-- ** The QCDataPlus class

-- Implementation note: Since Haskell does not allow cyclic
-- dependencies in the definition of type classes, it was a
-- non-trivial problem to define 'QShape' and 'QCDataPlus' so that the
-- implications go both ways. We solved this problem by basing both
-- classes on QCData, together with a generous application of
-- equational reasoning.

-- | The 'QCDataPlus' type class is almost identical to 'QCData',
-- except that it contains one additional piece of information that
-- allows the type checker to prove the implications
-- 
-- > QCDataPlus qc     implies   QShape (BType qc) (QType qc) (CType qc)
-- > QCDataPlus qc     implies   QData (QType qc)
-- > QCDataPlus qc     implies   CData (CType qc)
-- > QCDataPlus qc     implies   BData (BType qc)
-- 
-- This is sometimes useful, for example, in the context of a function
-- that inputs a 'QCData', measures all the qubits, and returns a
-- 'CData'. However, the additional information for the type checker
-- comes at a price, which is drastically increased compilation time.
-- Therefore 'QCDataPlus' should only be used when 'QCData' is
-- insufficient.

class (QCData qc, QData (QType qc)) => QCDataPlus qc
instance (QCData qc, QData (QType qc)) => QCDataPlus qc

-- ----------------------------------------------------------------------
-- ** Fixed size QCDataPlus

-- | 'QCDataPlus_Simple' is a convenience type class that combines
-- 'QCDataPlus' and 'SimpleType'.
class (QCData qc, SimpleType qc) => QCData_Simple qc
instance (QCData qc, SimpleType qc) => QCData_Simple qc

-- | 'QCDataPlus_Simple' is a convenience type class that combines
-- 'QCDataPlus' and 'SimpleType'.
class (QCDataPlus qc, SimpleType qc) => QCDataPlus_Simple qc
instance (QCDataPlus qc, SimpleType qc) => QCDataPlus_Simple qc

-- Implementation note: We could just have made 'SimpleType' a
-- subclass of 'QCData' directly, but this would require the
-- type-checker to do lots of additional theorem proving, to the point
-- of overflowing the context stack and significantly slowing down
-- compilation.

-- ----------------------------------------------------------------------
-- ** The QCLeaf class

-- | The class 'QCLeaf' consists of the two types 'Qubit' and 'Bit'.
-- It is primarily used for convenience, in those cases (such as the
-- arithmetic library) where some class instance should be defined for
-- the cases 'Qubit' and 'Bit', but not for general 'QCData'. It is
-- also used, e.g., in the definition of the './=.' operator.
class (QCData q, 
       SimpleType q, 
       ControlSource q, 
       ControlSource (Signed q), 
       Labelable q String, 
       QCType Qubit Bit q ~ q,
       QCType Bool Bool q ~ Bool) => QCLeaf q

instance QCLeaf Qubit
instance QCLeaf Bit

-- ----------------------------------------------------------------------
-- ** Canonical string representation

-- $ For the purpose of storing boxed subroutines, it is useful to
-- have a unique representation of 'QCData' shapes as strings.  The
-- currently implementation relies on 'show' to give unique
-- representations. Therefore, when defining 'Show' instances for
-- 'QCData', one should make sure that the generated strings contain
-- enough information to recover both the type and the shape uniquely.

-- | A type to represent a 'Qubit' leaf, for the sole purpose that
-- 'show' will show it as \"Q\".
data Qubit_Leaf = Qubit_Leaf
instance Show Qubit_Leaf where
  show _ = "Q"

-- | A type to represent a 'Bit' leaf, for the sole purpose that
-- 'show' will show it as \"C\".
data Bit_Leaf = Bit_Leaf
instance Show Bit_Leaf where
  show _ = "C"

-- | Turn any 'QCData' into a string uniquely identifying its type and
-- shape. The current implementation assumes that appropriately unique
-- 'Show' instances are defined for all 'QCData'.
canonical_shape :: (QCData qc) => qc -> String  
canonical_shape qc = show $ qcdata_map qc do_qubit do_bit qc
  where
    do_qubit :: Qubit -> Qubit_Leaf
    do_qubit q = Qubit_Leaf
    
    do_bit :: Bit -> Bit_Leaf
    do_bit c = Bit_Leaf
           
-- | The type operator 'LType' converts 'Qubit' to 'Qubit_Leaf' and
-- 'Bit' to 'Bit_Leaf'.
type LType a = QCType Qubit_Leaf Bit_Leaf a

-- ======================================================================
-- * Defining new QCData instances

-- $ To define a new kind of quantum data, the following must be
-- defined:
-- 
-- * A class instance of 'QCData',
-- 
-- * a type instance of 'QCType', and
-- 
-- * a type instance of 'QTypeB'.
-- 
-- If the new type is simple, an class instance of 'SimpleType' should
-- also be defined.
-- 
-- If the new type may be integrated with Template Haskell, a class
-- instance of 'CircLiftingUnpack' should also be defined.
-- 
-- To ensure that circuit labeling will work for the new type, a class
-- instance of 'Labelable' must also be defined for every member of
-- 'QCData'. See "Quipper.Labels" for detailed instructions on how to
-- do so.
-- 
-- Modules that define new kinds of quantum data should import
-- "Quipper.Internal".
