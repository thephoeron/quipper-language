-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}

-- | This module provides functionality for labelling endpoints in
-- wires. The goal is to achieve two things:
-- 
-- * Label qubits individually. For example, we would like to label
-- three qubits (/a/, /b/, /c/) as \"a\", \"b\", and \"c\",
-- respectively.
-- 
-- * Label data structures all at once. For example, if
-- /a/=[/x/,/y/,/z/] is a piece of quantum data, and we label this
-- data structure \"a\", then the individual qubits will be labelled:
-- /x/ = /a/[0], /y/ = /a/[1], /z/ = /a/[2]. 
-- 
-- We can also combine both methods to arbitrary nesting levels. For
-- example, we can label (([x,y,z], t), [u,v,w]) as (\"a\", [\"u\",
-- \"v\", \"w\"]), to get the labelling /x/ = /a/[0,0], /y/ =
-- /a/[0,1], /z/ = /a/[0,2], /t/ = /a/[1], /u/ = /u/, /v/ = /v/, /w/ =
-- /w/.

module Quipper.Labels where

import Quipper.Circuit
import Quipper.Monad
import Libraries.Auxiliary
import Libraries.Tuple
import Quipper.Transformer

import qualified Data.Map as Map
import Data.Map (Map)

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)

-- ----------------------------------------------------------------------
-- * Helper functions

-- ** Indices

-- | An index list is something that can be appended to a string. We
-- consider subscript indices of the form \"[i]\", dotted indices of
-- the form \".i\", and perhaps arbitrary suffixes.  A complication is
-- that we want consecutive subscript indices to be combined, as in
-- \"[i,j,k]\". We therefore need a special data structure to hold an
-- index list \"under construction\".
-- 
-- An index list consists of a string and a list of current
-- subscripts. For efficiency, the list of subscripts is reversed,
-- i.e., the most recent subscript is at the head of the list.
type IndexList = (String, [String])

-- | Convert an index list to a string.
indexlist_format :: IndexList -> String
indexlist_format (s,idx) = 
  s ++ string_of_list "[" "," "]" "" id (reverse idx)

-- | The empty index list.
indexlist_empty :: IndexList
indexlist_empty = ("", [])

-- | Append a subscript to an index list.
indexlist_subscript :: IndexList -> String -> IndexList
indexlist_subscript (s, idx) i = (s, i:idx)

-- | Append a dotted index to an index list.
indexlist_dotted :: IndexList -> String -> IndexList
indexlist_dotted idxl i = (indexlist_format idxl ++ "." ++ i, [])

-- ** The LabelMonad monad

-- | A monad to provide a convenient syntax for specifying 'Labelable'
-- instances. Computations in this monad have access to a read-only
-- \"current index list\", and they output a binding from wires to
-- strings.
newtype LabelMonad a = LabelMonad { 
  getLabelMonad :: IndexList -> (Map Wire String, a)
  }

instance Monad LabelMonad where
  return a = LabelMonad (\idxl -> (Map.empty, a))
  f >>= g = LabelMonad h where
    h idxl = (Map.union m1 m2, z) where
      (m1, y) = getLabelMonad f idxl
      (m2, z) = getLabelMonad (g y) idxl

instance Applicative LabelMonad where
  pure = return
  (<*>) = ap

instance Functor LabelMonad where
  fmap = liftM

-- | Get the current string and index.
labelmonad_get_indexlist :: LabelMonad IndexList
labelmonad_get_indexlist = LabelMonad h where
  h idxl = (Map.empty, idxl)
  
-- | Output a binding for a label
labelmonad_put_binding :: Wire -> String -> LabelMonad ()
labelmonad_put_binding x label = LabelMonad h where
  h idxl = (Map.singleton x label, ())

-- | Run a subcomputation with a new current index list.
labelmonad_with_indexlist :: IndexList -> LabelMonad a -> LabelMonad a
labelmonad_with_indexlist idxl body = LabelMonad h where
  h idxl' = getLabelMonad body idxl

-- | Extract a labelling from a label monad computation. This is the
-- run function of the label monad.
labelmonad_run :: LabelMonad () -> Map Wire String
labelmonad_run body = bindings where
  (bindings, _) = getLabelMonad body indexlist_empty

-- ----------------------------------------------------------------------
-- ** Formatting of labels

-- | Label a wire with the given name, using the current index.
label_wire :: Wire -> String -> LabelMonad ()
label_wire x s = do
  idxl <- labelmonad_get_indexlist
  let label = s ++ indexlist_format idxl
  labelmonad_put_binding x label

-- | Run a subcomputation with a subscript index appended to the
-- current index list. Sample usage:
-- 
-- > with_index "0" $ do
-- >   <<<labelings>>>
with_index :: String -> LabelMonad () -> LabelMonad ()
with_index i body = do
  idxl <- labelmonad_get_indexlist
  labelmonad_with_indexlist (indexlist_subscript idxl i) body

-- | Run a subcomputation with a dotted index appended to the current
-- index list. Sample usage:                                                                  
-- 
-- > with_dotted_index "left" $ do
-- >   <<<labelings>>>

with_dotted_index :: String -> LabelMonad () -> LabelMonad ()
with_dotted_index i body = do
  idxl <- labelmonad_get_indexlist
  labelmonad_with_indexlist (indexlist_dotted idxl i) body

-- | Like 'with_index', except the order of the arguments is
-- reversed. This is intended to be used as an infix operator:
-- 
-- > <<<labeling>>> `indexed` "0"
indexed :: LabelMonad () -> String -> LabelMonad ()
indexed body i = with_index i body

-- | Like 'with_dotted_index', except the order of the arguments is
-- reversed. This is intended to be used as an infix operator:
-- 
-- > <<<labeling>>> `dotted_indexed` "left"
dotted_indexed :: LabelMonad () -> String -> LabelMonad ()
dotted_indexed body i = with_dotted_index i body

-- | Do nothing.
label_empty :: LabelMonad ()
label_empty = return ()

-- ----------------------------------------------------------------------
-- * The Labelable type class

-- | 'Labelable' /a/ /s/ means that /a/ is a data structure that can
-- be labelled with the format /s/. A \"format\" is a string, or a
-- data structure with strings at the leaves.

class Labelable a s where
  -- | Recursively label a data structure with the given format. 
  label_rec :: a -> s -> LabelMonad ()

-- | Given a data structure and a format, return a list of labelled
-- wires.
mklabel :: (Labelable a s) => a -> s -> [(Wire, String)]
mklabel a s = Map.toList bindings where
  bindings = labelmonad_run (label_rec a s)

instance Labelable Qubit String where
  label_rec a s = label_wire (wire_of_qubit a) s
  
instance Labelable Bit String where
  label_rec a s = label_wire (wire_of_bit a) s
  
instance (Labelable a String) => Labelable (Signed a) String where
  label_rec (Signed a b) s = 
    label_rec a s `dotted_indexed` (if b then "+" else "-")

instance (Labelable a String) => Labelable (Signed a) (Signed String) where
  label_rec (Signed a b) (Signed s c) 
    | b == c = label_rec a s
    | otherwise = return () -- fail silently

instance Labelable () String where
  label_rec a s = label_empty
  
instance Labelable () () where
  label_rec a s = label_empty
  
instance (Labelable a String, Labelable b String) => Labelable (a,b) String where
  label_rec (a,b) s = do
    label_rec a s `indexed` "0"
    label_rec b s `indexed` "1"

instance (Labelable a String, Labelable b String, Labelable c String) => Labelable (a,b,c) String where
  label_rec (a,b,c) s = do
    label_rec a s `indexed` "0"
    label_rec b s `indexed` "1"
    label_rec c s `indexed` "2"

instance (Labelable a String, Labelable b String, Labelable c String, Labelable d String) => Labelable (a,b,c,d) String where
  label_rec (a,b,c,d) s = do
    label_rec a s `indexed` "0"
    label_rec b s `indexed` "1"
    label_rec c s `indexed` "2"
    label_rec d s `indexed` "3"

instance (Labelable a String, Labelable b String, Labelable c String, Labelable d String, Labelable e String) => Labelable (a,b,c,d,e) String where
  label_rec (a,b,c,d,e) s = do
    label_rec a s `indexed` "0"
    label_rec b s `indexed` "1"
    label_rec c s `indexed` "2"
    label_rec d s `indexed` "3"
    label_rec e s `indexed` "4"

instance (Labelable a String, Labelable b String, Labelable c String, Labelable d String, Labelable e String, Labelable f String) => Labelable (a,b,c,d,e,f) String where
  label_rec (a,b,c,d,e,f) s = do
    label_rec a s `indexed` "0"
    label_rec b s `indexed` "1"
    label_rec c s `indexed` "2"
    label_rec d s `indexed` "3"
    label_rec e s `indexed` "4"
    label_rec f s `indexed` "5"

instance (Labelable a String, Labelable b String, Labelable c String, Labelable d String, Labelable e String, Labelable f String, Labelable g String) => Labelable (a,b,c,d,e,f,g) String where
  label_rec (a,b,c,d,e,f,g) s = do
    label_rec a s `indexed` "0"
    label_rec b s `indexed` "1"
    label_rec c s `indexed` "2"
    label_rec d s `indexed` "3"
    label_rec e s `indexed` "4"
    label_rec f s `indexed` "5"
    label_rec g s `indexed` "6"

instance (Labelable a String, Labelable b String, Labelable c String, Labelable d String, Labelable e String, Labelable f String, Labelable g String, Labelable h String) => Labelable (a,b,c,d,e,f,g,h) String where
  label_rec (a,b,c,d,e,f,g,h) s = do
    label_rec a s `indexed` "0"
    label_rec b s `indexed` "1"
    label_rec c s `indexed` "2"
    label_rec d s `indexed` "3"
    label_rec e s `indexed` "4"
    label_rec f s `indexed` "5"
    label_rec g s `indexed` "6"
    label_rec h s `indexed` "7"

instance (Labelable a String, Labelable b String, Labelable c String, Labelable d String, Labelable e String, Labelable f String, Labelable g String, Labelable h String, Labelable i String) => Labelable (a,b,c,d,e,f,g,h,i) String where
  label_rec (a,b,c,d,e,f,g,h,i) s = do
    label_rec a s `indexed` "0"
    label_rec b s `indexed` "1"
    label_rec c s `indexed` "2"
    label_rec d s `indexed` "3"
    label_rec e s `indexed` "4"
    label_rec f s `indexed` "5"
    label_rec g s `indexed` "6"
    label_rec h s `indexed` "7"
    label_rec i s `indexed` "8"

instance (Labelable a String, Labelable b String, Labelable c String, Labelable d String, Labelable e String, Labelable f String, Labelable g String, Labelable h String, Labelable i String, Labelable j String) => Labelable (a,b,c,d,e,f,g,h,i,j) String where
  label_rec (a,b,c,d,e,f,g,h,i,j) s = do
    label_rec a s `indexed` "0"
    label_rec b s `indexed` "1"
    label_rec c s `indexed` "2"
    label_rec d s `indexed` "3"
    label_rec e s `indexed` "4"
    label_rec f s `indexed` "5"
    label_rec g s `indexed` "6"
    label_rec h s `indexed` "7"
    label_rec i s `indexed` "8"
    label_rec j s `indexed` "9"

instance (Labelable a sa, Labelable b sb) => Labelable (a,b) (sa,sb) where  
  label_rec (a,b) (sa,sb) = do
    label_rec a sa
    label_rec b sb
  
instance (Labelable a sa, Labelable b sb, Labelable c sc) => Labelable (a,b,c) (sa, sb, sc) where
  label_rec a s = label_rec (untuple a) (untuple s)

instance (Labelable a sa, Labelable b sb, Labelable c sc, Labelable d sd) => Labelable (a,b,c,d) (sa, sb, sc, sd) where
  label_rec a s = label_rec (untuple a) (untuple s)

instance (Labelable a sa, Labelable b sb, Labelable c sc, Labelable d sd, Labelable e se) => Labelable (a,b,c,d,e) (sa, sb, sc, sd, se) where
  label_rec a s = label_rec (untuple a) (untuple s)

instance (Labelable a sa, Labelable b sb, Labelable c sc, Labelable d sd, Labelable e se, Labelable f sf) => Labelable (a,b,c,d,e,f) (sa, sb, sc, sd, se, sf) where
  label_rec a s = label_rec (untuple a) (untuple s)

instance (Labelable a sa, Labelable b sb, Labelable c sc, Labelable d sd, Labelable e se, Labelable f sf, Labelable g sg) => Labelable (a,b,c,d,e,f,g) (sa, sb, sc, sd, se, sf, sg) where
  label_rec a s = label_rec (untuple a) (untuple s)

instance (Labelable a sa, Labelable b sb, Labelable c sc, Labelable d sd, Labelable e se, Labelable f sf, Labelable g sg, Labelable h sh) => Labelable (a,b,c,d,e,f,g,h) (sa, sb, sc, sd, se, sf, sg, sh) where
  label_rec a s = label_rec (untuple a) (untuple s)

instance (Labelable a sa, Labelable b sb, Labelable c sc, Labelable d sd, Labelable e se, Labelable f sf, Labelable g sg, Labelable h sh, Labelable i si) => Labelable (a,b,c,d,e,f,g,h,i) (sa, sb, sc, sd, se, sf, sg, sh, si) where
  label_rec a s = label_rec (untuple a) (untuple s)

instance (Labelable a sa, Labelable b sb, Labelable c sc, Labelable d sd, Labelable e se, Labelable f sf, Labelable g sg, Labelable h sh, Labelable i si, Labelable j sj) => Labelable (a,b,c,d,e,f,g,h,i,j) (sa, sb, sc, sd, se, sf, sg, sh, si, sj) where
  label_rec a s = label_rec (untuple a) (untuple s)

instance (Labelable a String) => Labelable [a] String where
  label_rec as s = do
    sequence_ [ label_rec a s `indexed` show i | (a,i) <- zip as [0..] ]

instance (Labelable a s) => Labelable [a] [s] where
  label_rec as ss = do
    sequence_ [ label_rec a s | (a,s) <- zip as ss ]

instance (Labelable a String, Labelable b String) => Labelable (B_Endpoint a b) String where
  label_rec (Endpoint_Qubit a) s = label_rec a s
  label_rec (Endpoint_Bit b) s = label_rec b s

instance (Labelable a s, Labelable b t) => Labelable (B_Endpoint a b) (B_Endpoint s t) where
  label_rec (Endpoint_Qubit a) (Endpoint_Qubit s) = label_rec a s
  label_rec (Endpoint_Bit b) (Endpoint_Bit t) = label_rec b t
  label_rec _ _ = return ()  -- fail silently

-- ----------------------------------------------------------------------
-- Parameters are labellable  
  
-- Since parameters (such as Integers) are QCData, they must also be
-- labellable. However, they have no qubits, so the labels are trivial
-- (there are 0 labels on such a type).
  
instance Labelable Integer String where
  label_rec a s = label_empty

instance Labelable Int String where
  label_rec a s = label_empty

instance Labelable Double String where
  label_rec a s = label_empty

instance Labelable Float String where
  label_rec a s = label_empty

instance Labelable Char String where
  label_rec a s = label_empty

-- ======================================================================
-- * High-level functions

-- | Insert a comment in the circuit. This is not a gate, and has no
-- effect, except to mark a spot in the circuit. How the comment is
-- displayed depends on the printing backend.
comment :: String -> Circ ()
comment s = comment_with_label s () ()

-- | Label qubits in the circuit. This is not a gate, and has no
-- effect, except to make the circuit more readable. How the labels
-- are displayed depends on the printing backend. This can take
-- several different forms. Examples:
-- 
-- Label /q/ as @q@ and /r/ as @r@:
-- 
-- > label (q,r) ("q", "r")
-- 
-- Label /a/, /b/, and /c/ as @a@, @b@, and @c@, respectively:
-- 
-- > label [a,b,c] ["a", "b", "c"]
-- 
-- Label /q/ as @x[0]@ and /r/ as @x[1]@:
-- 
-- > label (q,r) "x"
-- 
-- Label /a/, /b/, and /c/ as @x[0]@, @x[1]@, @x[2]@:
-- 
-- > label [a,b,c] "x"
label :: (Labelable qa labels) => qa -> labels -> Circ ()
label qa labels = comment_with_label "" qa labels

-- | Combine 'comment' and 'label' in a single command.
comment_with_label :: (Labelable qa labels) => String -> qa -> labels -> Circ ()
comment_with_label comment qa labels = 
  comment_label comment False (mklabel qa labels)

-- ======================================================================
-- * Defining new Labelable instances

-- $ A 'Labelable' instance should be defined for each new instance of
-- 'QCData'. The general idea is that the structure of the label
-- should exactly follow the structure of the data being labeled,
-- except that at any level the label can be a string (which will then
-- be decorated with appropriate subscripts for each leaf in the
-- data structure).
-- 
-- In practice, there are two cases to consider: adding a new
-- 'QCData' constructor, and adding a new atomic 'QCData'.
-- 
-- [New 'QCshape' constructors]
-- 
-- Consider the case of a new 'QCData' constructor:
-- 
-- > instance (QCData a) => QCData (Constructor a).
-- 
-- There are two required 'Labelable' instances. The first instance
-- deals with a label that is a string, and takes the following form:
-- 
-- > instance (Labelable a String) => Labelable (Constructor a) String where
-- >   label_rec as s = do
-- >     label_rec <<<a1>>> s `indexed` <<<index1>>>
-- >     ...
-- >     label_rec <<<an>>> s `indexed` <<<indexn>>>
-- 
-- Here, /a/[sub 1].../a/[sub /n/] are the components of the data
-- structure, and /index/[sub 1].../index[sub /n/] are the
-- corresponding subscripts. The function 'indexed' appends a
-- subscript of the form \"[i]\".  There is a similar function
-- 'dotted_indexed', which appends a subscript of the form \".i\".
-- 
-- The second required instance deals with a label that is a data
-- structure of the same shape as the data being labeled. It takes the
-- form:
-- 
-- > instance (Labelable a s) => Labelable (Constructor a) (Constructor s) where
-- >   label_rec as ss idx = do
-- >     label_rec <<<a1>>> <<<s1>>>
-- >     ...
-- >     label_rec <<<an>>> <<<sn>>>
-- 
-- Here, /a/[sub 1].../a/[sub /n/] are the components of the data
-- structure, and /s/[sub 1].../s/[sub /n/] are the corresponding
-- components of the label.
-- 
-- [Example]
-- 
-- As a concrete example, consider a constructor
-- 
-- > data MaybeTwo a = One a | Two a a
-- > instance (QCData a) => QCData (MaybeTwo a)
-- 
-- The following instance declarations would be appropriate:
-- 
-- > instance (Labelable a String) => Labelable (MaybeTwo a) String where
-- >    label_rec (One x) s =
-- >      with_dotted_index "one" $ do
-- >        label_rec x s
-- >    label_rec (Two x y) s =
-- >      with_dotted_index "two" $ do
-- >        label_rec x s `indexed` "0"
-- >        label_rec y s `indexed` "1"
-- >
-- > instance (Labelable a s) => Labelable (MaybeTwo a) (MaybeTwo s) where
-- >    label_rec (One x) (One s) = label_rec x s
-- >    label_rec (Two x y) (Two s t) = do
-- >      label_rec x s
-- >      label_rec y t
-- >    label_rec _ _ = return ()  -- fail silently
-- 
-- With this example, the commands
-- 
-- > mklabel (One x) "s"
-- > mklabel (Two y z) "s"
-- 
-- produce the respective labelings
-- 
-- > x -> s.one
-- > y -> s.two[0]
-- > z -> s.two[1]
-- 
-- [New atomic QCShape]
-- 
-- Consider the case of a new atomic 'QCData' instance:
-- 
-- > instance QCData (Atomic x).
-- 
-- We usually need a 'Labelable' instance for the cases /x/='Qubit'
-- and /x/='Bit'. This should be done uniformly, by using the 'QCLeaf'
-- type class. The instance takes the following form:
-- 
-- > instance QCLeaf x => Labelable (Atomic x) String where
-- >   label_rec a s = do
-- >     label_rec <<<a1>>> s `indexed` <<<index1>>>
-- >     ...
-- >     label_rec <<<an>>> s `indexed` <<<indexn>>>
-- 
-- Here, /a/[sub 1].../a/[sub /n/] are the components of the data
-- structure, and /index/[sub 1].../index[sub /n/] are the
-- corresponding subscripts. It is up to the designer of the data
-- structure to decide what are \"components\" and how they should be
-- labelled. On or more layers of string or numeric indices can be
-- added as appropriate.
-- 
-- [Example]
-- 
-- Consider the following sample atomic quantum data. A real number
-- consists of an exponent, a sign, and a list of digits.
-- 
-- > data MyReal x = MyReal Int x [x]
-- > instance QCLeaf x => QCData (MyReal x)
-- 
-- The following instance declaration would be appropriate:
-- 
-- > instance QCLeaf x => Labelable (MyReal x) String where
-- >    label_rec (MyReal exp sign digits) s = do
-- >      label_rec sign s `dotted_indexed` "sign"
-- >      with_dotted_index "digit" $ do
-- >        sequence_ [ label_rec d s `indexed` show i | (d,i) <- zip digits [-exp..] ]
-- 
-- With this example, the command
-- 
-- > mklabel (MyReal 2 x [y0, y1, y2, y3]) "s"
-- 
-- produces the labeling
-- 
-- > x  -> "s.sign"
-- > y0 -> "s.digit[-2]"
-- > y1 -> "s.digit[-1]"
-- > y2 -> "s.digit[0]"
-- > y3 -> "s.digit[1]"
-- 
-- Note that we could have also used the default labeling for the
-- members of a list, but in this case, it was convenient to use a
-- custom labeling.
