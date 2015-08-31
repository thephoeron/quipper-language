-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module provides isomorphisms between /n/-tuples and repeated
-- pairs. It is used to be able to write type classes for /n/-tuples
-- more generically. Essentially we want to be able to write code for
-- 17-tuples once and for all, rather than once for each type class we
-- define. Ideally there would be a standard Haskell library for this.
--
-- Two type classes are provided: 'Tuple', and 'TupleOrUnary'.
-- 'Tuple' is recommended for most uses.

module Libraries.Tuple where

-- I only want to write code involving explicit 7-tuples once in my life

-- | This type class relates types of the form @t = (a,b,c,d)@ (“tupled form”) to
-- types of the form @s = (a,(b,(c,(d,()))))@ (“standard form”), and provides a way to
-- convert between the two representations.
--
-- The tupled form can always be deduced from the standard form.

class TupleOrUnary t s | s -> t where
  -- | For example, maps @(a,(b,(c,(d,()))))@ to @(a,b,c,d)@.
  weak_tuple :: s -> t
  -- | For example, maps @(a,b,c,d)@ to @(a,(b,(c,(d,()))))@.
  weak_untuple :: t -> s

instance TupleOrUnary () () where
  weak_tuple () = ()
  weak_untuple () = ()

instance TupleOrUnary a (a,()) where
  weak_tuple (a,()) = a
  weak_untuple a = (a,())

instance TupleOrUnary (a,b) (a,(b,())) where
  weak_tuple (a,(b,())) = (a,b)
  weak_untuple (a,b) = (a,(b,()))
  
instance TupleOrUnary (a,b,c) (a,(b,(c,()))) where
  weak_tuple (a,(b,(c,()))) = (a,b,c)
  weak_untuple (a,b,c) = (a,(b,(c,())))
  
instance TupleOrUnary (a,b,c,d) (a,(b,(c,(d,())))) where
    weak_tuple (a,(b,(c,(d,())))) = (a,b,c,d)
    weak_untuple (a,b,c,d) = (a,(b,(c,(d,()))))

instance TupleOrUnary (a,b,c,d,e) (a,(b,(c,(d,(e,()))))) where
    weak_tuple (a,(b,(c,(d,(e,()))))) = (a,b,c,d,e)
    weak_untuple (a,b,c,d,e) = (a,(b,(c,(d,(e,())))))

instance TupleOrUnary (a,b,c,d,e,f) (a,(b,(c,(d,(e,(f,())))))) where
    weak_tuple (a,(b,(c,(d,(e,(f,())))))) = (a,b,c,d,e,f)
    weak_untuple (a,b,c,d,e,f) = (a,(b,(c,(d,(e,(f,()))))))

instance TupleOrUnary (a,b,c,d,e,f,g) (a,(b,(c,(d,(e,(f,(g,()))))))) where
    weak_tuple (a,(b,(c,(d,(e,(f,(g,()))))))) = (a,b,c,d,e,f,g)
    weak_untuple (a,b,c,d,e,f,g) = (a,(b,(c,(d,(e,(f,(g,())))))))

instance TupleOrUnary (a,b,c,d,e,f,g,h) (a,(b,(c,(d,(e,(f,(g,(h,())))))))) where
    weak_tuple (a,(b,(c,(d,(e,(f,(g,(h,())))))))) = (a,b,c,d,e,f,g,h)
    weak_untuple (a,b,c,d,e,f,g,h) = (a,(b,(c,(d,(e,(f,(g,(h,()))))))))

instance TupleOrUnary (a,b,c,d,e,f,g,h,i) (a,(b,(c,(d,(e,(f,(g,(h,(i,()))))))))) where
    weak_tuple (a,(b,(c,(d,(e,(f,(g,(h,(i,()))))))))) = (a,b,c,d,e,f,g,h,i)
    weak_untuple (a,b,c,d,e,f,g,h,i) = (a,(b,(c,(d,(e,(f,(g,(h,(i,())))))))))

instance TupleOrUnary (a,b,c,d,e,f,g,h,i,j) (a,(b,(c,(d,(e,(f,(g,(h,(i,(j,())))))))))) where
    weak_tuple (a,(b,(c,(d,(e,(f,(g,(h,(i,(j,())))))))))) = (a,b,c,d,e,f,g,h,i,j)
    weak_untuple (a,b,c,d,e,f,g,h,i,j) = (a,(b,(c,(d,(e,(f,(g,(h,(i,(j,()))))))))))

-- | In almost all instances, the standard form can also be deduced from the tupled form;  
-- the only exception is the unary case.  The 'Tuple' class includes no new methods, 
-- adding just this functional dependency.
--
-- While the methods of 'Tuple' are always copied from those of 'TupleOrUnary', 
-- they are renamed, so that use of these methods tells the type checker it
-- can use the extra functional dependency.
class (TupleOrUnary t s) => Tuple t s | s -> t, t -> s where
  tuple :: s -> t
  tuple = weak_tuple

  untuple :: t -> s
  untuple = weak_untuple
  
instance Tuple () ()
instance Tuple (a,b) (a,(b,()))
instance Tuple (a,b,c) (a,(b,(c,())))
instance Tuple (a,b,c,d) (a,(b,(c,(d,()))))
instance Tuple (a,b,c,d,e) (a,(b,(c,(d,(e,())))))
instance Tuple (a,b,c,d,e,f) (a,(b,(c,(d,(e,(f,()))))))
instance Tuple (a,b,c,d,e,f,g) (a,(b,(c,(d,(e,(f,(g,())))))))
instance Tuple (a,b,c,d,e,f,g,h) (a,(b,(c,(d,(e,(f,(g,(h,()))))))))
instance Tuple (a,b,c,d,e,f,g,h,i) (a,(b,(c,(d,(e,(f,(g,(h,(i,())))))))))
instance Tuple (a,b,c,d,e,f,g,h,i,j) (a,(b,(c,(d,(e,(f,(g,(h,(i,(j,()))))))))))
