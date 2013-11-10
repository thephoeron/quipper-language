-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The standard Haskell module "Data.Typeable" only provides
-- instances for tuples up to length 7. Since we need larger tuples,
-- we provide the missing instances here. 
-- 
-- Unfortunately, there is no easy way to do this portably; once the
-- instances get added to "Data.Typeable", we must remove them here.
-- 
-- Please note: type instances do not generate documentation, so there
-- is nothing here to document. Please click on \"Source\" above to
-- see the source code.

module Libraries.Typeable where

import Data.Typeable

-- Note: we use scoped type variables so that the typerep is constant;
-- it can be computed at compile time. Same trick as in
-- Data.Typeable.Internal.
instance (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable f, Typeable g, Typeable h) => Typeable (a,b,c,d,e,f,g,h) where
  typeOf _ = typerep
    where
      typerep = mkTyCon3 "GHC" "Tuple" "(,,,,,,,)" `mkTyConApp` [ typeOf (undefined :: a), typeOf (undefined :: b), typeOf (undefined :: c), typeOf (undefined :: d), typeOf (undefined :: e), typeOf (undefined :: f), typeOf (undefined :: g), typeOf (undefined :: h) ]

instance (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable f, Typeable g, Typeable h, Typeable i) => Typeable (a,b,c,d,e,f,g,h,i) where
  typeOf _ = typerep
    where
      typerep = mkTyCon3 "GHC" "Tuple" "(,,,,,,,,)" `mkTyConApp` [ typeOf (undefined :: a), typeOf (undefined :: b), typeOf (undefined :: c), typeOf (undefined :: d), typeOf (undefined :: e), typeOf (undefined :: f), typeOf (undefined :: g), typeOf (undefined :: h), typeOf (undefined :: i) ]

instance (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable f, Typeable g, Typeable h, Typeable i, Typeable j) => Typeable (a,b,c,d,e,f,g,h,i,j) where
  typeOf _ = typerep
    where
      typerep = mkTyCon3 "GHC" "Tuple" "(,,,,,,,,,)" `mkTyConApp` [ typeOf (undefined :: a), typeOf (undefined :: b), typeOf (undefined :: c), typeOf (undefined :: d), typeOf (undefined :: e), typeOf (undefined :: f), typeOf (undefined :: g), typeOf (undefined :: h), typeOf (undefined :: i), typeOf (undefined :: j) ]
