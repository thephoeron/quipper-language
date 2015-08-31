-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | This module is for use with "Libraries.Template.Lifting". 
-- It contains various lifted functions of general use. They are not
-- intended to be used directly (although this would not break
-- anything).

module Libraries.Template.Auxiliary where

import Libraries.Auxiliary (fold_right_zip,fold_right_zipM)
import Data.List
import Control.Monad

-- ----------------------------------------------------------------------
-- * List operations

-- | Lifted version of @'(:)' :: a -> [a] -> [a]@.
template_symb_colon_ :: Monad m => m (a -> m ([a] -> m [a]))
template_symb_colon_ = return $ \h -> return $ \t -> return (h:t)

-- | Lifted version of @'[]' :: [a]@.
template_symb_obracket_symb_cbracket_ :: Monad m => m [a]
template_symb_obracket_symb_cbracket_ = return []

-- | Lifted version of @'init' :: [a] -> [a]@.
template_init ::  Monad m => m ([a] -> m [a])
template_init = return $ \l -> return (init l)

-- | Lifted version of @'last' :: [a] -> [a]@.
template_last :: Monad m => m ([a] -> m a)
template_last = return $ \l -> return (last l)

-- | Lifted version of @'(++)' :: [a] -> [a] -> [a]@.
template_symb_plus_symb_plus_ :: Monad m => m ([a] -> m ([a] -> m [a]))
template_symb_plus_symb_plus_ = return $ \l1 -> return $ \l2-> return (l1 ++ l2)

-- | Lifted version of 'zip3'.
template_zip3 :: Monad m => m ([a] -> m ([b] -> m ([c] -> m [(a,b,c)])))
template_zip3 = return $ \x -> return $ \y -> return $ \z -> return (zip3 x y z)

-- | lifted version of @'foldl'@
template_foldl :: Monad m => m ((a -> m (b -> m a)) -> m (a -> m ([b] -> m a)))
template_foldl = return $ \f -> return $ \a -> return $ \lb -> foldM (auxf f) a lb
        where auxf f a b = do
                g <- f a
                g b

-- | lifted version of @'reverse'@
template_reverse :: Monad m => m ([a] -> m [a])
template_reverse = return $ \x -> return (reverse x)


-- | lifted version of @'zipWith'@
template_zipWith :: Monad m => m ((a -> m (b -> m c)) -> m ([a] -> m ([b] -> m [c])))
template_zipWith = return $ \f -> return $ \a -> return $ \b -> zipWithM (auxf f) a b
        where auxf f a b = do
                g <- f a
                g b

-- | Lifted version of @'fold_right_zip'@
template_fold_right_zip :: 
  Monad m => m (((a,b,c) -> m (a,d)) -> m ((a,[b],[c]) -> m (a,[d])))
template_fold_right_zip = return $ \f -> return $ \x -> (fold_right_zipM f x)

-- ----------------------------------------------------------------------
-- * Other operations

-- | Lifted version of the combinator '$'.
template_symb_dollar_ :: Monad m => m ((a -> m b) -> m (a -> m b))
template_symb_dollar_ = return $ \f -> return $ \x -> f x

-- | Lifted version of @'error' :: String -> a@. Using it will make the
-- circuit generation fail with the error described in 'String'.
template_error :: Monad m => m (String -> m a)
template_error = return $ error

-- | Lifted version of @'snd' :: (a,b) -> b@
template_snd :: Monad m => m ((a,b) -> m b)
template_snd = return $ \(a,b) -> return b


