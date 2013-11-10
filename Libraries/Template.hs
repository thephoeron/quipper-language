-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides the public interface to the template lifting
-- library. It provides functions that input a Haskell declaration or
-- expression (in the form of a Haskell abstract syntax tree), and
-- lift this to another declaration or expression, with all functions
-- lifted into a specified monad.
-- 
-- This can be combined with Template Haskell to convert source code
-- to Haskell abstract syntax trees and vice versa.

module Libraries.Template (
  -- * Example
  -- $EXAMPLE
  
  -- * General lifting functions
  decToMonad,
  expToMonad,
  
  -- * Liftings of specific constants
  module Libraries.Template.Auxiliary
  ) where

import Libraries.Template.Lifting
import Libraries.Template.Auxiliary

-- $EXAMPLE 
-- 
-- We give an example to illustrate what is meant by \"lifting\" a
-- term to a monad. Consider the expression
-- 
-- > f = \g x -> g x x,
-- 
-- which has type
-- 
-- > f :: (a -> a -> b) -> (a -> b).
-- 
-- We can lift this to the 'IO' monad by 
-- 
-- * converting the expression to an abstract syntax tree, using the
-- special Template Haskell notation [nobr @[| ... |]@];
-- 
-- * applying the 'expToMonad' function;
-- 
-- * converting the resulting abstract syntax tree back to a term,
-- using the special Template Haskell notation [nobr @$( ... )@].
-- 
-- This allows us to write the following:
-- 
-- > f' = $( expToMonad "IO" [| \g x -> g x x |] ),
-- 
-- which has type
-- 
-- > f' :: IO ((a -> IO (a -> IO b)) -> IO (a -> IO b)),
-- 
-- and is in fact equivalent to
-- 
-- > f'' = return $ \g ->
-- >         return $ \x -> do
-- >           h <- g x
-- >           y <- h x
-- >           return y

