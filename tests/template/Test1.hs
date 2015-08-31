-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TemplateHaskell #-}

module Main where

import Libraries.Template

import Data.Map as Map
import Language.Haskell.TH as TH
import Test1Import

template_tick :: IO (a -> IO a)
template_tick = return $ \x -> do
            putStrLn "tick"
            return x

template_symb_star_ :: IO (Integer -> IO (Integer -> IO Integer))
template_symb_star_ = return $ \x -> return $ \y -> return (x*y)

template_symb_minus_ :: IO (Integer -> IO (Integer -> IO Integer))
template_symb_minus_ = return $ \x -> return $ \y -> return (x-y)

tick :: a -> a
tick x = x

$( decToMonad "IO" 
      [d| fact x = tick (case x of
                           0 -> 1
                           n -> n * (fact (n-1))) |] )


main = do
     f <- template_fact
     f 3
