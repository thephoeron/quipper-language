-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TemplateHaskell #-}

module Main where

import Libraries.Template
import Data.Map as Map
import Language.Haskell.TH as TH
import Test2Import

data MyBool = MyTrue | MyFalse

template_not :: IO (MyBool -> IO MyBool)
template_not = return $ \x -> do
   putStrLn "doing not";
   return (case x of MyTrue -> MyFalse
                     MyFalse -> MyTrue)

template_symb_ampersand_symb_ampersand_ :: IO (MyBool -> IO (MyBool -> IO MyBool))
template_symb_ampersand_symb_ampersand_ = return $ \x -> return $ \y -> do
   putStrLn "doing and";
   return (case (x,y) of (MyTrue,MyTrue) -> MyTrue
                         _               -> MyFalse)

$( decToMonad  "IO" 
    [d| myOr (x,y) = not ((not x) && (not y)) |] )

main = do
   f <- template_myOr
   f (MyTrue,MyFalse)

