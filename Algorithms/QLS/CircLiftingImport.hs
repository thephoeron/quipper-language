-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | This module contains definitions to work with Template Haskell. All
-- the definitions in this module are used by Template Haskell in
-- "Algorithms.QLS.TemplateOracle" and "Algorithms.QLS.RealFunc".
module Algorithms.QLS.CircLiftingImport where

import Data.Typeable

import Quipper
import Quipper.Internal

import QuipperLib.Arith
import QuipperLib.Decompose

import Algorithms.QLS.QDouble
import Algorithms.QLS.QSignedInt
import Algorithms.QLS.Utils

-- * Utility function

-- | @'grepn' /regexp/ /list/@: Counts how many times /regexp/ is a
-- sublist of 'list'.
grepn :: (Eq a) => [a] -> [a] -> Int
grepn regexp l = 
      if (length regexp > length l) then 0
      else if ((take (length regexp) l) == regexp) then 1 + (grepn regexp $ tail l)
      else grepn regexp $ tail l




-- * Lifting of ordering operators.


-- | Template version of '/='.
template_symb_slash_symb_equal_ :: (Typeable qa, QOrd qa, Show (BType qa)) => Circ (qa -> Circ (qa -> Circ Qubit))
template_symb_slash_symb_equal_ = return $ \x -> return $ \y -> do
            (_,_,r) <- box "/=" (decompose_generic Toffoli $ uncurry q_is_not_equal) (x,y)
            return r

-- | Template version of '<'.
template_symb_oangle_ :: (Typeable qa, QOrd qa, Show (BType qa)) => Circ (qa -> Circ (qa -> Circ Qubit))
template_symb_oangle_ = return $ \x -> return $ \y -> box "<" (uncurry q_less) (x,y)

-- | Template version of '<='.
template_symb_oangle_symb_equal_ :: (Typeable qa, QOrd qa, Show (BType qa)) => Circ (qa -> Circ (qa -> Circ Qubit))
template_symb_oangle_symb_equal_ = return $ \x -> return $ \y -> box "<=" (uncurry q_leq) (x,y)

-- | Template version of '>'.
template_symb_cangle_ :: (Typeable qa, QOrd qa, Show (BType qa)) => Circ (qa -> Circ (qa -> Circ Qubit))
template_symb_cangle_ = return $ \x -> return $ \y -> box ">" (uncurry q_greater) (x,y)

-- | Template version of '>='.
template_symb_cangle_symb_equal_ :: (Typeable qa, QOrd qa, Show (BType qa)) => Circ (qa -> Circ (qa -> Circ Qubit))
template_symb_cangle_symb_equal_ = return $ \x -> return $ \y -> box ">=" (uncurry q_geq) (x,y)




-- * Lifting of arithmetic operators

-- | Template version of '-'.
template_symb_minus_ :: (Typeable qa, QNum qa, Show (BType qa)) => Circ (qa -> Circ (qa -> Circ qa))
template_symb_minus_ = return $ \qx -> return $ \qy -> do (qx,qy,qz) <- box "-" (uncurry q_sub) (qx,qy); return qz

-- | Template version of '+'.
template_symb_plus_ :: (Typeable qa, QNum qa, Show (BType qa)) => Circ (qa -> Circ (qa -> Circ qa))
template_symb_plus_ = return $ \qx -> return $ \qy -> do (qx,qy,qz) <- box "+" (uncurry q_add) (qx,qy); return qz

-- | Template version of '*'.
template_symb_star_ :: (Typeable qa, QNum qa, Show (BType qa)) => Circ (qa -> Circ (qa -> Circ qa))
template_symb_star_ = return $ \qx -> return $ \qy -> do (qx,qy,qz) <- box "*" (uncurry q_mult) (qx,qy); return qz

-- | Template version of 'negate'.
template_negate :: (Typeable qa, QNum qa, Show (BType qa)) => Circ (qa -> Circ qa)
template_negate = return $ \qx -> do (_,qz) <- box "neg" q_negate qx; return qz

-- | Template version of 'abs'.
template_abs :: (Typeable qa, QNum qa, Show (BType qa)) => Circ (qa -> Circ qa)
template_abs = return $ \x -> do
                  (_,r) <- box "abs" q_abs x
                  return r

-- | Template version of 'mod'
template_mod :: Circ (QSignedInt -> Circ (QSignedInt -> Circ QSignedInt))
template_mod = return $ \x -> return $ \y -> box "mod" (decompose_generic Toffoli $ uncurry q_mod) (x,y)


-- * Operations on 'QDouble'

-- | Template version of '/' on 'Fractional'.
template_symb_slash_:: Circ (QDouble -> Circ (QDouble -> Circ QDouble))
template_symb_slash_ = return $ \x -> return $ \y -> box "/" (decompose_generic Toffoli $ uncurry q_div_real) (x,y)

-- | The constant 'pi' as an 'FDouble'.
local_pi :: FDouble
local_pi =  fdouble pi

-- | Template version of 'local_pi'.
template_local_pi :: Circ QDouble
template_local_pi = qinit (fdouble pi)



-- * Relation between 'QDouble' and 'QSignedInt'.

-- | Template version of 'floor'.
template_floor :: Circ (QDouble -> Circ QSignedInt)
template_floor = return $ \(XDouble k (SInt x b)) -> 
      return $ SInt (reverse . drop k . reverse $ x) b

-- | Template version of 'ceil'.
template_ceiling :: Circ (QDouble -> Circ QSignedInt)
template_ceiling = return $ \x -> q_ceiling x

-- | Template version of 'fromIntegral'.
template_fromIntegral :: Circ (QSignedInt -> Circ QDouble)
template_fromIntegral = return $ \x -> q_fromIntegral x



-- * Dealing with parameters.


-- | Lift a real number to 'QDouble'.
template_rational :: Double -> Circ QDouble
template_rational x = qinit $ fdouble x

-- | Lift an integer to 'QSignedInt'.
template_integer :: Int -> Circ QSignedInt
template_integer x = qinit $ fromIntegral x


-- | Make a parameter 'Int' as a regular 'Int' that can be lifted.
getIntFromParam :: Int -> Int
getIntFromParam x = fromIntegral x

-- | Template version of 'getIntFromParam'.
template_getIntFromParam :: Circ (Int -> Circ QSignedInt)
template_getIntFromParam = return $ \x -> qinit $ fromIntegral x

-- | Parameter integer of value '0'.
paramZero :: Int
paramZero = 0

-- | Template version of 'paramZero'.
template_paramZero :: Circ Int
template_paramZero = return 0

-- | Parameter integer of value '10'.
paramTen :: Int
paramTen = 10

-- | Template version of 'paramTen'.
template_paramTen :: Circ Int
template_paramTen = return paramTen

-- | Successor function acting on parameter 'Int'.
paramSucc :: Int -> Int
paramSucc x = x+1

-- | Template version of 'paramSucc'.
template_paramSucc :: Circ (Int -> Circ Int)
template_paramSucc = return $ \x -> return (x+1)

-- | Predecessor function acting on parameter 'Int'.
paramPred :: Int -> Int
paramPred x = x - 1

-- | Template version of 'paramPred'.
template_paramPred :: Circ (Int -> Circ Int)
template_paramPred = return $ \x -> return (x-1)



-- | Subtraction of parameter integers.
paramMinus :: Int -> Int -> Int
paramMinus x y = x - y

-- | Template version of 'paramMinus'.
template_paramMinus :: Circ (Int -> Circ (Int -> Circ Int))
template_paramMinus = return $ \x -> return $ \y -> return (x-y)



-- * Miscellaneous operations.

-- | Lifted version of @'length'@.
template_length :: Circ ([a] -> Circ QSignedInt)
template_length = return $ \l -> qinit $ fromIntegral $ length l

-- | Return the first half of the input list.
take_half :: [a] -> [a]
take_half l = take (1 + (length l) `div` 2) l

-- | Lifted version of @'take_half'@.
template_take_half :: Circ ([a] -> Circ [a])
template_take_half = return $ \l -> return $ take_half l

