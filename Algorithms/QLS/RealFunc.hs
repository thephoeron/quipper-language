-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


-- | Define various analytic functions for 'FDouble' and 'QDouble'.
module Algorithms.QLS.RealFunc where

import Data.List(mapAccumL)
import Quipper
import Algorithms.QLS.CircLiftingImport
import Algorithms.QLS.QSignedInt
import Algorithms.QLS.QDouble
import Algorithms.QLS.Utils


-- * Some analytic functions on 'FDouble'.

-- | Approximation of the sine function using Taylor series.
build_circuit
approx_sin :: FDouble -> FDouble
approx_sin x = let x2 = x * x in
               let x3 = x2 * x in
               let x4 = x2 * x2 in
               let x5 = x4 * x in
               let x7 = x2 * x5 in
               let x9 = x2 * x7 in
               let x11 = x2 * x9 in
               x - (x3 / 6.0) 
                 + (x5 / 120.0) 
                 - (x7 / 5040.0) 
                 + (x9 / 362880.0) 
                 - (x11 / 39916800.0) 


-- | Implementation of the sine function valid on the whole domain of
-- 'FDouble'.
build_circuit
local_sin :: FDouble -> FDouble
local_sin x = let n = fromIntegral $ floor (x/(2.0*local_pi)) in
              let y = x - 2.0*local_pi*n in 
              if (y < local_pi/2.0) then approx_sin y
              else if (y > 3.0*local_pi/2.0) then approx_sin (y - 2.0*local_pi)
              else approx_sin (local_pi - y)


-- | Implementation of the cosine function valid on the whole domain
-- of 'FDouble'.
build_circuit
local_cos :: FDouble -> FDouble
local_cos x = local_sin (x + local_pi/2.0)




-- listAngle :: [Double]
listAngle = snd $ mapAccumL (\a x -> (a+1, x / (2 ** a))) 3.0 (replicate after_radix_length pi)

-- template_listAngle :: Circ [QDouble]
template_listAngle = mapM (\x -> qinit $ fdouble x) listAngle

-- listCos :: [Double]
listCos = map cos listAngle

-- template_listCos :: Circ [QDouble]
template_listCos = mapM (\x -> qinit $ fdouble x) listCos

-- listSin :: [Double]
listSin = map sin listAngle

-- template_listSin :: Circ [QDouble]
template_listSin = mapM (\x -> qinit $ fdouble x) listCos



-- list_values :: [(FDouble,FDouble,FDouble)]
list_values = map (\(x,y,z) -> (fdouble x, fdouble y, fdouble z)) $ 
                                    zip3 listAngle listCos listSin

template_list_values = mapM (\(x,y,z) -> do
                              x' <- qinit $ fdouble x
                              y' <- qinit $ fdouble y
                              z' <- qinit $ fdouble z
                              return (x',y',z')) $ zip3 listAngle listCos listSin


-- | Auxiliary function for 'local_sqrt'.
build_circuit
approx_sqrt :: Int -> FDouble -> FDouble 
approx_sqrt n x = case n of
                    0 -> x
                    n -> let s = approx_sqrt (paramPred n) x in (s + x/s)/2.0

-- | Approximation of the square root using iterative means.
build_circuit
local_sqrt :: FDouble -> FDouble
local_sqrt x = approx_sqrt paramTen x


-- | The function 'magnitude' defined for 'FDouble'.
build_circuit
local_mag :: FDouble -> FDouble -> FDouble
local_mag x y = local_sqrt (x * x + y * y)


-- | Apply the matrix
-- 
-- >  ( a b )
-- >  ( c d )
-- 
-- to the column vector (/x/,/y/).
build_circuit
rotate :: FDouble -> FDouble -> FDouble -> FDouble -> FDouble -> FDouble -> (FDouble,FDouble)
rotate a b c d x y = (a * x + b * y, c * x + d * y)


-- | Auxiliary function for 'approx_atan2'.
build_circuit
approx_atan2_aux :: FDouble -> FDouble -> (FDouble,FDouble, FDouble) -> (FDouble, FDouble, FDouble)
                -> (FDouble,FDouble,FDouble)
approx_atan2_aux x y (angle, x', y') (r, cn, sn) =
    let (a,(b,c)) = if (y' > y) then (angle - r, rotate cn sn (-sn) cn x' y')
                    else (angle + r, rotate cn (-sn) sn cn x' y')
    in (a,b,c)

-- | Definition of 'atan2' using a CORDIC method.  Assume (/x/,/y/) is
-- in first quadrant and that /x/ > /y/.
build_circuit
approx_atan2 :: FDouble -> FDouble -> FDouble
approx_atan2 y x = 
   let list = list_values in
   let (a,_,_) = foldl (approx_atan2_aux x y) (0.0, local_mag x y, 0.0) list in a

-- | Definition of 'atan2' using a CORDIC method. /x/ and /y/ can be any 'FDouble'.
build_circuit
local_atan2 :: FDouble -> FDouble -> FDouble
local_atan2 y' x' = 
   let (x,y,(pad,sign)) = if      (x' >= 0.0 && y' >= 0.0) then ( x',  y', (0.0, 1.0))
                          else if (x' >= 0.0 && y' <  0.0) then ( x', -y', (0.0, -1.0))
                          else if (x' <  0.0 && y' <  0.0) then (-x', -y', (-local_pi, 1.0))
                          else                                  (-x',  y', (local_pi,  -1.0))
   in
   let angle = if (x > y) then approx_atan2 y x
               else            local_pi/2.0 - approx_atan2 x y
   in sign * angle + pad


-- | The function 'mkPolar' defined for 'FDouble'.
build_circuit
local_mkPolar :: FDouble -> FDouble -> (FDouble,FDouble)
local_mkPolar p t = (p * local_cos t, p * local_sin t)






instance Floating FDouble where
  pi    = fromRational $ toRational pi
  sin x = local_sin x
  cos x = local_cos x

  sinh x = (exp x - exp (-x)) / 2
  cosh x = (exp x - exp (-x)) / 2

  asinh x = error "asinh not defined for FDouble"
  acosh x = error "acosh not defined for FDouble"
  atanh x = error "atanh not defined for FDouble"

  exp x = undefined
  log x = undefined

  asin x = error "asin not defined for FDouble"
  acos x = error "acos not defined for FDouble"
  atan x = atan2 x 1


instance RealFloat FDouble where
   floatRadix _ = 2
   floatDigits x = xdouble_length x
   floatRange _ = (0,0)
   decodeFloat (XDouble k n) = (integer_of_fsint n, -k)
   encodeFloat x k = XDouble (-k) (fromInteger x)
   isNaN _ = False
   isInfinite _ = False
   isDenormalized _ = False
   isNegativeZero _ = False
   isIEEE _ = False
   atan2 y x = local_atan2 y x




-- | A type class for quantum floating-point numbers.
class QFloating a where
  -- | Quantum implementation of the sine function.
  q_sin :: a -> Circ a
  -- | Quantum implementation of the cosine function.
  q_cos :: a -> Circ a

instance QFloating QDouble where
  q_sin x = (unpack template_local_sin) x
  q_cos x = (unpack template_local_cos) x


-- | Quantum implementation of 'atan2' on 'QDouble'.
q_atan2 :: QDouble -> QDouble -> Circ QDouble
q_atan2 = unpack template_local_atan2

-- | Quantum implementation of 'magnitude' on 'QDouble'.
q_magnitude :: (QDouble, QDouble) -> Circ QDouble
q_magnitude = Prelude.uncurry $ unpack template_local_mag


-- | Quantum implementation of 'mkPolar' on 'QDouble'.
q_mkPolar :: QDouble -> QDouble -> Circ (QDouble,QDouble)
q_mkPolar = unpack template_local_mkPolar


-- | Quantum implementation of 'Re' on 'QDouble': a quantum complex is
-- a pair of two 'QDouble's.
q_Re :: (QDouble,QDouble) -> Circ QDouble
q_Re (x,y) = return x

-- | Quantum implementation of 'Im' on 'QDouble': a quantum complex is
-- a pair of two 'QDouble's.
q_Im :: (QDouble,QDouble) -> Circ QDouble
q_Im (x,y) = return y



my_test_fdouble = do
          for 0 37 1 $ \i -> do
            let x = fromIntegral i
            let a1 = fromRational $ toRational (sin(x * pi/37))
            let a2 = fromRational $ toRational (cos(x * pi/37))
            let z1 = local_atan2 a1 a2
            let z2 = fromRational $ toRational $ atan2  (sin(x * pi/37)) (cos(x * pi/37))
            putStrLn $ show_fdouble $ abs (z1 - z2)




-- * Template subroutines of analytic functions.

-- | Template version of 'sin'.
template_sin :: Circ (QDouble -> Circ QDouble)
template_sin = return $ \x -> box "sin" q_sin x

-- | Template version of 'cos'.
template_cos :: Circ (QDouble -> Circ QDouble)
template_cos = return $ \x -> box "cos" q_cos x

-- | Template version of 'atan2'.
template_atan2 :: Circ (QDouble -> Circ (QDouble -> Circ QDouble))
template_atan2 = return $ \x -> return $ \y -> box "atan" (uncurry q_atan2) (x,y)






-- * Template subroutines for dealing with quantum complex number encoded as pairs of 'QDouble'.

-- | Template version of 'mkPolar'.
template_mkPolar :: Circ (QDouble -> Circ (QDouble -> Circ (QDouble,QDouble)))
template_mkPolar = return $ \x -> return $ \y -> box "mkPolar" (uncurry q_mkPolar) (x,y)

-- | Template version of the constructor ':+' of 'Complex'.
template_symb_colon_symb_plus_ :: Circ (QDouble -> Circ (QDouble -> Circ (QDouble,QDouble)))
template_symb_colon_symb_plus_ = return $ \x -> return $ \y -> return (x,y) 


-- | Template version of 'magnitude'.
template_magnitude :: Circ ((QDouble,QDouble) -> Circ QDouble)
template_magnitude = return $ \p -> box "mag" q_magnitude p

-- | Template version of 'realPart'.
template_realPart :: Circ ((QDouble,QDouble) -> Circ QDouble)
template_realPart = return $ \(x,y) -> return x

-- | Template version of 'imagPart'.
template_imagPart :: Circ ((QDouble,QDouble) -> Circ QDouble)
template_imagPart = return $ \(x,y) -> return y

