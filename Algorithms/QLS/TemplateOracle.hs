-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE NoMonomorphismRestriction #-}


-- | This module contains an implementation of the oracle and its
-- automatic lifting to quantum circuits using Template Haskell.
module Algorithms.QLS.TemplateOracle where

import Data.Complex
import Libraries.Auxiliary

import Control.Monad

import QuipperLib.Arith hiding (template_symb_plus_)
import Algorithms.QLS.Utils
import Algorithms.QLS.QDouble
import Algorithms.QLS.RealFunc
import Algorithms.QLS.QSignedInt
import Algorithms.QLS.CircLiftingImport

import Quipper
import Quipper.CircLifting

-- | Lifted version of @'any'@ (local version).
build_circuit
local_any :: (a -> Bool) -> [a] -> Bool
local_any f l = case l of
            []    -> False
            (h:t) -> if (f h) then True else local_any f t

 

-- | Auxiliary function.
build_circuit
itoxy :: Int -> Int -> Int -> (Int, Int)
itoxy i nx ny = 
   if (i <= 0) then (0,0)
   else if (i > (nx-1)*ny + nx*(ny-1)) then (0,0)
   else ((mod (i - 1) (2*nx - 1)) + 1, ceiling ((fromIntegral i)/(2.0*(fromIntegral nx)-1.0)))


-- | The function sin /x/ \/ /x/.
build_circuit
sinc :: Double -> Double
sinc x = if (x /= 0.0) then (sin x) / x else 1.0


-- | Auxiliary function.
build_circuit
edgetoxy :: Int -> Int -> Int -> (Double, Double)
edgetoxy e nx ny = 
  let (ex,ey) = itoxy e nx ny in
     if (ex < nx) then ((fromIntegral ex) + 0.5, fromIntegral ey)
     else (fromIntegral (ex - nx + 1), (fromIntegral ey) + 0.5)


-- | Auxiliary function. The inputs are:
-- 
-- * /y1/ :: 'Int' - Global edge index of row index of desired matrix element;
-- 
-- * /y2/ :: 'Int' - Global edge index of column index of desired matrix element;
-- 
-- * /nx/ :: 'Int' - Number of vertices left to right;
-- 
-- * /ny/ :: 'Int' - Number of vertices top to bottom;
-- 
-- * /lx/ :: 'Double' - Length of horizontal edges (distance between vertices in /x/ direction);
-- 
-- * /ly/ :: 'Double' - Length of vertical edges (distance between vertices in /y/ direction);
-- 
-- * /k/ :: 'Double' - Plane wave wavenumber.
-- 
-- The output is the matrix element /A/(/y1/, /y2/).
build_circuit
calcmatrixelement :: --
	-- Inputs
	Int 	-- int y1 - Global edge index of row index of desired matrix element  
	-> Int 	-- int y2 - Global edge index of column index of desired matrix element
	-> Int 	-- int nx - Number of vertices left to right
	-> Int	-- int ny - Number of vertices top to bottom
	-> Double -- float lx - Length of horizontal edges (distance between vertices in x direction)
	-> Double -- float ly - Length of vertical edges (distance between vertices in y direction)
	-> Double -- float k - Plane wave wavenumber	
	-- Outputs
	-> Complex Double -- float A - Matrix element A(y1,y2)
calcmatrixelement y1 y2 nx ny lx ly k = 
	let (xg1, yg1) = itoxy y1 nx ny in
        let (xg2, yg2) = itoxy y2 nx ny in
        let b = if ( (y1==y2) && (xg1 >= nx) ) then ly/lx - k*k*lx*ly/3.0
                -- B11 and B22
                else if ( (y1==y2) && (xg1<nx) ) then lx/ly - k*k*lx*ly/3.0
                -- B12 and B21
                else if ( (abs(yg1-yg2) == 1) && (abs(xg1-xg2) == 0) && (xg1<nx) ) then -lx/ly + k*k*lx*ly/12.0
                -- B34 and B43
                else if ( (abs(yg1-yg2)==0) && (abs(xg1-xg2) == 1) && (xg1>=nx) ) then -ly/lx + k*k*lx*ly/12.0
                -- B13
                else if ( (yg1==(yg2+1)) && (xg1==(xg2-nx+1)) && (xg2>=nx) ) then -1.0
                -- B31
                else if ( (yg2==(yg1+1)) && (xg2==(xg1-nx+1)) && (xg1>=nx) ) then -1.0
                -- B14
                else if ( (yg1==(yg2+1)) && (xg1==(xg2-nx)) && (xg1<nx) ) then 1.0
                -- B41
                else if ( (yg2==(yg1+1)) && (xg2==(xg1-nx)) && (xg2<nx) ) then 1.0
                -- B42
                else if ( (yg1==yg2) && (xg1==(xg2+nx)) && (xg1>=nx) ) then -1.0
                -- B24
                else if ( (yg2==yg1) && (xg2==(xg1+nx)) && (xg2>=nx) ) then -1.0
                -- B32
                else if ( (yg1==yg2) && (xg1==(xg2+nx-1)) && (xg2<nx) ) then 1.0
                -- B23
                else if ( (yg2==yg1) && (xg2==(xg1+nx-1)) && (xg1<nx) ) then 1.0
                else -1.0
        in 
        let c = if ( (y1==y2) && ( (xg1==nx) || (xg1==(2*nx-1)) ) ) then 0.0 :+ (k*ly)
                else if  ( (y1==y2) && ( ((yg1==1) && (xg1<nx)) || ((yg1==ny) && (xg1<nx)) ) ) then 0.0 :+ (k*lx)
                else 0.0 :+ 0.0
	in (b :+ 0.0) + c


-- | Auxiliary function.
build_circuit
get_edges l = case l of
                [] -> []
                (x:tt) -> case tt of
                   [] -> []
                   (y:t) -> (x,y):(get_edges (y:t))

-- | Auxiliary function.
build_circuit
checkedge :: Int -> [(Double,Double)] -> Int -> Int -> Bool
checkedge e scatteringnodes nx ny = 
     let (xi,yi) = edgetoxy e nx ny in
     let test_elt ((x1,y1),(x2, y2)) = xi >= x1 && yi >= y1 && xi <= x2 && yi <= y2 in
     let half = take_half scatteringnodes in
     let test_list = local_any test_elt (get_edges half) in (not test_list)




-- | Oracle /r/.
build_circuit
calcRweights :: Int -> Int -> Int -> Double -> Double -> Double -> Double -> Double -> Complex Double
calcRweights y nx ny lx ly k theta phi =
     let (xc',yc') = edgetoxy y nx ny in
     let xc = (xc'-1.0)*lx - ((fromIntegral nx)-1.0)*lx/2.0 in
     let yc = (yc'-1.0)*ly - ((fromIntegral ny)-1.0)*ly/2.0 in
     let (xg,yg) = itoxy y nx ny in
     
     if (xg == nx) then
         
         let i = (mkPolar ly (k*xc*(cos phi)))*
                 (mkPolar 1.0 (k*yc*(sin phi)))*
                 ((sinc (k*ly*(sin phi)/2.0)) :+ 0.0) in
             
         let r = ( cos(phi) :+ k*lx )*((cos (theta - phi))/lx :+ 0.0) in i * r
 
     else if (xg==2*nx-1) then
         
         let i = (mkPolar ly (k*xc*cos(phi)))*
                 (mkPolar 1.0 (k*yc*sin(phi)))*
                 ((sinc (k*ly*sin(phi)/2.0)) :+ 0.0) in
             
         let r = ( cos(phi) :+ (- k*lx))*((cos (theta - phi))/lx :+ 0.0) in i * r
     
         
     else if ( (yg==1) && (xg<nx) ) then 
         
         let i = (mkPolar lx (k*yc*sin(phi)))*
                 (mkPolar 1.0 (k*xc*cos(phi)))*
                 ((sinc (k*lx*(cos phi)/2.0)) :+ 0.0) in
             
         let r = ( (- sin phi) :+ k*ly )*((cos(theta - phi))/ly :+ 0.0) in i * r
     
         
     else if ( (yg==ny) && (xg<nx) ) then 
         
         let i = (mkPolar lx (k*yc*sin(phi)))*
                 (mkPolar 1.0 (k*xc*cos(phi)))*
                 ((sinc (k*lx*(cos phi)/2.0)) :+ 0.0) in
             
         let r = ( (- sin phi) :+ (- k*ly) )*((cos(theta - phi)/ly) :+ 0.0) in i * r
     
     else 0.0 :+ 0.0



-- | Auxiliary function for oracle /A/.
build_circuit
convertband :: Int -> Int -> Int -> Int -> Int
convertband y b nx ny = 
 let nedges = (nx - 1)*ny + nx*(ny - 1) in
 let (ex,ey) = itoxy y nx ny in 
 let x = if ( (ex < nx) && (ey /= 1) ) then
           case b of
                1 -> y-2*nx+1
                2 -> y-nx
                3 -> y-nx+1
                5 -> y
                7 -> y+nx-1
                8 -> y+nx 
                9 -> y+2*nx-1
                _ -> -1
         else if ( (ex < nx) && (ey == 1) ) then 
           case b of
                5 -> y
                7 -> y+nx-1
                8 -> y+nx
                9 -> y+2*nx-1
                _ -> -1
         else if ( (ex >= nx) && (ex /= nx) && (ex /= 2*nx-1) ) then
           case b of
                    2 -> y-nx
                    3 -> y-nx+1
                    4 -> y-1
                    5 -> y
                    6 -> y+1
                    7 -> y+nx-1
                    8 -> y+nx
                    _ -> -1
         else if ( (ex >= nx) && (ex == nx) ) then
                 case b of
                    3 -> y-nx+1
                    5 -> y
                    6 -> y+1
                    8 -> y+nx
                    _ -> -1
         else if ( (ex >= nx) && (ex == 2*nx-1) ) then
                case b of
                    2 -> y-nx 
                    4 -> y-1
                    5 -> y
                    7 -> y+nx-1
                    _ -> -1
         else -1
 in if ( (x < 1) || (x > nedges) ) then -1 else x




-- | Oracle /A/. It is equivalent to the Matlab function
-- 'getBandNodeValues'.
--
-- 'getNodeValuesMoreOutputs v b ...'  outputs the node of the edge
-- connected to vertex v in band b, and a real number parameterized by
-- the 'BoolParam' parameter: the magnitude (PFalse) or the phase
-- (PTrue) of the complex value at the corresponding place in the matrix A.
build_circuit
getNodeValuesMoreOutputs :: 
    Int -> Int -> Int -> Int -> [(Double,Double)] -> Double -> Double -> Double -> BoolParam 
    -> Int -> (Int, Double)
getNodeValuesMoreOutputs v' b' nx ny scatteringnodes lx ly k argflag maxConnectivity =
   let maxC = getIntFromParam maxConnectivity in
   let b = getIntFromParam b' in
   let nedges = (nx - 1)*ny + nx*(ny - 1) in
   let flag = v' <= nedges in
   let v = (if flag then v' else (v' - nedges)) in
   let nodeDefault = (if flag then v + nedges else v) in
   let valueDefault = 0.0 in
   let indicesDefault = (-1, -1) in
   let isvalid = checkedge v scatteringnodes nx ny 
   in 
   if ( (not isvalid) && b == 5 ) then
 
     let indices = (if flag then (v, v + nedges) else (v + nedges, v)) in
     case argflag of
        PTrue  -> (nodeDefault, valueDefault)
        PFalse -> (nodeDefault, 1.0)
 
   else if ( (not isvalid) && b /= 5) then (nodeDefault, valueDefault)
 
   else if ((b > maxC + 2) || (b <= 0)) then (nodeDefault, valueDefault)
 
   else
 
   let x = convertband v b' nx ny in
 
   if (x == -1) then (nodeDefault, valueDefault)
   else
 
   let isvalid = checkedge x scatteringnodes nx ny in
 
   if isvalid then
 
     let ax = calcmatrixelement v x nx ny lx ly k in
     let (node, indices) = if flag then (x + nedges, (v, x + nedges)) 
                           else (x, (v+nedges,x)) in
     let value = case argflag of
                   PTrue -> atan2  (imagPart ax) (realPart ax)
                   PFalse -> magnitude ax
     in (node, value)
     
   else
     (nodeDefault, valueDefault)




-- | Auxiliary function for oracle /b/. The inputs are:
-- 
-- * /y/ :: 'Int' - Global edge index.  Note this is the unmarked /y/
-- coordinate, i.e. the coordinate without scattering regions removed;
-- 
-- * /nx/ :: 'Int' - Number of vertices left to right;
-- 
-- * /ny/ :: 'Int' - Number of vertices top to bottom;
-- 
-- * /lx/ :: 'Double' - Length of horizontal edges (distance between vertices in /x/ direction);
-- 
-- * /ly/ :: 'Double' - Length of vertical edges (distance between vertices in /y/ direction);
-- 
-- * /k/ :: 'Double' - Plane wave wavenumber;
-- 
-- * θ :: 'Double' - Direction of wave propagation;
-- 
-- * /E0/ :: 'Double' - Magnitude of incident plane wave.
-- 
-- The output is the magnitude of the electric field on edge /y/.
build_circuit
calcincidentfield :: --
	-- Inputs
		Int -- int y - Global edge index.  Note this is the unmarked y coordinate, 
			-- i.e. the coordinate without scattering regions removed.
	-> Int -- int nx - Number of vertices left to right
	-> Int --  int ny - Number of vertices top to bottom
	-> Double -- float lx - Length of horizontal edges (distance between vertices in x direction)
	-> Double -- float ly - Length of vertical edges (distance between vertices in y direction)
	-> Double -- float k - Plane wave wavenumber
	-> Double -- float theta - Direction of wave propagation
	-> Double -- float E0 - Magnitude of incident plane wave
	-- Outputs
	-> Complex Double -- complex float e - Magnitude of electric field on edge y
calcincidentfield y nx ny lx ly k theta e0 = 
        let (xg, yg) = itoxy y nx ny in
        --Determine whether edge is horizontal or vertical
        let isvertical = xg >= nx in
        let (xvalueTmp, yvalueTmp) = edgetoxy y nx ny in
        let xvalue = xvalueTmp * lx in
        let yvalue = yvalueTmp * ly in
        -- Convert x and y edge coordinates to x and y values and caluculate field
        if isvertical then
          mkPolar (-cos(theta)*e0) ( -k*(xvalue*cos(theta)+yvalue*sin(theta)))
        else
          mkPolar (sin(theta)*e0) ( -k*(xvalue*cos(theta)+yvalue*sin(theta)))


-- | Auxiliary function for oracle /b/.
build_circuit
getconnection :: Int -> Int -> Int -> Int -> Int -> Int
getconnection y i' nx ny maxConnectivity =
  let i = getIntFromParam i' in
  let maxC = getIntFromParam maxConnectivity in
  let (ex,ey) = itoxy y nx ny in
  let x = if ( (ex < nx) && (ey /= 1) ) then 
            case i' of 
                1 -> y-2*nx+1
                2 -> y-nx
                3 -> y-nx+1
                4 -> y
                5 -> y+nx-1
                6 -> y+nx
                7 -> y+2*nx-1
                _ -> -1
          else if ( (ex < nx) && (ey == 1) ) then
            case i' of
                1 -> y
                2 -> y+nx-1
                3 -> y+nx
                4 -> y+2*nx-1
                _ -> -1
          else if ( (ex >= nx) && (ex /= nx) && (ex /= 2*nx-1) ) then 
             case i' of 
                1 -> y-nx
                2 -> y-nx+1
                3 -> y-1
                4 -> y
                5 -> y+1
                6 -> y+nx-1
                7 -> y+nx
                _ -> -1
          else if ( (ex >= nx) && (ex == nx) ) then
             case i' of
                1 -> y-nx+1
                2 -> y
                3 -> y+1
                4 -> y+nx
                _ -> -1
          else if ( (ex >= nx) && (ex == 2*nx-1) ) then
             case i' of
                1 -> y-nx
                2 -> y-1
                3 -> y
                4 -> y+nx-1
                _ -> -1
          else -1
  in
  if (i > maxC) then -1
  else if (x > nx*(ny-1)+ny*(nx-1)) then -1 
  else x



-- | Auxiliary function to @'template_paramZero'@.
build_circuit
local_loop_with_index_aux :: Int -> Int -> t -> (Int -> t -> t) -> t
local_loop_with_index_aux i n x f = 
   case paramMinus n i of
     0 -> x
     _ -> local_loop_with_index_aux (paramSucc i) n (f i x) f


-- | Local version of @'loop_with_index'@, for lifting.
build_circuit
local_loop_with_index :: Int -> t -> (Int -> t -> t) -> t
local_loop_with_index n x f = local_loop_with_index_aux paramZero n x f


-- | Oracle /b/.
build_circuit
getKnownWeights :: Int -> Int -> Int -> [(Double,Double)] -> Double -> Double -> Double -> Double -> Double -> Int -> Complex Double
getKnownWeights y nx ny scatteringnodes lx ly k theta e0 maxConnectivity =
   let makeConnections i connections = let x = getconnection y (paramSucc i) nx ny maxConnectivity in
                                       let t = not $ checkedge x scatteringnodes nx ny in 
                                       (x,t):connections
   in
   let calcTang b (c,t) = if t 
                          then let matElt = calcmatrixelement y c nx ny lx ly k in
                               let incField = calcincidentfield c nx ny lx ly k theta e0
                               in b - matElt * incField
                          else b
   in
   let connections = local_loop_with_index maxConnectivity [] makeConnections in
   if (not $ checkedge y scatteringnodes nx ny) then 0.0 :+ 0.0
   else foldl calcTang (0.0 :+ 0.0) connections





----------------------------------------------------------------------
----------------------------------------------------------------------
-- Testing functions

test_template_sinc = do
      f <- template_sinc
      r <- qinit (0 :: FDouble)
      f r
      return ()

test_template_itoxy = do
      f <- template_itoxy
      x <- qinit (0 :: FSignedInt)
      y <- qinit (0 :: FSignedInt)
      z <- qinit (0 :: FSignedInt)
      g <- f x
      h <- g y
      k <- h z
      return ()

test_template_edgetoxy = do
      f <- template_edgetoxy
      x <- qinit (0 :: FSignedInt)
      y <- qinit (0 :: FSignedInt)
      z <- qinit (0 :: FSignedInt)
      g <- f x
      h <- g y
      k <- h z
      return ()

test_template_calcRweights = do
      f <- template_calcRweights
      n1 <- qinit (0 :: FSignedInt)
      n2 <- qinit (0 :: FSignedInt)
      n3 <- qinit (0 :: FSignedInt)
      x1 <- qinit (0 :: FDouble)
      x2 <- qinit (0 :: FDouble)
      x3 <- qinit (0 :: FDouble)
      x4 <- qinit (0 :: FDouble)
      x5 <- qinit (0 :: FDouble)
      f1 <- f n1
      f2 <- f1 n2
      f3 <- f2 n3
      g1 <- f3 x1
      g2 <- g1 x2
      g3 <- g2 x3
      g4 <- g3 x4
      g5 <- g4 x5
      return ()

test_template_calcincidentfield = do
   y' <- qinit (0 :: FSignedInt)
   nx' <- qinit (0 :: FSignedInt)
   ny' <- qinit (0 :: FSignedInt)
   lx' <- qinit (0 :: FDouble)
   ly' <- qinit (0 :: FDouble)
   k' <- qinit (0 :: FDouble)
   theta' <- qinit (0 :: FDouble)
   e0' <- qinit (0 :: FDouble)
   f <- template_calcincidentfield 
   f1 <- f y'
   f2 <- f1 nx'
   f3 <- f2 ny'
   f4 <- f3 lx'
   f5 <- f4 ly'
   f6 <- f5 k'
   f7 <- f6 theta'
   f8 <- f7 e0'
   return ()

test_template_calcmatrixelement = do
   y1 <- qinit (0 :: FSignedInt)
   y2 <- qinit (0 :: FSignedInt)
   nx <- qinit (0 :: FSignedInt)
   ny <- qinit (0 :: FSignedInt)
   lx <- qinit (0 :: FDouble)
   ly <- qinit (0 :: FDouble)
   k  <- qinit (0 :: FDouble)
   f <- template_calcmatrixelement
   f1 <- f y1
   f2 <- f1 y2
   f3 <- f2 nx
   f4 <- f3 ny
   f5 <- f4 lx
   f6 <- f5 ly
   f7 <- f6 k
   return ()

test_template_getconnection = do
   y <- qinit (0 :: FSignedInt)
   nx <- qinit (0 :: FSignedInt)
   ny <- qinit (0 :: FSignedInt)
   f <- template_getconnection
   f1 <- f y
   f2 <- f1 6
   f3 <- f2 nx
   f4 <- f3 ny
   f5 <- f4 7
   return ()

test_template_checkedge = do
   y <- qinit (0 :: FSignedInt)
   nx <- qinit (0 :: FSignedInt)
   ny <- qinit (0 :: FSignedInt)
   s <- qinit [(0 :: FDouble,0 :: FDouble),(0 :: FDouble,0 :: FDouble)]
   f <- template_checkedge
   f1 <- f y
   f2 <- f1 s
   f3 <- f2 nx
   f4 <- f3 ny
   return ()

