-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS -fcontext-stack=50 #-}

-- | This module provides an implementation of the Quantum Walk for
-- the Triangle Finding Problem. 
--
-- The algorithm works by performing a Grover-based quantum walk on
-- a larger graph /H/, called the Hamming graph associated to /G/.
-- We refer to this part of the algorithm as the /outer/ walk. 
-- The subroutine used to check whether a triangle has been found 
-- is itself a quantum walk, the /inner/ walk. 
--
-- The overall algorithm is parameterized on integers /l/, /n/ and /r/
-- specifying respectively the length /l/ of the integers used by the
-- oracle, the number 2[sup /n/] of nodes of /G/ and the size 2[sup /r/]
-- of Hamming graph tuples.

module Algorithms.TF.QWTFP where

import Prelude hiding (mapM, mapM_)

import Quipper
import Quipper.Internal (BType)
import QuipperLib.Arith
import Algorithms.TF.Definitions

import Data.IntMap (IntMap, adjust, insert, size)
import qualified Data.IntMap as IntMap
import Data.Traversable (mapM)
import Data.Foldable (mapM_)
import Control.Monad (foldM)


-- ======================================================================
-- * Main TF algorithm

-- | Algorithm 1. Do a quantum walk on the Hamming graph associated with /G/. 
-- Returns a quadruple /(testTMeasure, wMeasure, TMeasure, EMeasure)/ 
-- where /wMeasure/ contains a node of the triangle with the 
-- other two nodes in /TMeasure/. 
a1_QWTFP :: QWTFP_spec -> Circ (Bit,CNode,IntMap CNode,IntMap (IntMap Bit))
a1_QWTFP oracle@(n,r,edgeOracle,_) = do
  comment "ENTER: a1_QWTFP"
  let nn = 2^n 
  let rr = 2^r 
  let rbar = max ((2 * r) `div` 3) 1 
  let rrbar = 2^rbar 
  let tm = 2^(n - r)
  let tw = floor $ sqrt $ fromIntegral rr

  testTEdge <- a2_ZERO False
  tt <- a3_INITIALIZE (intMap_replicate rr (replicate n False)) 
  i <- a3_INITIALIZE (intm r 0)
  v <- a3_INITIALIZE (replicate n False) 

  (tt, ee) <- a5_SETUP oracle tt

  (tt,i,v,ee) <- box_loopM "a1_loop1" tm (tt,i,v,ee)
    (\(tt,i,v,ee) -> do

      ((tt,ee),_) <- with_computed_fun (tt,ee)

        (\(tt,ee) -> a15_TestTriangleEdges oracle tt ee)
  
        (\(tt,ee,w,triTestT,triTestTw) -> do
          phaseFlipUnless (triTestT .==. 0 .&&. triTestTw .==. 0)
          return ((tt,ee,w,triTestT,triTestTw),()))

      (tt,i,v,ee) <- box_loopM "a1_loop2" tw (tt,i,v,ee) (\(a,b,c,d) -> a6_QWSH oracle a b c d)
      return (tt,i,v,ee))

  (tt,ee,w,triTestT,triTestTw) <- a15_TestTriangleEdges oracle tt ee

  testTEdge <- qor testTEdge [(triTestT, True), (triTestTw, True)]

  testTMeasure <- measure testTEdge
  wMeasure <- measure w
  ttMeasure <- measure tt
  eeMeasure <- measure ee
  qdiscard (i,v,triTestT,triTestTw)
  comment_with_label "EXIT: a1_QWTFP" (testTMeasure, wMeasure, ttMeasure, eeMeasure) ("testTMeasure", "wMeasure", "ttMeasure", "eeMeasure")
  return (testTMeasure, wMeasure, ttMeasure, eeMeasure)


-- ======================================================================
-- *Utility subroutines

-- | Algorithm 2.
-- Initialize the qubits in a register to a specified state. 
-- Defined using the more generic 'qinit'.    
a2_ZERO :: QShape a qa ca => a -> Circ qa
a2_ZERO b = do
  comment "ENTER: a2_ZERO"
  q <- qinit b
  comment_with_label "EXIT: a2_ZERO" q "q"
  return q

-- | Algorithm 3.
-- Initialize to a specified state then apply a Hadamard gate to 
-- the qubits in a register.  
a3_INITIALIZE :: QShape a qa ca => a -> Circ qa
a3_INITIALIZE reg = do
  comment "ENTER: a3_INITIALIZE"
  zreg <- a2_ZERO reg
  hzreg <- a4_HADAMARD zreg 
  comment_with_label "EXIT: a3_INITIALIZE" hzreg "hzreg"
  return hzreg

-- | Algorithm 4.
-- Apply a Hadamard gate to every qubit in the given quantum data. 
-- Defined using the more generic 'map_hadamard'.    
a4_HADAMARD :: QData qa => qa -> Circ qa
a4_HADAMARD q = do
  comment_with_label "ENTER: a4_HADAMARD" q "q"
  q <- map_hadamard q
  comment_with_label "EXIT: a4_HADAMARD" q "q"
  return q

-- | Algorithm 5. 
-- Set up the register /ee/ with the edge information 
-- for the nodes contained in /tt/.
a5_SETUP :: QWTFP_spec -> (IntMap QNode) -> Circ (IntMap QNode, IntMap (IntMap Qubit))
a5_SETUP oracle@(n,r,edgeOracle,_) = box "a5" $ \tt -> do
  comment_with_label "ENTER: a5_SETUP" tt "tt"
  let rr = 2^r 
  ee <- qinit $ IntMap.fromList [(j,(intMap_replicate j False)) | j <- [0..(rr-1)]]
  ee <- loop_with_indexM (rr) ee (\k ee ->
          loop_with_indexM k ee (\j ee -> do
            edgejk <- edgeOracle (tt ! j) (tt ! k) (ee ! k ! j)
            ee <- return $ adjust (insert j edgejk) k ee
            return ee))
  comment_with_label "EXIT: a5_SETUP" (tt,ee) ("tt","ee")
  return (tt, ee)


-- ======================================================================
-- ** The outer quantum walk and the standard Qram

-- | Algorithm 6. 
-- Do a quantum walk step on the Hamming graph.
a6_QWSH :: QWTFP_spec -> (IntMap QNode) -> QDInt -> QNode -> (IntMap (IntMap Qubit))
        -> Circ (IntMap QNode, QDInt, QNode, IntMap (IntMap Qubit))
a6_QWSH oracle@(n,r,edgeOracle,qram) = box "a6" $ \tt i v ee -> do
  comment_with_label "ENTER: a6_QWSH" (tt, i, v, ee) ("tt", "i", "v", "ee")
  with_ancilla_init (replicate n False) $ \ttd -> do 
    with_ancilla_init (intMap_replicate (2^r) False) $ \eed -> do 
      (i,v) <- a7_DIFFUSE (i,v)

      ((tt,i,v,ee,ttd,eed),_) <- with_computed_fun (tt,i,v,ee,ttd,eed)

        (\(tt,i,v,ee,ttd,eed) -> do
          (i,tt,ttd) <- qram_fetch qram i tt ttd 
          (i,ee,eed) <- a12_FetchStoreE i ee eed
          (tt,ttd,eed) <- a13_UPDATE oracle tt ttd eed
          (i,tt,ttd) <- qram_store qram i tt ttd
          return (tt,i,v,ee,ttd,eed))
            
        (\(tt,i,v,ee,ttd,eed) -> do
          (ttd,v) <- a14_SWAP ttd v
          return ((tt,i,v,ee,ttd,eed),()))
  
      comment_with_label "EXIT: a6_QWSH" (tt, i, v, ee) ("tt", "i", "v", "ee")
      return (tt,i,v,ee)

-- | Algorithm 7. 
-- Diffuse a piece of quantum data, in the Grover search sense of 
-- reflecting about the average. 
-- 
-- Note: relies on @'shape' q@ corresponding to the “all false” state. 
a7_DIFFUSE :: (QData qa) => qa -> Circ qa
a7_DIFFUSE = box "a7" $ \q -> do
  comment_with_label "ENTER: a7_DIFFUSE" q "q"
  q <- a4_HADAMARD q
  phaseFlipUnless $ q .==. qc_false q
  q <- a4_HADAMARD q
  comment_with_label "EXIT: a7_DIFFUSE" q "q"
  return q

-- | Algorithm 8. 
-- Perform a quantum-addressed fetch operation.
-- This fetches the /i/-th element from /tt/ into /ttd/.
-- Precondition: /ttd/ = 0. 
-- 
-- This could be implemented more efficiently using the qRAM implementation 
-- in "Alternatives".
a8_FetchT :: (QData qa) => QDInt -> IntMap qa -> qa -> Circ (QDInt, IntMap qa, qa)
a8_FetchT = box "a8" $ \i tt ttd -> do
  comment_with_label "ENTER: a8_FetchT" (i,tt,ttd) ("i","tt","ttd")
  let r = qdint_length i
  (i,tt,ttd) <- loop_with_indexM (2^r) (i,tt,ttd)
    (\j (i,tt,ttd) -> do 
      let ttj = tt ! j
      (ttj,ttd) <- mapBinary
        (\q p -> do     
          p <- qnot p `controlled` q .&&. i .==. (fromIntegral j)
          return (q,p)) 
        (tt ! j) ttd
      return (i, insert j ttj tt, ttd))
  comment_with_label "EXIT: a8_FetchT" (i,tt,ttd) ("i","tt","ttd")
  return (i,tt,ttd)

-- | Algorithms 9. 
-- Perform a quantum-addressed store operation: 
-- store /ttd/ into the /i/-th element from /tt/.
-- Analogous to 'a8_FetchT'.
a9_StoreT :: (QData qa) => QDInt -> IntMap qa -> qa -> Circ (QDInt, IntMap qa, qa)
a9_StoreT = box "a9" $ \i tt ttd -> do	
  comment_with_label "ENTER: a9_StoreT" (i,tt,ttd) ("i","tt","ttd")
  let r = qdint_length i
  (i,tt,ttd) <- loop_with_indexM (2^r) (i,tt,ttd)
    (\j (i,tt,ttd) -> do 
      (ttj,ttd) <- mapBinary
        (\q p -> do     
          q <- qnot q `controlled` p .&&. i .==. (fromIntegral j)
          return (q,p)) 
        (tt ! j) ttd
      return (i, insert j ttj tt, ttd))
  comment_with_label "EXIT: a9_StoreT" (i,tt,ttd) ("i","tt","ttd")
  return (i,tt,ttd)


-- | Algorithm 10. 
-- Perform a quantum-addressed swap: 
-- swap /ttd/ with the /i/-th element of /tt/.
-- Analogous to 'a8_FetchT' and 'a9_StoreT'.
a10_FetchStoreT :: (QData qa) => QDInt -> IntMap qa -> qa -> Circ (QDInt, IntMap qa, qa)
a10_FetchStoreT = box "a10" $ \i tt ttd -> do
  comment_with_label "ENTER: a10_FetchStoreT" (i,tt,ttd) ("i","tt","ttd")
  let r = qdint_length i
  (i,tt,ttd) <- loop_with_indexM (2^r) (i,tt,ttd)
    (\j (i,tt,ttd) -> do
      (qq,ttd) <- a14_SWAP (tt ! j) ttd
                  `controlled`  i .==. (fromIntegral j)
      return (i,(insert j qq tt), ttd))
  comment_with_label "EXIT: a10_FetchStoreT" (i,tt,ttd) ("i","tt","ttd")
  return (i,tt,ttd)
  

-- | Algorithm 11.  Perform a quantum-addressed fetch operation. This
-- is a somewhat specialized addressed fetching operation.
a11_FetchE :: QDInt -> IntMap (IntMap Qubit) -> IntMap Qubit
              -> Circ (QDInt, IntMap (IntMap Qubit), IntMap Qubit)
a11_FetchE = box "a11" $ \i qs ps -> do
  comment_with_label "ENTER: a11_FetchE" (i, qs, ps) ("i", "qs", "ps")
  let r = qdint_length i
  (i,qs,ps) <- loop_with_indexM (2^r) (i,qs,ps) (\j (i,qs,ps) ->
    loop_with_indexM j (i,qs,ps) (\k (i,qs,ps) -> do
      pk <- qnot (ps ! k) `controlled`
              (qs ! j ! k) .&&. i .==. (fromIntegral j)
      ps <- return $ insert k pk ps
      pj <- qnot (ps ! j) `controlled` 
              (qs ! j ! k) .&&. i .==. (fromIntegral k) 
      ps  <- return $ insert j pj ps
      return (i,qs,ps)))  
  comment_with_label "EXIT: a11_FetchE" (i, qs, ps) ("i", "qs", "ps")
  return (i,qs,ps)

-- | Algorithm 12. 
-- Perform a quantum-addressed swap. Analogous to 'a11_FetchE'.
a12_FetchStoreE :: QDInt ->  IntMap (IntMap Qubit) -> IntMap Qubit
                   -> Circ (QDInt, IntMap (IntMap Qubit), IntMap Qubit)
a12_FetchStoreE = box "a12" $ \i qs ps -> do
  comment_with_label "ENTER: a12_FetchStoreE" (i, qs, ps) ("i", "qs", "ps")
  let r = qdint_length i
  (i,qs,ps) <- loop_with_indexM (2^r) (i,qs,ps) (\j (i,qs, ps) ->
    loop_with_indexM j (i,qs, ps) (\k (i,qs, ps) -> do
      (q,p) <- a14_SWAP (qs ! j ! k) (ps ! k)
                   `controlled` i .==. (fromIntegral j)
      (qs,ps) <- return (adjust (insert k q) j qs, insert k p ps)
      (q,p) <- a14_SWAP (qs ! j ! k) (ps ! j)
                   `controlled` i .==. (fromIntegral k)
      (qs,ps) <- return (adjust (insert k q) j qs, insert j p ps)
      return (i,qs,ps)))
  comment_with_label "EXIT: a12_FetchStoreE" (i, qs, ps) ("i", "qs", "ps")
  return (i,qs,ps)

-- | Algorithm 13. 
-- Given a list of nodes /tt/, a distinguished node /ttd/, 
-- and a list of bits /eed/, either:
--
-- * store the edge information for /(ttd,tt)/ into /eed/, if /eed/ is initially 0; or
--
-- * zero /eed/, if it initially holds the edge information. 
a13_UPDATE :: QWTFP_spec -> IntMap QNode -> QNode -> IntMap Qubit
              -> Circ (IntMap QNode, QNode, IntMap Qubit)
a13_UPDATE oracle@(n,r,edgeOracle,_) = box "a13" $ \tt ttd eed -> do
  comment_with_label "ENTER: a13_UPDATE" (tt,ttd,eed) ("tt","ttd","eed")
  (tt,ttd,eed) <- loop_with_indexM (2^r) (tt,ttd,eed) (\j (tt,ttd,eed) -> do
    e <- edgeOracle (tt ! j) ttd (eed ! j)
    return (tt,ttd,insert j e eed))
  comment_with_label "EXIT: a13_UPDATE" (tt,ttd,eed) ("tt","ttd","eed")
  return (tt,ttd,eed)

-- | Algorithm 14.  Swap two registers of equal size. This is a
-- generic function and works for any quantum data type.
a14_SWAP :: QCData qa => qa -> qa -> Circ (qa, qa)
a14_SWAP q r = do
  comment_with_label "ENTER: a14_SWAP" (q,r) ("q", "r")
  (q,r) <- swap q r
  comment_with_label "EXIT: a14_SWAP" (q,r) ("q", "r")
  return (q,r)

-- | The qRAM operations from Algorithms 8–10 wrapped into a 'Qram' object.
standard_qram :: Qram
standard_qram = Qram {
  qram_fetch = a8_FetchT,
  qram_store = a9_StoreT,
  qram_swap = a10_FetchStoreT
}

-- ======================================================================
-- ** The inner quantum walk

-- | A type to hold the Graph Collision Quantum Walk Registers 
-- /(tau, iota, sigma, eew, cTri, triTestT)/, used in 'a20_GCQWStep'.
type GCQWRegs = (IntMap QDInt, QDInt, QDInt, IntMap Qubit, QDInt, Qubit)

-- | Algorithm 15: /TestTriangleEdges/.  
-- Test whether the nodes /tt/ contain a pair that can be extended to a 
-- triangle in the graph. Used as the test function in the outer quantum 
-- walk. Seeks triangles in two different ways:
-- 
-- 1. Entirely within the nodes /tt/.  If found, set qubit /triTestT/.
-- 
-- 2. With two vertices from /tt/, a third anywhere in the graph.  If found, 
-- set qubit /triTestTw/, and return the third vertex as /w/.  This is 
-- implemented using an “inner quantum walk” to seek /w/.
a15_TestTriangleEdges :: 
  QWTFP_spec  -- ^ The ambient oracle.
  -> IntMap QNode       -- ^ /tt/, an /R/-tuple of nodes.
  -> IntMap (IntMap Qubit)  -- ^ /ee/, a cache of the edge information between nodes in /tt/.
  -> Circ (IntMap QNode, IntMap (IntMap Qubit), QNode, Qubit,Qubit) -- ^ Return /(tt, ee, w, triTestT,triTestTw)/.
a15_TestTriangleEdges oracle = box "a15" $ \tt ee -> do
  comment_with_label "ENTER: a15_TestTriangleEdges" (tt,ee) ("tt","ee")
  (ee,triTestT) <- a16_TriangleTestT ee
  (tt,ee,w,triTestT) <- a18_TriangleEdgeSearch oracle tt ee triTestT
  (tt,ee,w,triTestTw) <- a17_TriangleTestTw oracle tt ee w
  comment_with_label "EXIT: a15_TestTriangleEdges" (tt,ee,w,triTestT,triTestTw) ("tt","ee","w","triTestT","triTestTw")
  return (tt,ee,w,triTestT,triTestTw)

-- | Algorithm 16: /TriangleTestT ee triTestT/.
-- Search exhaustively over the array /ee/ of edge data, seeking a triangle. 
-- Whenever one is found, flip the qubit /triTestT/.  
a16_TriangleTestT :: IntMap (IntMap Qubit) -> Circ (IntMap (IntMap Qubit), Qubit)
a16_TriangleTestT = box "a16" $ \ee -> do
  comment_with_label "ENTER: a16_TriangleTestT" ee "ee"
  let rr = size ee
  (ee,triTestT) <- with_computed_fun ee
     
    (\ee -> do
      cTri <- qinit (intm (ceiling (logBase 2 (fromIntegral (rr `choose` 3)))) 0)  
      cTri <- foldM (\cTri (i,j,k) -> do
                  cTri <- increment cTri `controlled` (ee ! j ! i) .&&. (ee ! k ! i) .&&. (ee ! k ! j)
                  return cTri) 
               cTri [(i,j,k) | i <- [0..rr-1], j <- [i+1..rr-1], k <- [j+1..rr-1]]
      return (ee,cTri))
         
    (\(ee,cTri) -> do
      triTestT <- qinit True
      triTestT <- qnot triTestT `controlled` cTri .==. 0
      return ((ee,cTri),triTestT))
        
  comment_with_label "EXIT: a16_TriangleTestT" (ee,triTestT) ("ee","triTestT")
  return (ee,triTestT)

{-Alternative implementation, using (a lot of) extra ancillas instead of a counter: 
a16_TriangleTestT :: [[Qubit]] -> Qubit -> Circ ([[Qubit]], Qubit)
a16_TriangleTestT ee triTestT = do
  let rr = length ee
  ((ee,triTestT),_) <- with_computed_fun
     
    (\(ee,triTestT) -> do
      tests <- mapM (\(i,j,k) -> do
          t <- a2_ZERO False
          t <- qnot t `controlled` 
                 [(ee !! j !! i),(ee !! k !! i),(ee !! k !! j)]
          return(t))
        [(i,j,k) | i <- [0..rr-1], j <- [i+1..rr-1], k <- [j+1..rr-1]]
      return (ee,triTestT,tests))
        
    (ee,triTestT)
         
    (\(ee,triTestT,tests) -> do
      triTestT <- qor triTestT (map (\p -> (p,True)) tests)
      return ((ee,triTestT,tests),()))
        
  return (ee,triTestT)-}


-- | Algorithm 17: /TriangleTestTw ee triTestTw/.
-- Search exhaustively for a pair of nodes in /tt/ that form a triangle with /w/.  
-- Whenever a triangle found, flip qubit /triTestTw/. 
a17_TriangleTestTw :: QWTFP_spec -- ^ The ambient oracle.
              -> IntMap QNode    -- ^ /tt/, an /R/-tuple of nodes.
              -> IntMap (IntMap Qubit)  -- ^ /ee/, a cache of the edge data for /T/.
              -> QNode      -- ^ /w/, another node.
              -> Circ (IntMap QNode, IntMap (IntMap Qubit), QNode, Qubit) -- ^ return /(tt,ee,w,triTestTw)/.
a17_TriangleTestTw oracle@(n,r,edgeOracle,_) = box "a17" $ \tt ee w -> do
  comment_with_label "ENTER: a17_TriangleTestTw" (tt,ee,w) ("tt","ee","w")
  let rr = size ee
  with_ancilla_init (intMap_replicate rr False) $ \eed -> do
    ((tt,ee,w,eed),triTestTw) <- with_computed_fun (tt,ee,w,eed)
     
      (\(tt,ee,w,eed) -> do
        eed <- mapWithKeyM (\k e -> do
                 e <- edgeOracle (tt ! k) w e
                 return e) 
               eed
        cTri <- qinit (intm (ceiling (logBase 2 (fromIntegral (rr `choose` 2)))) 0)  
        cTri <- foldM
          (\cTri (i,j) ->
            increment cTri `controlled` (ee ! j ! i) .&&. (eed ! i) .&&. (eed ! j)) 
          cTri
          [(i,j) | i <- [0..rr-1], j <- [i+1..rr-1]]
        return (tt,ee,w,eed,cTri))
         
      (\(tt,ee,w,eed,cTri) -> do
        triTestTw <- qinit True
        triTestTw <- qnot triTestTw `controlled` cTri .==. 0
        return ((tt,ee,w,eed,cTri),triTestTw))
        
    comment_with_label "EXIT: a17_TriangleTestTw" (tt,ee,w,triTestTw) ("tt","ee","w","triTestTw")
    return (tt,ee,w,triTestTw)   

{-Alternative implementation, using (a lot of) extra ancillas instead of a counter: 
a17_TriangleTestTw oracle@(n,r,edgeOracle) tt ee w triTestTw = do
  let rr = length ee
  with_ancilla_list rr $ \eed -> do
    ((tt,ee,w,triTestTw,eed),_) <- with_computed_fun
     
      (\(tt,ee,w,triTestTw,eed) -> do
        eed <- mapM (\(b,a) -> do
          b <- edgeOracle (tt !! a) w b
          return (b)) 
          (zip (eed) [0..rr-1])
        tests <- mapM (\(i,j) -> do
          t <- a2_ZERO False
          t <- qnot t `controlled` (ee !! j !! i) .&&. (eed !! i) .&&. (eed !! j)
          return(t))
          [(i,j) | i <- [0..rr-1], j <- [i+1..rr-1]]    
        return (tt,ee,w,triTestTw,eed,tests))           
        
      (tt,ee,w,triTestTw,eed)
         
      (\(tt,ee,w,triTestTw,eed,tests) -> do
        triTestTw <- qor triTestTw (map (\p -> (p,True)) tests)
        return ((tt,ee,w,triTestTw,eed,tests),()))
        
    return (tt,ee,w,triTestTw)-}


-- | Algorithm 18: /TriangleEdgeSearch/.
-- Use Grover search to seek a node /w/ that forms a triangle with some pair of
-- nodes in /tt/, unless a triangle has already been found (recorded in /triTestT/), 
-- in which case do nothing. 
a18_TriangleEdgeSearch :: QWTFP_spec -- ^ The ambient oracle.
  -> IntMap QNode           -- ^ /tt/, an /R/-tuple of nodes.
  -> IntMap (IntMap Qubit)  -- ^ /ee/, a cache of edge data for /R/.
  -> Qubit                  -- ^ /triTestT/, test qubit recording if a triangle has already been found.
  -> Circ (IntMap QNode, IntMap (IntMap Qubit), QNode, Qubit) -- ^ Return /(tt, ee, w, regs)/.
a18_TriangleEdgeSearch oracle@(n,r,edgeOracle,_) = box "a18" $ \tt ee triTestT -> do
  comment_with_label "ENTER: a18_TriangleEdgeSearch" (tt,ee,triTestT) ("tt","ee","triTestT")
  let nn = 2^n
      tG = floor (pi/4 *( sqrt ( fromIntegral nn)))

  w <- a2_ZERO (replicate n False)
  w <- a4_HADAMARD w

  box_loopM "a18_loop" tG (tt,ee,w,triTestT) (\(tt,ee,w,triTestT) -> do
    ((tt,ee,w,triTestT),()) <- with_computed_fun (tt,ee,w,triTestT)

      (\(tt,ee,w,triTestT) -> do
        (tt,ee,w,triTestT,cTri) <- a19_GCQWalk oracle tt ee w triTestT
          
        cTri_nonzero <- qinit True
        cTri_nonzero <- qnot cTri_nonzero `controlled` cTri .==. 0

        return (tt,ee,w,triTestT,cTri,cTri_nonzero))
          
      (\(tt,ee,w,triTestT,cTri,cTri_nonzero) -> do
        phaseFlipIf $ (triTestT .==. 0) .&&. cTri_nonzero
        return ((tt,ee,w,triTestT,cTri,cTri_nonzero),()))
       
    w <- a7_DIFFUSE w
    return (tt,ee,w,triTestT))
  comment_with_label "EXIT: a18_TriangleEdgeSearch" (tt,ee,w,triTestT) ("tt","ee","w","triTestT")
  return (tt,ee,w,triTestT)

-- | Algorithm 19: /GCQWalk/ (“Graph Collision Quantum Walk”)
-- 
-- Perform graph collision on the /R/-tuple /tt/ and the node /w/, to determine
-- (with high probability) whether /w/ forms a triangle with some pair of nodes 
-- in /tt/.
a19_GCQWalk :: QWTFP_spec  -- ^ The ambient oracle.
        -> IntMap QNode    -- ^ /tt/, an /R/-tuple of nodes.
        -> IntMap (IntMap Qubit)  -- ^ /ee/, a cache of the edge data for /tt/.
        -> QNode      -- ^ /w/, a node.
        -> Qubit   -- ^ /triTestT/, test qubit to record if a triangle has already been found.
  -> Circ (IntMap QNode, IntMap (IntMap Qubit), QNode, Qubit, QDInt) -- ^ Return /(tt,ee,w,triTestT,cTri)/.
a19_GCQWalk oracle@(n,r,edgeOracle,qram) = box "a19" $ \tt ee w triTestT -> do
  comment_with_label "ENTER: a19_GCQWalk" (tt,ee,w,triTestT) ("tt","ee","w","triTestT")
  let nn = 2^n 
      rr = 2^r 
      rbar = max ((2 * r) `div` 3) 1
      rrbar = 2^rbar   
      tbarm = max (rr `div` rrbar) 1
      tbarw = floor $ sqrt $ fromIntegral rrbar

  cTri <- qinit (intm (2*rbar - 1) 0)

  with_ancilla_init
    ((intMap_replicate rrbar (intm r 0)),
     (intm rbar 0),
     (intm r 0),
     (intMap_replicate rrbar False))
    $ \(tau,iota,sigma,eew) -> do

      tau <- a4_HADAMARD tau
      iota <- a4_HADAMARD iota
      sigma <- a4_HADAMARD sigma  
  
      eew <- mapWithKeyM (\j eew_j -> do 
          let taub = tau ! j
          ttd <- qinit (replicate n False)
          (taub, tt, ttd) <- qram_fetch qram taub tt ttd
          eew_j <- edgeOracle ttd w eew_j
          (taub, tt, ttd) <- qram_fetch qram taub tt ttd
          qterm (replicate n False) ttd
          return eew_j)
        eew

      cTri <- foldM (\cTri j -> do
          let tau_j = tau ! j
          eed <- qinit (intMap_replicate rr False)
          (taub,ee,eed) <- a11_FetchE tau_j ee eed
          cTri <- foldM (\cTri k -> do
              let tau_k = tau ! k
  -- Note: the Fetch to eedd_k seems redundant here; why not control on (eedd !! k) directly?
              eedd_k <- qinit False         
              (tauc, eed, eedd_k) <- qram_fetch qram tau_k eed eedd_k
              cTri <- increment cTri `controlled` eedd_k .&&. (eew ! j) .&&. (eew ! k)
              (tauc, eed, eedd_k) <- qram_fetch qram tau_k eed eedd_k
              qterm False eedd_k
              return cTri)
            cTri [j+1..rrbar-1]
          (taub,ee,eed) <- a11_FetchE tau_j ee eed
          qterm (intMap_replicate rr False) eed
          return cTri)
        cTri [0..rrbar-1]

      (tt,ee,w,(tau,iota,sigma,eew,cTri,triTestT)) <- box_loopM "a19_loop1" tbarm
        (tt,ee,w,(tau,iota,sigma,eew,cTri,triTestT))

        (\(tt,ee,w,(e1,e2,e3,e4,cTri,triTestT)) -> do
          ((cTri,triTestT),()) <- with_computed_fun (cTri,triTestT)
           
            (\(cTri,triTestT) -> do
              cTri_nonzero <- qinit True
              cTri_nonzero <- qnot cTri_nonzero `controlled` cTri .==. 0 
              return (cTri,triTestT,cTri_nonzero))
          
            (\(cTri,triTestT,cTri_nonzero) -> do
              phaseFlipIf $ (triTestT .==. 0) .&&. cTri_nonzero 
              return ((cTri,triTestT,cTri_nonzero),()))

          box_loopM "a19_loop2" tbarw (tt,ee,w,(e1,e2,e3,e4,cTri,triTestT)) (\(b,c,d,e) -> a20_GCQWStep oracle b c d e))

      comment_with_label "EXIT: a19_GCQWalk" (tt,ee,w,triTestT,cTri) ("tt","ee","w","triTestT","cTri")
      return (tt,ee,w,triTestT,cTri)


-- | Algorithm 20: /GCQWStep/
-- Take one step in the graph collision walk (used in 'a19_GCQWalk' above).  
-- Uses many auxiliary registers.
-- The arguments are, in this order:
-- 
-- * The ambient oracle.
-- 
-- * /tt/, an /R/-tuple of nodes.
-- 
-- * /ee/, a cache of the edge data for /tt/.
-- 
-- * /w/, a node.
-- 
-- * /regs/, various workspace\/output registers.
-- 
-- * /ttd/, /eed/, /taud/, /eewd/, and /eedd/, local ancillas.
-- 
-- The function returns /(tt, ee, w, regs)/.
a20_GCQWStep :: QWTFP_spec                                       
        -> IntMap QNode   
        -> IntMap (IntMap Qubit) 
        -> QNode    
        -> GCQWRegs    
        -> Circ (IntMap QNode, IntMap (IntMap Qubit), QNode, GCQWRegs)    
a20_GCQWStep oracle@(n,r,edgeOracle,qram) = box "a20" $
  \tt ee w gcqwRegs@(tau,iota,sigma,eew,cTri,triTestT) -> do
  comment_with_label "ENTER: a20_GCQWStep" (tt,ee,w,tau,iota,sigma,eew,cTri,triTestT) ("tt","ee","w","tau","iota","sigma","eew","cTri","triTestT")
  let rr = 2^r 
      rbar = max ((2 * r) `div` 3) 1
      rrbar = 2^rbar   

  (iota, sigma) <- a7_DIFFUSE (iota, sigma)

  ((tt,ee,w,gcqwRegs),_) <- with_computed_fun (tt,ee,w,gcqwRegs)

    (\(tt,ee,w,gcqwRegs@(tau,iota,sigma,eew,cTri,triTestT)) -> do
      ttd <- qinit (replicate n False)
      eed <- qinit (intMap_replicate rr False)
      taud <- qinit (intm r 0)
      eewd <- qinit False
      eedd <- qinit (intMap_replicate rrbar False)

      (iota, tau, taud) <- qram_fetch qram iota tau taud
      (taud, tt, ttd) <- qram_fetch qram taud tt ttd
      (iota,eew,eewd) <- qram_swap qram iota eew eewd 
      (taud,ee,eed) <- a11_FetchE taud ee eed
      eedd <- mapWithKeyM (\k eeddb -> do
          let taub = tau ! k
          (taub, eed, eeddb) <- qram_fetch qram taub eed eeddb
          return eeddb)
        eedd
      cTri <- loop_with_indexM (rrbar-1) cTri (\a cTri -> do
        decrement cTri `controlled` (eedd ! a) .&&. (eewd) .&&. (eew ! a))
      eewd <- edgeOracle ttd w eewd
      eedd <- mapWithKeyM (\k e -> do
          let taub = tau ! k
          let eeddb = eedd ! k
          (taub, eed, eeddb) <- qram_fetch qram taub eed eeddb
          return e)
        eedd
      (taud,ee,eed) <- a11_FetchE taud ee eed
      (taud,tt,ttd) <- qram_fetch qram taud tt ttd
      (iota,tau,taud) <- qram_store qram iota tau taud
      return (tt,ee,w,gcqwRegs,ttd,eed,taud,eewd,eedd))

    (\(tt,ee,w,(tau,iota,sigma,eew,cTri,triTestT),ttd,eed,taud,eewd,eedd) -> do
      (taud,sigma) <- a14_SWAP taud sigma
      return ((tt,ee,w,(tau,iota,sigma,eew,cTri,triTestT),ttd,eed,taud,eewd,eedd),()))

  comment_with_label "ENTER: a20_GCQWStep" (tt,ee,w,gcqwRegs) ("tt","ee","w",("tau","iota","sigma","eew","cTri","triTestT"))
  return (tt,ee,w,gcqwRegs)
