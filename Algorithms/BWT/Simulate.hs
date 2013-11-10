-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module contains functions for simulating and debugging
-- BWT oracles.

module Algorithms.BWT.Simulate where

import Quipper hiding (comment)

import QuipperLib.Qureg
import QuipperLib.Simulation
import QuipperLib.Decompose

-- import other Quipper stuff
import Algorithms.BWT.Definitions
import Algorithms.BWT.BWT

import Libraries.Render
import Libraries.Sampling
import Libraries.Auxiliary

-- import other stuff
import Text.Printf
import Data.Bits

-- ======================================================================
-- * Generic simulation

-- | Inputs an oracle and prints out a list of colored edges in text
-- format. This is done by simulating the circuit for every possible
-- input, decomposed to the given 'GateBase'.
simulate_edges :: GateBase -> Oracle -> IO()
simulate_edges gb oracle =
  mapM_ output (sample_all0 (2^m'-1, 3))
  where
    m' = (m oracle)
    ofun c (a, b, r) = do
      let a_reg = qureg_of_qulist_te a
      let b_reg = qureg_of_qulist_te b
      (oraclefun oracle) c (a_reg, b_reg, r)
      return (a, b, r)
    
    simulate :: (Int, Int) -> (Int, Bool)
    simulate (c, a) = (b1, r1) where
      
      -- convert inputs to boollisttors
      a_in = boollist_of_int_bh m' a
      b_in = take m' $ repeat False
      r_in = False
    
      (a_out, b_out, r_out) = run_classical_generic (decompose_generic gb (ofun c)) (a_in, b_in, r_in)
      
      -- convert outputs to integers
      a1 = int_of_boollist_unsigned_bh a_out
      b1 = int_of_boollist_unsigned_bh b_out
      r1 = r_out
      
    output :: (Int, Int) -> IO()
    output (a, c) =
      case simulate (c, a) of
        (b, False) -> printf "%d ---%d---> %d\n" a c b
        (b, True) -> printf "%d ---%d---> None (%d)\n" a c b
        
-- | Input an oracle and output the colored edges in graphical
-- format. This is done by simulating the circuit for every possible
-- input. The second parameter is a boolean which determines whether
-- the node numbering follows the schema of the orthodox oracle
-- ('True') or the simple oracle ('False').
render_oracle :: GateBase -> Bool -> Oracle -> Document ()
render_oracle gb node_style oracle = do
  newpage (sc * width) (sc * height) $ do
    scale sc sc
    setlinewidth linewidth
    sequence_ [ output a c | (a,c) <- sample_all0 (2^m'-1, 3) ]
    setcolor (Color_Gray 0)
    sequence_ [ label a | a <- sample_all0 (2^m'-1) ]
  where
    sc = 5.0 :: Double
    labelfont = Font TimesRoman 0.8
    dotradius = 0.1 :: Double
    linewidth = 0.04 :: Double
    black = Color_Gray 0

    m' = (m oracle)
    n' = (n oracle)
    nn = fromIntegral n'
    ofun c (a, b, r) = do    
      let a_reg = qureg_of_qulist_te a
      let b_reg = qureg_of_qulist_te b
      (oraclefun oracle) c (a_reg, b_reg, r)
      return (a, b, r)
    
    simulate :: (Int, Int) -> (Int, Bool)
    simulate (c, a) = (b1, r1) where
      
      -- convert inputs to boollisttors
      a_in = boollist_of_int_bh m' a
      b_in = take m' $ repeat False
      r_in = False
    
      (a_out, b_out, r_out) = run_classical_generic (decompose_generic gb (ofun c)) (a_in, b_in, r_in)
      
      -- convert outputs to integers
      a1 = int_of_boollist_unsigned_bh a_out
      b1 = int_of_boollist_unsigned_bh b_out
      r1 = r_out
      
    width = 2.0^(n'+1) 
    height = (2.0*(nn)+4) * 2.0  + 2.0^n' 
    
    -- coord: map a node id to a pair of coordinates
    coord_simple :: Int -> (Double, Double)
    coord_simple a = (x,y) where
      t = (a .&. (2^(n'+1)) /= 0)  -- tree bit
      a' = a .&. (2^(n'+1)-1)      -- node address
      h = hibit a'                 -- logical height in subtree
      w = a' .&. (2^(h-1)-1)       -- logical position in row
      hh = fromIntegral h
      ww = fromIntegral w
      h1 = 1 + 2 * hh    -- physical height in subtree
      y = if t then h1 else height - h1
      x = if h == 0 then 0.5 * width else (1+2*ww)  * 2^(n'+1-h)
    
    -- coord_orthodox: same as coord, but use the layout of the orthodox oracle.
    coord_orthodox :: Int -> (Double, Double)
    coord_orthodox a | a >= 2^(n'+1) = (width - x,y) where
      (x,y) = coord_simple (2^(n'+2)+2^(n'+1)-1-a)
    coord_orthodox a = coord_simple a -- for the upper subtree, no difference
    
    coord :: Int -> (Double, Double)
    coord = if node_style then coord_orthodox else coord_simple
    
    color :: Int -> Color
    color 0 = Color_RGB 1 0 0
    color 1 = Color_RGB 0 1 0
    color 2 = Color_RGB 0 0 1
    color 3 = Color_RGB 1 1 0
    color n = error ("render_oracle: unknown color: " ++ show n)

    output :: Int -> Int -> Draw ()
    output a c =
      case simulate (c, a) of
        (b, False) -> do
          comment (printf "%d ---%d---> %d" a c b)
          moveto x0 y0
          lineto x2 y2
          setcolor (color c)
          stroke
          where
            (x0,y0) = coord a
            (x1,y1) = coord b
            (x2,y2) = ((x0+x1)/2, (y0+y1)/2)
        (b, True) -> do
          comment (printf "%d ---%d---> None (%d)" a c b)

    label :: Int -> Draw ()
    label a = do
      render_dot x y
      textbox align_left labelfont black (x+0.1) y (x+1.9) y 0 (show a)
      where
        (x,y) = coord a
        
    render_dot :: X -> Y -> Draw ()
    render_dot x y = do
      arc x y dotradius 0 360
      fill black

-- ======================================================================
-- * Testing of specific circuit fragments

-- | Simulate 'parseNodeRoot' on all possible inputs for tree height /n/. 
simulate_parseNodeRoot :: Int -> IO()
simulate_parseNodeRoot n = mapM_ output (sample_all0 (4*nn-1, True, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer,Bool,Bool) -> IO()
    output (a, root, even) =
      let
        as = boollist_of_int_bh (n+2) a
        (as',root',even') = run_classical_generic (runfun n) (as, root, even)

        runfun :: Int -> (Qulist,Qubit,Qubit) -> Circ (Qulist,Qubit,Qubit)
        runfun n (as, root, even) = do
          parseNodeRoot (qureg_of_qulist_te as, root, even, n)
          return (as, root, even)
        a' = int_of_boollist_unsigned_bh as' :: Integer
        d_root = root `bool_xor` root'
        d_even = even `bool_xor` even'
      in do
        printf "(a=%d, root=%s, even=%s) -> (a=%d, root=%s, even=%s)\n" a (show root) (show even) a' (show root') (show even')
        if (a /= a' || d_root /= d_even) then
          error "Test failed (1)"
        else if (d_root /= ((a .&. (2*nn-1)) <= 1)) then
          error "Test failed (2)"
        else
          return ()

-- | Simulate 'parseNodeEven' on all possible inputs for tree height /n/. 
simulate_parseNodeEven :: Int -> IO()
simulate_parseNodeEven n = mapM_ output (sample_all0 (4*nn-1, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer,Bool) -> IO()
    output (a, even) =
      let
        as = boollist_of_int_bh (n+2) a
        (as',even') = run_classical_generic (runfun n) (as, even)

        runfun :: Int -> (Qulist,Qubit) -> Circ (Qulist,Qubit)
        runfun n (as, even) = do
          parseNodeEven (qureg_of_qulist_te as, even, n)
          return (as, even)
        a' = int_of_boollist_unsigned_bh as' :: Integer
        d_even = even `bool_xor` even'
      in do
        printf "(a=%d, even=%s) -> (a=%d, even=%s)\n" a (show even) a' (show even')
        if (a /= a') then
          error "Test failed (3)"
        else if ((a .&. (2*nn-1)) <= 1) then
          if (d_even) then
            error "Test failed (4)"
          else
            return ()
        else if (d_even /= not (Prelude.even (hibit (a .&. (2*nn-1))))) then
          error "Test failed (5)"
        else
          return ()

-- | Simulate 'testIsParent' on all possible inputs for tree height /n/. 
simulate_testIsParent :: Int -> IO()
simulate_testIsParent n = mapM_ output (sample_all0 (1, True, True, True, 3, 1, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer, Bool, Bool, Bool, Integer, Int, Bool) -> IO()
    output (a, root, even, isparent, color, really, ismatch) =
      let
        as = boollist_of_int_bh 1 a
        cs = boollist_of_int_bh 2 color
        (as', root', even', isparent', ismatch') = run_classical_generic (runfun n cs really) (as, root, even, isparent, ismatch)

        runfun :: Int -> Boollist -> Int -> (Qulist,Qubit,Qubit,Qubit,Qubit) -> Circ (Qulist,Qubit,Qubit,Qubit,Qubit)
        runfun n cs rs (as, root, even, isparent, ismatch) = do
          testIsParent (qureg_of_qulist_te as, root, even, isparent, boolreg_of_boollist_te cs, n, really, ismatch)
          return (as, root, even, isparent, ismatch)
        
        a' = int_of_boollist_unsigned_bh as' :: Integer
        d_root = root `bool_xor` root'
        d_even = even `bool_xor` even'
        d_isparent = isparent `bool_xor` isparent'
        d_ismatch = ismatch `bool_xor` ismatch'
      in do
        printf "(a=%d, root=%s, even=%s, isparent=%s, color=%d, really=%d, ismatch=%s) -> (a=%d, root=%s, even=%s, isparent=%s, ismatch=%s)\n" a (show root) (show even) (show isparent) color really (show ismatch) a' (show root') (show even') (show isparent') (show ismatch')
        if (a /= a' || root /= root' || even /= even') then
          error "Test failed (6)"
        else if (root == True && even == True) then
          if d_isparent == False then
            return ()
          else
            error "Test failed (7)"
        else if really == 1 && ismatch == False then
          if d_isparent /= (color == (a .&. 1) .|. (if even then 2 else 0)) then
            error "Test failed (8)"
          else if d_ismatch /= (d_isparent && even) then
            error "Test failed (9)"
          else
            return ()
        else -- really == 0 -- we don't write more test cases because the algorithm is so convoluted.
          return ()

-- | Simulate 'testIsChild' on all possible inputs for tree height /n/. 
simulate_testIsChild :: Int -> IO()
simulate_testIsChild n = mapM_ output (sample_all0 (True, True, True, 3))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Bool, Bool, Bool, Integer) -> IO()
    output (even, ischild, direction, color) =
      let
        cs = boollist_of_int_bh 2 color
        (even', ischild', direction') = run_classical_generic (runfun cs n) (even, ischild, direction)

        runfun :: Boollist -> Int -> (Qubit,Qubit,Qubit) -> Circ (Qubit,Qubit,Qubit)
        runfun cs n (even, ischild, direction) = do
          testIsChild (even, ischild, direction, boolreg_of_boollist_te cs, n)
          return (even, ischild, direction)
        d_ischild = ischild `bool_xor` ischild'
        d_direction = direction `bool_xor` direction'
      in do
        printf "(even=%s, ischild=%s, direction=%s, color=%d) -> (even=%s, ischild=%s, direction=%s)\n" (show even) (show ischild) (show direction) color (show even') (show ischild') (show direction')
        if (even /= even' || d_direction == (Prelude.even color)) then
          error "Test failed (10)"
        else if even && (d_ischild /= (color <= 1)) then
          error "Test failed (11)"
        else if not even && (d_ischild /= (color >= 2)) then
          error "Test failed (12)"
        else
          return ()

-- | Simulate 'setParent' on all possible inputs for tree height /n/. 
simulate_setParent :: Int -> IO()
simulate_setParent n = mapM_ output (sample_all0 (4*nn-1, 4*nn-1, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer,Integer,Bool) -> IO()
    output (a,b,isparent) =
      let
        as = boollist_of_int_bh (n+2) a
        bs = boollist_of_int_bh (n+2) b
        (as',bs',isparent') = run_classical_generic (runfun n) (as, bs, isparent)

        runfun :: Int -> (Qulist,Qulist,Qubit) -> Circ (Qulist,Qulist,Qubit)
        runfun n (as, bs, isparent) = do
          setParent (qureg_of_qulist_te as, qureg_of_qulist_te bs, isparent, n)
          return (as, bs, isparent)
        a' = int_of_boollist_unsigned_bh as' :: Integer
        b' = int_of_boollist_unsigned_bh bs' :: Integer
        db = b `xor` b'
      in do
        printf "(a=%d, b=%d) -> (a=%d, b=%d) (db=%d) isparent=%s\n" a b a' b' db (show isparent)
        if (a /= a' || isparent /= isparent') then
          error "Test failed (13)"
        else if (isparent == False) then
           if (b /= b') then
             error "Test failed (14)"
           else
             return ()
        else if db /= ((a `div` 2) .&. (nn-1)) .|. (a .&. (2*nn)) then
          error "Test failed (15)"
        else
          return ()

-- | Simulate 'setChild' on all possible inputs for tree height /n/. 
simulate_setChild :: Int -> IO()
simulate_setChild n = mapM_ output (sample_all0 (4*nn-1, 4*nn-1, nn-1, nn-1, True, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer,Integer,Integer,Integer,Bool,Bool) -> IO()
    output (a,b,f,g,ischild,direction) =
      let
        as = boollist_of_int_bh (n+2) a
        bs = boollist_of_int_bh (n+2) b
        fs = boollist_of_int_bh n f
        gs = boollist_of_int_bh n g
        (as',bs',ischild',direction') = run_classical_generic (runfun n fs gs) (as, bs, ischild, direction)

        runfun :: Int -> Boollist -> Boollist -> (Qulist,Qulist,Qubit,Qubit) -> Circ (Qulist,Qulist,Qubit,Qubit)
        runfun n f g (as, bs, ischild, direction) = do
          setChild (qureg_of_qulist_te as, qureg_of_qulist_te bs, ischild, direction, boolreg_of_boollist_te f, boolreg_of_boollist_te g, n)
          return (as, bs, ischild, direction)
        a' = int_of_boollist_unsigned_bh as' :: Integer
        b' = int_of_boollist_unsigned_bh bs' :: Integer
        db = b `xor` b'
      in do
        printf "(a=%d, b=%d, f=%d, g=%d) -> (a=%d, b=%d) (db=%d) ischild=%s direction=%s\n" a b f g a' b' db (show ischild) (show direction)
        if (a /= a' || ischild /= ischild' || direction /= direction') then
          error "Test failed (16)"
        else if (ischild == False) then
           if (b /= b') then
             error "Test failed (17)"
           else
             return ()
        else if a .&. nn /= 0 then
          if direction == False && db /= (a `xor` f `xor` 2*nn) .|. nn then
            error "Test failed (18)"
          else if direction == True && a .&. (2*nn) /= 0 && db /= ((a - g) .&. (2*nn-1)) .|. nn then
            error "Test failed (19)"
          else if direction == True && a .&. (2*nn) == 0 && db /= (((a + g) .&. (2*nn-1)) .|. (2*nn) .|. nn) then
            error "Test failed (20)"
          else
            return ()
        else
          if db /= ((2*a) .&. (2*nn-1)) .|. (a .&. (2*nn)) .|. (if direction then 1 else 0) then
            error "Test failed (21)"
          else
            return ()

-- | Simulate 'setChildInTree' on all possible inputs for tree height /n/. 
simulate_setChildInTree :: Int -> IO()
simulate_setChildInTree n = mapM_ output (sample_all0 (4*nn-1, 4*nn-1, True, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer,Integer,Bool,Bool) -> IO()
    output (a,b,childctrl,direction) =
      let
        as = boollist_of_int_bh (n+2) a
        bs = boollist_of_int_bh (n+2) b
        (as',bs',childctrl',direction') = run_classical_generic (runfun n) (as, bs, childctrl, direction)

        runfun :: Int -> (Qulist,Qulist,Qubit,Qubit) -> Circ (Qulist,Qulist,Qubit,Qubit)
        runfun n (as, bs, childctrl, direction) = do
          setChildInTree (qureg_of_qulist_te as, qureg_of_qulist_te bs, childctrl, direction, n)
          return (as, bs, childctrl, direction)
        a' = int_of_boollist_unsigned_bh as' :: Integer
        b' = int_of_boollist_unsigned_bh bs' :: Integer
        db = b `xor` b'
      in do
        printf "(a=%d, b=%d) -> (a=%d, b=%d) (db=%d) childctrl=%s direction=%s\n" a b a' b' db (show childctrl) (show direction)
        if (a /= a' || childctrl /= childctrl' || direction /= direction') then
          error "Test failed (22)"
        else if (childctrl == False) then
           if (b /= b') then
             error "Test failed (23)"
           else
             return ()
        else if db /= ((2*a) .&. (2*nn-1)) .|. (a .&. (2*nn)) .|. (if direction then 1 else 0) then
          error "Test failed (24)"
        else
          return ()

-- | Simulate 'setWeld' on all possible inputs for tree height /n/. 
simulate_setWeld :: Int -> IO()
simulate_setWeld n = mapM_ output (sample_all0 (4*nn-1, 4*nn-1, nn-1, nn-1, True, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer,Integer,Integer,Integer,Bool,Bool) -> IO()
    output (a,b,f,g,childctrl,direction) =
      let
        as = boollist_of_int_bh (n+2) a
        bs = boollist_of_int_bh (n+2) b
        fs = boollist_of_int_bh n f
        gs = boollist_of_int_bh n g
        (as',bs',childctrl',direction') = run_classical_generic (runfun n fs gs) (as, bs, childctrl, direction)

        runfun :: Int -> Boollist -> Boollist -> (Qulist,Qulist,Qubit,Qubit) -> Circ (Qulist,Qulist,Qubit,Qubit)
        runfun n f g (as, bs, childctrl, direction) = do
          setWeld (qureg_of_qulist_te as, qureg_of_qulist_te bs, childctrl, direction, boolreg_of_boollist_te f, boolreg_of_boollist_te g, n)
          return (as, bs, childctrl, direction)
        a' = int_of_boollist_unsigned_bh as' :: Integer
        b' = int_of_boollist_unsigned_bh bs' :: Integer
        db = b `xor` b'
      in do
        printf "(a=%d, b=%d, f=%d, g=%d) -> (a=%d, b=%d) (db=%d) childctrl=%s direction=%s\n" a b f g a' b' db (show childctrl) (show direction)
        if (a /= a' || childctrl /= childctrl' || direction /= direction') then
          error "Test failed (25)"
        else if (childctrl == False) then
           if (b /= b') then
             error "Test failed (26)"
           else
             return ()
        else if direction == False && db /= (a `xor` f `xor` 2*nn) .|. nn then
          error "Test failed (27)"
        else if direction == True && a .&. (2*nn) /= 0 && db /= ((a - g) .&. (2*nn-1)) .|. nn then
          error "Test failed (28)"
        else if direction == True && a .&. (2*nn) == 0 && db /= (((a + g) .&. (2*nn-1)) .|. (2*nn) .|. nn) then
          error "Test failed (29)"
        else
          return ()

-- | Simulate 'doWeld1' on all possible inputs for tree height /n/. 
simulate_doWeld1 :: Int -> IO()
simulate_doWeld1 n = mapM_ output (sample_all0 (4*nn-1, 4*nn-1, nn-1, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer, Integer, Integer, Bool) -> IO()
    output (a,b,c,control) =    
      let
        as = boollist_of_int_bh (n+2) a
        bs = boollist_of_int_bh (n+2) b
        cs = boollist_of_int_bh n c
        (control', bs', as') = run_classical_generic (runfun n cs) (control, bs, as)

        runfun :: Int -> Boollist -> (Qubit, Qulist, Qulist) -> Circ (Qubit, Qulist, Qulist)
        runfun n c (control, b, a) = do
          doWeld1 (qureg_of_qulist_te a, qureg_of_qulist_te b, control, boolreg_of_boollist_te c, n)
          return (control, b, a)
        a' = int_of_boollist_unsigned_bh as' :: Integer
        b' = int_of_boollist_unsigned_bh bs' :: Integer
      in do
        printf "(%d, %d, %d) -> (%d, %d) %s %s\n" a b c a' b' (show control) (show control')
        if (control && a .&. (2*nn) /= 0 && a' == a && b' == (((a-c) .&. (nn-1)) `xor` b) && control' == control)
           || (control && a .&. (2*nn) == 0 && a' == a && b' == (((a+c) .&. (nn-1)) `xor` b) && control' == control)
           || (not control && a' == a && b' == b && control' == control) then
          return ()  -- assertion succeeds
          else
          error "Test failed (30)"

-- | Simulate 'doWeld0' on all possible inputs for tree height /n/. 
simulate_doWeld0 :: Int -> IO()
simulate_doWeld0 n = mapM_ output (sample_all0 (2*nn-1, 2*nn-1, nn-1, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer, Integer, Integer, Bool) -> IO()
    output (a,b,c,control) =    
      let
        as = boollist_of_int_bh (n+1) a
        bs = boollist_of_int_bh (n+1) b
        cs = boollist_of_int_bh n c
        (control', bs', as') = run_classical_generic (runfun n cs) (control, bs, as)

        runfun :: Int -> Boollist -> (Qubit, Qulist, Qulist) -> Circ (Qubit, Qulist, Qulist)
        runfun n c (control, b, a) = do
          doWeld0 (qureg_of_qulist_te a, qureg_of_qulist_te b, control, boolreg_of_boollist_te c, n)
          return (control, b, a)
        a' = int_of_boollist_unsigned_bh as' :: Integer
        b' = int_of_boollist_unsigned_bh bs' :: Integer
      in do
        printf "(%d, %d, %d) -> (%d, %d) %s %s\n" a b c a' b' (show control) (show control')
        if (control && a' == a && b' == (((a `xor` c) .&. (nn-1)) `xor` b) && control' == control)
           || (not control && a' == a && b' == b && control' == control) then
          return ()  -- assertion succeeds
          else
          error "Test failed (31)"

-- | Simulate 'cAddNum' (including 'cAddNumClear') on all possible inputs for tree height /n/. 
simulate_cAddNum :: Int -> IO()
simulate_cAddNum n = mapM_ output (sample_all0 (nn-1, nn-1, nn-1, True))
  where
    nn = 2^(toInteger n) :: Integer
    output :: (Integer, Integer, Integer, Bool) -> IO()
    output (a,b,c,control) =    
      let
        as = boollist_of_int_bh n a
        bs = boollist_of_int_bh n b
        cs = boollist_of_int_bh n c
        (control', bs', as') = run_classical_generic (runfun n cs) (control, bs, as)

        runfun :: Int -> Boollist -> (Qubit, Qulist, Qulist) -> Circ (Qubit, Qulist, Qulist)
        runfun n c (control, b, a) = do
          cAddNum (control, qureg_of_qulist_te b, qureg_of_qulist_te a, boolreg_of_boollist_te c, n)
          return (control, b, a)
        a' = int_of_boollist_unsigned_bh as'
        b' = int_of_boollist_unsigned_bh bs'
      in do
        printf "(%d, %d, %d) -> (%d, %d) %s %s\n" a b c a' b' (show control) (show control')
        if (control && a' == a && b' == (((a+c) `mod` (2^n)) `xor` b) && control' == control)
           || (not control && a' == a && b' == b && control' == control) then
          return ()  -- assertion succeeds
          else
          error "Test failed (32)"

-- | Simulate 'cSubNum' (including 'cSubNumClear') on all possible inputs for tree height /n/. 
simulate_cSubNum :: Int -> IO()
simulate_cSubNum n = mapM_ output (sample_all0 (nn-1, nn-1, nn-1, True))
  where
    nn = 2^(toInteger n) :: Integer -- can be quite large!
    output :: (Integer, Integer, Integer, Bool) -> IO()
    output (a,b,c,control) =    
      let
        as = boollist_of_int_bh n a
        bs = boollist_of_int_bh n b
        cs = boollist_of_int_bh n c
        (control', bs', as') = run_classical_generic (runfun n cs) (control, bs, as)

        runfun :: Int -> Boollist -> (Qubit, Qulist, Qulist) -> Circ (Qubit, Qulist, Qulist)
        runfun n c (control, b, a) = do
          cSubNum (control, qureg_of_qulist_te b, qureg_of_qulist_te a, boolreg_of_boollist_te c, n)
          return (control, b, a)
        a' = int_of_boollist_unsigned_bh as'
        b' = int_of_boollist_unsigned_bh bs'
      in do
        printf "(%d, %d, %d) -> (%d, %d) %s %s\n" a b c a' b' (show control) (show control')
        if (control && a' == a && b' == (((a-c) `mod` nn) `xor` b) && control' == control)
           || (not control && a' == a && b' == b && control' == control) then
          return ()  -- assertion succeeds
          else
          error "Test failed (33)"

-- ======================================================================
-- * Auxiliary functions

-- | Return the smallest number of bits required to hold the given integer.
hibit :: Integral a => Integral b => a -> b
hibit n =
  if n <= 0 then 
    0 
  else
    1 + hibit (n `div` 2)

-- ======================================================================
-- * Main functions

-- | Run simulations of 'parseNodeRoot', 'parseNodeEven',
-- 'testIsParent', 'testIsChild', 'setParent', 'setChild',
-- 'setChildInTree', 'setWeld', 'doWeld0', 'doWeld1', 'cAddNum', and
-- 'cSubNum' for tree height /n/.
main_all :: Int -> IO()
main_all n = do
  simulate_parseNodeRoot n
  simulate_parseNodeEven n
  simulate_testIsParent n
  simulate_testIsChild n
  simulate_setParent n
  simulate_setChild n
  simulate_setChildInTree n
  simulate_setWeld n
  simulate_doWeld0 n
  simulate_doWeld1 n
  simulate_cAddNum n
  simulate_cSubNum n
