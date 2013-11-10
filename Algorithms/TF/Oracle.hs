-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleContexts #-}

-- | This module provides implementations of an oracle for the
-- Triangle Finding Algorithm. 
--
-- This oracle injects the graph /G/ into the space 
-- {0, 1, . . . , 2/l/ − 1} of /l/-bit integers, and each oracle 
-- call requires the extensive use of modular arithmetic.
--
-- The circuits produced by running this \"orthodox\" oracle are 
-- very big. We therefore also provide a \"blackbox\" oracle, 
-- which is simply a placeholder for an actual oracle call, 
-- to replace the orthodox oracle when running subroutines and 
-- for resource estimation.  The oracle circuit is the same every 
-- time it is used, so for resource estimation purposes, it only 
-- needs to be generated once, rather than inlined at every use site.

module Algorithms.TF.Oracle where

import Quipper

import Algorithms.TF.Definitions

import Libraries.Auxiliary

-- ======================================================================

-- * Orthodox oracle

-- | Algorithm O-1. The two 'QNode' inputs /u/ and
-- /v/ are assumed to be of equal length.
o1_ORACLE :: Int -> QNode -> QNode -> Qubit -> Circ (QNode,QNode,Qubit)
o1_ORACLE l = box "o1" $ \u v edge -> do
  comment_with_label "ENTER: o1_ORACLE" (u,v,edge) ("u","v","edge")
  let n = length u
      hn = 2^(n-1)

  ((u,v),e) <- with_computed_fun (u,v)
    (o1_ORACLE_aux l hn)
    (\((u,v),(uint,vint,u17,v17,u3,v3),(uF,vF,uH,vH,t_uv,t_uHvH,t_u3v3)) -> do
      edge <- qnot edge `controlled` (t_uv .==. 0 .&&. uF .==. 1 .&&. vF .==. 1)
      edge <- qnot edge `controlled` (t_uv .==. 0 .&&. uF .==. 1 .&&. vF .==. 0 .&&. t_u3v3 .==. 1)
      edge <- qnot edge `controlled` (t_uv .==. 0 .&&. uF .==. 0 .&&. vF .==. 1 .&&. t_u3v3 .==. 1)
      edge <- qnot edge `controlled` (t_uv .==. 0 .&&. uF .==. 0 .&&. vF .==. 0 .&&. t_u3v3 .==. 0 .&&. t_uHvH .==. 0)
      return (((u,v),(uint,vint,u17,v17,u3,v3),(uF,vF,uH,vH,t_uv,t_uHvH,t_u3v3)),edge))

  comment_with_label "EXIT: o1_ORACLE" (u,v,edge) ("u","v","edge")
  return (u,v,edge)

-- | Compute the various auxiliary data for 'o1_ORACLE'.
o1_ORACLE_aux :: Int -> Int -> (QNode, QNode) -> Circ ((QNode, QNode), (QIntTF, QIntTF, QIntTF, QIntTF, QIntTF, QIntTF), (Qubit, Qubit, Qubit, Qubit, Qubit, Qubit, Qubit))
o1_ORACLE_aux l hn = box "o1_aux" $ \(u,v) -> do
      comment_with_label "ENTER: o1_ORACLE_aux" (u,v) ("u","v")
      (u,uint) <- o2_ConvertNode l u hn
      (v,vint) <- o2_ConvertNode l v hn
      (uint,vint,t_uv) <- o3_TestEqual uint vint
      {- Since we don’t have “quantum control”, we can’t say “if t == True… return” here;
         instead we just add a “control on t_uv == False” to the later flips of ‘edge’. -}

      (uint,u17) <- o4_POW17 uint
      (uint,u17,uF) <- o3_TestEqual uint u17
      (vint,v17) <- o4_POW17 vint
      (vint,v17,vF) <- o3_TestEqual vint v17

      let uint_bits = qulist_of_qinttf_lh uint
      let vint_bits = qulist_of_qinttf_lh vint
      uH <- qinit False
      uH <- qnot uH `controlled` (uint_bits !! (l-1))
      vH <- qinit False
      vH <- qnot vH `controlled` (vint_bits !! (l-1))
--    Would like to say ”t_uHvH <- qd_testequal uH vH t_uHvH”, if testequal were generic.
      t_uHvH <- qinit True
      t_uHvH <- qnot t_uHvH `controlled` uH
      t_uHvH <- qnot t_uHvH `controlled` vH

      (u17,u3) <- o5_MOD3 u17
      (v17,v3) <- o5_MOD3 v17
      (u3,v3,t_u3v3) <- o3_TestEqual u3 v3
      
      comment_with_label "EXIT: o1_ORACLE_aux" ((u,v),(uint,vint,u17,v17,u3,v3),(uF,vF,uH,vH,t_uv,t_uHvH,t_u3v3)) (("u","v"),("uint","vint","u17","v17","u3","v3"),("uF","vF","uH","vH","t_uv","t_uHvH","t_u3v3"))
      return ((u,v),(uint,vint,u17,v17,u3,v3),(uF,vF,uH,vH,t_uv,t_uHvH,t_u3v3))

-- | Algorithm O-2. Convert a 'QNode' into a freshly assigned 'QIntTF',
o2_ConvertNode :: Int -> QNode -> Int -> Circ (QNode,QIntTF)
o2_ConvertNode l u hn = ($ u) $ box "o2" $ \u -> do
  comment_with_label "ENTER: o2_ConvertNode" u "u"
  let n = if (length u < l) then (length u) else (error ("ConvertNode: requires n < l.  n = " ++ (show (length u)) ++ ", l = " ++ (show l) ++ "."))

  (u, uint) <- with_computed_fun u
    (\u -> do
      (u,w_low) <- qc_copy_fun u
      w_high <- qinit (replicate (l-n) False)
      return (u,qinttf_of_qulist_lh (w_low ++ w_high)))

    (\(u,w) -> do
      (w,uint) <- o6_SUB w hn
      return ((u,w),uint))
  comment_with_label "EXIT: o2_ConvertNode" (u, uint) ("u", "uint")
  return (u, uint)

-- | Algorithm O-3. Compare if two QIntTF’s are equal;
-- return the result in a fresh Qubit. 
-- 
-- This function is in general iffy: 00…00 and 11…11 do /not/ test as equal, as they should.
-- However, that case does not arise in the oracle: on the one hand, both 00…00 and 11…11
-- are literal fixed points of 'o4_POW17', and on the other, 'o5_MOD3' never outputs 00. 
o3_TestEqual :: QIntTF -> QIntTF-> Circ (QIntTF,QIntTF,Qubit)
o3_TestEqual = box "o3" $ \x y -> do
  comment_with_label "ENTER: o3_TestEqual" (x,y) ("x", "y")
  let x_bits = qulist_of_qinttf_lh x
  let y_bits = qulist_of_qinttf_lh y
  y_bits <- mapM (\(p,q) -> qnot q `controlled` p) (zip x_bits y_bits)
  t <- qinit False
  t <- qnot t `controlled` [ q .==. 0 | q <- y_bits ]
  y_bits <- mapM (\(p,q) -> qnot q `controlled` p) (zip x_bits y_bits)
  let x = qinttf_of_qulist_lh x_bits
  let y = qinttf_of_qulist_lh y_bits
  comment_with_label "EXIT: o3_TestEqual" (x, y, t) ("x", "y", "t")
  return (x, y, t)

-- | Algorithm O-4. Compute 17th power of a 31-bit 'QIntTF' /x/, into a
-- freshly 31-bit /QIntTF/. 
o4_POW17 :: QIntTF -> Circ (QIntTF,QIntTF)
o4_POW17 = box "o4" $ \x -> do
  comment_with_label "ENTER: o4_POW17" x "x"
  (x, x17) <- with_computed_fun x
    (\x -> do
      (x,x2) <- square x
      (x2,x4) <- square x2
      (x4,x8) <- square x4      
      (x8,x16) <- square x8
      return (x,x2,x4,x8,x16))
    
    (\(x,x2,x4,x8,x16) -> do
      (x,x16,x17) <- o8_MUL x x16
      return ((x,x2,x4,x8,x16),x17))
  comment_with_label "EXIT: o4_POW17" (x, x17) ("x", "x17")
  return (x, x17)

{- Alternative coding style:
o4_POW17 x = do
  (x,x17) <- with_computed_fun square x (\(x,x2) -> do
    (x2,(x,x17)) <- with_computed_fun square x2 (\(x2,x4) -> do
      (x4,(x,x17)) <- with_computed_fun square x4 (\(x4,x8) -> do
        (x8,(x,x17)) <- with_computed_fun square x8 (\(x8,x16) -> do
          (x,x16,x17) <- o8_MUL x x16
          return ((x8,x16),(x,x17)))
        return ((x4,x8),(x,x17)))
      return ((x2,x4),(x,x17)))
    return ((x,x2),x17))
  return (x,x17)
-}

-- | Map a QIntTF /x/ to (/x/,/x/^2).
-- 
-- A subroutine factored out of @'o4_POW17'@.
square :: QIntTF -> Circ (QIntTF,QIntTF)
square x = do
--           comment_with_label "ENTER: square" x "x"
           (x, x2) <- with_computed_fun x qc_copy_fun 
             (\(x,x') -> do
               (x,x',x2) <- o8_MUL x x'
               return ((x,x'),x2))
--           comment_with_label "EXIT: square" (x, x2) ("x", "x2")
           return (x, x2)

-- | Algorithm O-5. Compute residue modulo 3 of the lower-order bits of a
-- 'QIntTF', into a fresh 2-bit 'QIntTF'.
-- 
-- This algorithm is size-limited — works for up to 31-bit integers, but not beyond.
-- 
-- This also currently is mismatched with our specification of QIntTF, since it 
-- produces output in the range 1–3, rather than 0–2.  However, output of this 
-- algorithm is only used via '03_TestEqual', so this is not a problem in practice. 
o5_MOD3 :: QIntTF -> Circ (QIntTF,QIntTF)
o5_MOD3 = box "o5" $ \x -> do
  comment_with_label "ENTER: o5_MOD3" x "x"
  let x_bits = qulist_of_qinttf_lh x
  let l = length x_bits
      l' = if (l <= 31) then (l `div` 2)
                        else error "o5_MOD3: requires l <= 31"
  (x_bits, m_bits) <- with_computed_fun x_bits
    (\x_bits -> do
      s5 <- mmap qulist_of_qinttf_lh $ qinit (inttf 5 15)
    
      (x_bits,s5) <- loop_with_indexM l' (x_bits,s5) (\i (x_bits,s5) -> do
        s5 <- increment_little s5 `controlled` (x_bits !! (2*i))
        s5 <- if (2*i + 1 <= l - 2) -- in case l is even, skip this step on the last iteration. 
              then decrement_little s5 `controlled` (x_bits !! (2*i + 1))
              else return s5
        return (x_bits,s5))

      s3 <- mmap qulist_of_qinttf_lh $ qinit (inttf 3 3)

      (s5,s3) <- loop_with_indexM 2 (s5,s3) (\i (s5,s3) -> do
        s3 <- increment_little s3 `controlled` (s5 !! (2*i))
        s3 <- decrement_little s3 `controlled` (s5 !! (2*i + 1))
        return (s5,s3))
      s3 <- increment_little s3 `controlled` (s5 !! 4)
  
      let s3_high = last s3
          s2 = init s3
      s2 <- increment_little s2 `controlled` s3_high

      return (x_bits,s5,s3_high,s2))

    (\(x_bits,s5,s3_high,s2) -> do
      (s2,m_bits) <- qc_copy_fun s2
      return ((x_bits,s5,s3_high,s2), m_bits))
  let x = qinttf_of_qulist_lh x_bits
  let m = qinttf_of_qulist_lh m_bits
  comment_with_label "EXIT: o5_MOD3" (x, m) ("x", "m")
  return (x, m)

-- | Algorithm O-6. Subtract an integer parameter from a 'QIntTF'.  
-- Return the result as a second, freshly assigned 'QIntTF'.
o6_SUB :: QIntTF -> Int -> Circ (QIntTF,QIntTF)
o6_SUB x y = ($ x) $ box "o6" $ \x -> do
 comment_with_label "ENTER: o6_SUB" x "x"
 (x, d_out) <- with_computed_fun x
  (\x1 -> do
    let x = qulist_of_qinttf_lh x1
    let l = length x
    let y_bits = reverse (boollist_of_int_bh l y)  -- the little-endian binary rep of /y/
  
    d <- qinit (replicate l False) -- will be [the list of bits of] the eventual answer
    d1 <- qinit (replicate l False) -- will hold an intermediate version of the
            -- subtraction, not “corrected” modulo (2^l – 1).
    c1 <- qinit (replicate (l+1) False)

    (c1,d1,x) <- loop_with_indexM l (c1,d1,x) (\j (c1,d1,x) -> do
      let c1_j1 = c1 !! (j+1)
      let d1_j = d1 !! j
      c1_j1 <- if y_bits !! j 
              then return c1_j1
              else qnot c1_j1 `controlled` (x !! j)
      c1_j1 <- qnot c1_j1 `controlled` (x !! j) .&&. (c1 !! j)
      c1_j1 <- if  y_bits !! j 
              then return c1_j1
              else qnot c1_j1 `controlled` (c1!!j)
      d1_j <- qnot d1_j `controlled` (x !! j)
      d1_j <- if y_bits !! j 
             then return d1_j
             else qnot d1_j
      d1_j <- qnot d1_j `controlled` (c1 !! j)
      c1 <- return $ overwriteAt (j+1) c1_j1 c1
      d1 <- return $ overwriteAt j d1_j d1
      return (c1,d1,x))

    c2 <- qinit (replicate (l+1) False)
    c2_0 <- qnot (c2 !! 0) `controlled` (c1 !! l)
    c2 <- return $ overwriteAt 0 c2_0 c2
  
    (d,d1,c2) <- loop_with_indexM l (d,d1,c2) (\j (d,d1,c2) -> do
      let c2_j1 = c2 !! (j+1)
      let dj = d !! j
      c2_j1 <- qnot c2_j1 `controlled` (d1 !! j) .&&. (c2 !! j)
      dj <- qnot dj `controlled` (d1 !! j)
      dj <- qnot dj `controlled` (c2 !! j)
      c2 <- return $ overwriteAt (j+1) c2_j1 c2
      d <- return $ overwriteAt j dj d
      return (d,d1,c2))
  
    d_0 <- qnot (d !! 0) `controlled` (c2 !! l)
    d <- return $ overwriteAt 0 d_0 d
    return (x,d,d1,c1,c2))
  -- Having computed the difference /d/ along with much auxiliary data, we save a 
  -- copy of /d/ before undoing all the computation:
  (\(x,d,d1,c1,c2) -> do
     (d,d_out) <- qc_copy_fun d
     return ((x,d,d1,c1,c2),qinttf_of_qulist_lh d_out))
 comment_with_label "EXIT: o6_SUB" (x, d_out) ("x", "d_out")
 return (x, d_out)
  
-- | Algorithm O-7. Add two 'QIntTF's.  Return the result as a third, freshly assigned 'QIntTF'.
o7_ADD :: QIntTF -> QIntTF -> Circ (QIntTF,QIntTF,QIntTF)
o7_ADD = box "o7" $ \x y -> do 
  comment_with_label "ENTER: o7_ADD" (x, y) ("x", "y")
  let x_bits = qulist_of_qinttf_lh x
  let y_bits = qulist_of_qinttf_lh y
  let l = length x_bits

  ((x_bits,y_bits),s_out) <- with_computed_fun (x_bits,y_bits)
    (\(x_bits,y_bits) -> do
      s <- qinit (replicate l False) -- holds the eventual sum
      s1 <- qinit (replicate l False) -- holds the uncorrected sum
      c1 <- qinit (replicate (l+1) False) -- holds the carries

      (c1,s1,x_bits,y_bits) <- loop_with_indexM l (c1,s1,x_bits,y_bits) (\j (c1,s1,x_bits,y_bits) -> do
        let c1_j1 = c1 !! (j+1)
        let s1_j = s1 !! j
        c1_j1 <- qnot c1_j1 `controlled` (x_bits!!j) .&&. (y_bits!!j)
        c1_j1 <- qnot c1_j1 `controlled` (x_bits!!j) .&&. (c1!!j)
        c1_j1 <- qnot c1_j1 `controlled` (y_bits!!j) .&&. (c1!!j)
        s1_j <- qnot s1_j `controlled` (x_bits !! j)
        s1_j <- qnot s1_j `controlled` (y_bits !! j)
        s1_j <- qnot s1_j `controlled` (c1 !! j)
        c1 <- return $ overwriteAt (j+1) c1_j1 c1
        s1 <- return $ overwriteAt j s1_j s1
        return (c1,s1,x_bits,y_bits))

      c2 <- qinit (replicate (l+1) False)
      c2_0 <- qnot (c2 !! 0) `controlled` (c1 !! l)
      c2 <- return $ overwriteAt 0 c2_0 c2
  
      (s,s1,c2) <- loop_with_indexM l (s,s1,c2) (\j (s,s1,c2) -> do
        let c2_j1 = c2 !! (j+1)
        let sj = s !! j
        c2_j1 <- qnot c2_j1 `controlled` (s1 !! j) .&&. (c2 !! j)
        sj <- qnot sj `controlled` (s1 !! j)
        sj <- qnot sj `controlled` (c2 !! j)
        c2 <- return $ overwriteAt (j+1) c2_j1 c2
        s <- return $ overwriteAt j sj s
        return (s,s1,c2))
  
      s_0 <- qnot (s !! 0) `controlled` (c2 !! l)
      s <- return $ overwriteAt 0 s_0 s
      
      return (x_bits,y_bits,s,s1,c1,c2))
    
    (\(x_bits,y_bits,s,s1,c1,c2) -> do
      (s,s_out) <- qc_copy_fun s
      return ((x_bits,y_bits,s,s1,c1,c2), s_out))
  let x = qinttf_of_qulist_lh x_bits
  let y = qinttf_of_qulist_lh y_bits
  let s = qinttf_of_qulist_lh s_out
  comment_with_label "EXIT: o7_ADD" (x, y, s) ("x", "y", "s")
  return (x, y, s)

-- | Controlled version of 'o7_ADD'. Returns either a copy of the first 
-- input (if controls are “off”) or the sum of the inputs 
-- (if controls are “on”).
--
-- We make this version explicitly, rather than just using 'controlled',
-- because the controls only need to be applied to a very few selected 
-- gates in the routine.
o7_ADD_controlled :: (ControlSource ctrl, Labelable ctrl String)
                  => ctrl -> QIntTF -> QIntTF -> Circ (QIntTF,QIntTF,QIntTF)
o7_ADD_controlled controls x y = do
  comment_with_label "ENTER: o7_ADD_controlled" (controls,x,y) ("ctrl","x","y")
  let x_bits = qulist_of_qinttf_lh x
  let y_bits = qulist_of_qinttf_lh y
  let l = length x_bits

  ((x_bits,y_bits),s_out) <- with_computed_fun (x_bits,y_bits)
    (\(x_bits,y_bits) -> do
      s <- qinit (replicate l False) -- holds the eventual sum
      s1 <- qinit (replicate l False) -- holds the uncorrected sum
      c1 <- qinit (replicate (l+1) False) -- holds the carries

      (c1,s1,x_bits,y_bits) <- loop_with_indexM l (c1,s1,x_bits,y_bits) (\j (c1,s1,x_bits,y_bits) -> do
        let c1_j1 = c1 !! (j+1)
        let s1_j = s1 !! j
        c1_j1 <- qnot c1_j1 `controlled` (x_bits!!j) .&&. (y_bits!!j)
        c1_j1 <- qnot c1_j1 `controlled` (x_bits!!j) .&&. (c1!!j)
        c1_j1 <- qnot c1_j1 `controlled` (y_bits!!j) .&&. (c1!!j)
        s1_j <- qnot s1_j `controlled` (x_bits !! j)
        s1_j <- qnot s1_j `controlled` (y_bits !! j)
        s1_j <- qnot s1_j `controlled` (c1 !! j)
        c1 <- return $ overwriteAt (j+1) c1_j1 c1
        s1 <- return $ overwriteAt j s1_j s1
        return (c1,s1,x_bits,y_bits))

      c2 <- qinit (replicate (l+1) False)
      c2_0 <- qnot (c2 !! 0) `controlled` (c1 !! l)
      c2 <- return $ overwriteAt 0 c2_0 c2
  
      (s,s1,c2) <- loop_with_indexM l (s,s1,c2) (\j (s,s1,c2) -> do
        let c2_j1 = c2 !! (j+1)
        let sj = s !! j
        c2_j1 <- qnot c2_j1 `controlled` (s1 !! j) .&&. (c2 !! j)
        sj <- qnot sj `controlled` (s1 !! j)
        sj <- qnot sj `controlled` (c2 !! j)
        c2 <- return $ overwriteAt (j+1) c2_j1 c2
        s <- return $ overwriteAt j sj s
        return (s,s1,c2))
  
      s_0 <- qnot (s !! 0) `controlled` (c2 !! l)
      s <- return $ overwriteAt 0 s_0 s
      
      return (x_bits,y_bits,s,s1,c1,c2))

    (\(x_bits,y_bits,s,s1,c1,c2) -> do
      -- Prepare a qubit holding the value of the controls,
      -- since we want to control also on their negation.
      -- /Can’t/ include this in “with_computed_fun”: controls can’t be bound
      -- as QData, and including it unbound yields rather interesting bug.
      temp_control <- qinit False
      temp_control <- qnot temp_control `controlled` controls
      s_out <- qinit (replicate l False)
      (x_bits,s_out) <- mapBinary 
                     (\q q' -> do
                       q' <- qnot q' `controlled` (q .&&. (temp_control .==. 0))
                       return (q,q')) 
                     x_bits s_out
      (s,s_out) <- mapBinary 
                     (\q q' -> do
                       q' <- qnot q' `controlled` (q .&&. (temp_control .==. 1))
                       return (q,q'))
                     s s_out
      temp_control <- qnot temp_control `controlled` controls
      qterm False temp_control
      return ((x_bits,y_bits,s,s1,c1,c2), s_out))
  let x = qinttf_of_qulist_lh x_bits
  let y = qinttf_of_qulist_lh y_bits
  let s = qinttf_of_qulist_lh s_out
  comment_with_label "EXIT: o7_ADD_controlled" (x,y,s) ("x","y","s")
  return (x, y, s)


-- | Algorithm O-8. Multiply two 'QIntTF's; return the 
-- result as a third, freshly assigned 'QIntTF'.
o8_MUL :: QIntTF -> QIntTF -> Circ (QIntTF,QIntTF,QIntTF)
o8_MUL = box "o8" $ \x y -> do
--  comment_with_label "ENTER: o8_MUL" (x,y) ("x","y")
  let x_bits = qulist_of_qinttf_lh x
  let l = length x_bits

  ((x,y),p) <- with_computed_fun (x,y)
    (\(x, y) -> do
      let x_bits = qulist_of_qinttf_lh x
      -- We will build up a register of partial products, each obtained from the previous
      -- by adding (2^i * y) if the ith bit of x is set. 
      -- For this, we make a copy of y, to be repeatedly doubled as we go.
      (y,tmp_y) <- qc_copy_fun y
      wrk0 <- qinit (inttf l 0)
      (tmp_y,wrks) <- loop_with_indexM l (tmp_y,[wrk0]) 
        (\k (tmp_y,(wrk_prev:wrks_older)) -> do
          (wrk_prev,tmp_y,wrk_new)
            <- o7_ADD_controlled (x_bits !! k) wrk_prev tmp_y
          tmp_y <- double_TF tmp_y
          return (tmp_y,(wrk_new:wrk_prev:wrks_older)))
      return ((qinttf_of_qulist_lh x_bits),y,tmp_y,wrks))

    (\(x,y,tmp_y,(wrks_head:wrks_rest)) -> do
      (wrks_head,p) <- qc_copy_fun wrks_head
      return ((x,y,tmp_y,(wrks_head:wrks_rest)), p))

--  comment_with_label "EXIT: o8_MUL" (x,y,p) ("x","y","p")
  return (x,y,p)

-- | Double a 'QIntTF' in place.
-- 
-- A subroutine factored out of 'o8_MUL'.
double_TF :: QIntTF -> Circ QIntTF
double_TF x = do
  comment_with_label "ENTER: double_TF" x "x"
  x <- case qulist_of_qinttf_lh x of
    [] -> return (qinttf_of_qulist_lh [])
    x_bits -> return (qinttf_of_qulist_lh ((last x_bits):(init x_bits)))
  comment_with_label "EXIT: double_TF" x "x"
  return x

-- ======================================================================

-- * Blackbox oracle

-- | A black-box oracle for testing. Produces a labelled black-box gate in
-- place of the actual oracle circuit.

placeholder_oracle :: QNode -> QNode -> Qubit -> Circ Qubit
placeholder_oracle node1 node2 outp_bit = do 
  comment_with_label "placeholder_oracle" (node1, node2, outp_bit) ("node1", "node2", "outp_bit")       
  extended_named_gate_at "OC" [outp_bit] (node1 ++ node2)
  return outp_bit


