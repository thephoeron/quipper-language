-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-} 

-- | This module implements the specialized quantum operations required in stages 1 and 4 of Hallgren’s algorithm.
--
-- The key operation for stage 1 is 'q_fN', implementing /f/[sub /N/], the quasi-periodic
-- function used in approximating the regulator.  This is the function /h/ of
-- [Jozsa 2003], Sec. 9, discretized with precision 1\//N/ and translated by a
-- specified jitter parameter.
--
-- The key functions for stage 4 are not yet implemented.  These essentially
-- consist of the functions /f/[sub /I/,/N/], analogues of /f/[sub /N/] operating
-- within the equivalence classes of possibly non-principal ideals /I/ (representing
-- other elements of the class group), as described in [Hallgren 2006, Section 5].

module Algorithms.CL.RegulatorQuantum where

import Quipper
import Quipper.Internal

import QuipperLib.Arith hiding (q_ext_euclid, q_add, q_mult, q_div_exact,
                               q_add_in_place, q_add_param_in_place, q_div,
                               q_mult_param, q_mod_unsigned, q_sub_in_place,
                               q_increment) 
import qualified QuipperLib.Arith as Arith
import QuipperLib.FPReal

import Algorithms.CL.Auxiliary
import Algorithms.CL.Types
import Algorithms.CL.RegulatorClassical

import Control.Monad (foldM)

-- ======================================================================
-- * Basic operations on ideals

-- | Send /I/ = \</k/,/l/,/a/,/b/> to /l/\//ka/ /I/ = \<1,/a/,/a/,/b/>.
--
-- On distances, send δ[sub /I/] to δ[sub /I/] - log (/l/\//ka/).

-- Implementation note: is it more efficient to multply/divide and then
-- take log, or take logs separately and then add/subtract?
q_normalize :: IdDistQ -> Circ (IdDistQ,IdDistQ)
q_normalize = box "q_normalize" $ \((Ideal bigD k l a b), dist) -> do
  let k_bits = qulist_of_qdint_bh k
      n = length k_bits
  k' <- qinit (intm n 1)
  (a,l') <- qc_copy_fun a
  (a,a') <- qc_copy_fun a
  (b,b') <- qc_copy_fun b
  ((k,l,a,dist), dist') <- with_computed_fun
    (k,l,a,dist)
    (\(k,l,a,dist) -> do
      (k,k_clreal) <- q_fromQDInt k
      (l,l_clreal) <- q_fromQDInt l
      (a,a_clreal) <- q_fromQDInt a
      (k_clreal,log_k) <- fprealq_log_with_shape dist k_clreal
      (l_clreal,log_l) <- fprealq_log_with_shape dist l_clreal
      (a_clreal,log_a) <- fprealq_log_with_shape dist a_clreal
      (log_k, dist) <- fprealq_sub_in_place log_k dist
      (log_l, dist) <- fprealq_add_in_place log_l dist
      (log_a, dist) <- fprealq_sub_in_place log_a dist 
      return (((k,l,a),(k_clreal,l_clreal,a_clreal),(log_k,log_l,log_a)), dist))
    (\(various, dist) -> do
      (dist,dist') <- qc_copy_fun dist
      return ((various,dist), dist'))
  return ((Ideal bigD k l a b, dist), (Ideal bigD k' l' a' b', dist'))

-- | Apply the function ρ to an 'IdealQ' together with a distance.  
-- See [Jozsa 2003], Sect 6.2, preceding Prop. 21; compare 'rho_d'.

-- Implementation note: not factored into q_rho plus action on distance,
-- since the two share a bit of computation (c_num).
q_rho_d :: IdDistQ -> Circ (IdDistQ,IdDistQ) 
q_rho_d = box "rho" $ \iid@(Ideal bigD m l a b, del) -> do
  rho_iid <- with_computed
    (do
      (_,_,b_sq) <- q_mult b b
      b_sq' <- q_sub_param_in_place (fromIntegral bigD) b_sq
      (_,c_num) <- q_abs b_sq'
      (_,c_denom) <- q_mult_param 4 a
      (_,_,c) <- q_div_exact c_num c_denom
      let a' = c
      (_,b_neg) <- q_negate b
      (_,_,b') <- q_tau bigD b_neg a'
      (_,_,m') <- q_mult m a
      (_,_,l') <- q_mult l a'
      (_,_,_,_,d) <- q_ext_euclid m' l'
      (_,_,m'') <- q_div_exact m' d
      (_,_,l'') <- q_div_exact l' d
      let ii' = Ideal bigD a' b' m'' l''
  
  -- By definition, del_change = log $ abs $ gamma_bar / 2 * gamma,
  -- where gamma = b/2a + (1/2*a)*(sqrt bigD).
  --
  -- A few lines of algebra gives: 
  -- del_change = log $ (b - (sqrt bigD))^2 / (abs $ b^2 - bigD)
  -- = log (b - (sqrt bigD))^2 - log (abs $ b^2 - bigD)
      (_,b_fp) <- fprealq_of_QDInt_with_shape del b
      b_fp <- fprealq_add_param_in_place (negate $ sqrt $ fromIntegral bigD) b_fp
      (_,_,b_fp_sq) <- q_mult b_fp b_fp
      (_,del_change_1) <- fprealq_log_with_shape del b_fp_sq
      (_,del_change_2) <- fprealq_log_with_shape del (fprealx 0 c_num)
      del' <- qc_copy del
      (_,del') <- fprealq_add_in_place del_change_1 del'
      (_,del') <- fprealq_sub_in_place del_change_2 del'
      return (ii', del'))
    qc_copy
  return (iid, rho_iid)

-- | Apply the function ρ[sup –1] to an 'IdealQ' together with a distance.  
-- See [Jozsa 2003], Sec 6.2, preceding Prop. 21, and Sec 6.4; compare 'rho_inv_d'.
q_rho_inv_d :: IdDistQ -> Circ (IdDistQ, IdDistQ)
q_rho_inv_d = box "rho_inv" $ \iid@(Ideal bigD m l a b, del) -> do
  rho_inv_iid <- with_computed
    (do
    --  b' = τ(Δ,-b,a):
      (_, b_neg) <- q_negate b
      (_, _, b') <- q_tau bigD b_neg a
    --  a'' = (Δ - b'^2) / (4*a):
      (_, b'_sq) <- q_square b'
      (_, a''_num) <- q_negate b'_sq
      a''_num <- q_add_param_in_place (fromIntegral bigD) a''_num
      (_, a''_denom) <- q_mult_param 4 a
      (_, _, a'') <- q_div_exact a''_num a''_denom
      (_, _, b'') <- q_tau bigD b' a''
    -- m''/l'' = m*a / l*a'', reduced to lowest terms:
      (_, _, m') <- q_mult m a
      (_, _, l') <- q_mult l a''
      (_,_,_,_, d) <- q_ext_euclid m' l'
      (_, _, m'') <- q_div_exact m' d
      (_, _, l'') <- q_div_exact l' d  
      let ii' = Ideal bigD a'' b'' m'' l''
  
  -- Compute del_change as in 'q_rho_d',
  -- but using coefficients from ii':
      (_,b_fp) <- fprealq_of_QDInt_with_shape del b''
      b_fp <- fprealq_add_param_in_place (negate $ sqrt $ fromIntegral bigD) b_fp
      (_,_,b_fp_sq) <- q_mult b_fp b_fp
      (_,del_change_1) <- fprealq_log_with_shape del b_fp_sq
      (_,_,b_sq) <- q_mult b'' b''
      b_sq' <- q_sub_param_in_place (fromIntegral bigD) b_sq
      (_,c_num) <- q_abs b_sq'
      (_,del_change_2) <- fprealq_log_with_shape del (fprealx 0 c_num)
      del' <- qc_copy del
      (_,del') <- fprealq_sub_in_place del_change_1 del'
      (_,del') <- fprealq_add_in_place del_change_2 del'
      return (ii', del'))
    qc_copy
  return (iid, rho_inv_iid)

-- | As 'q_rho_d', but for reduced ideals.

-- Implementation note: could be optimised a bit, since some of the algebra 
-- needed for ρ in the general case is redundant for reduced ideals.
q_rho_red_d :: IdRedDistQ -> Circ (IdRedDistQ,IdRedDistQ) 
q_rho_red_d (ii,del) = do
  ii <- q_forget_reduced ii
  ((ii,del), (ii',del')) <- q_rho_d (ii,del)
  ii <- q_assert_reduced ii
  ii' <- q_assert_reduced ii'
  return ((ii,del), (ii',del'))

-- | As 'q_rho_inv_d', but for reduced ideals.

-- Implementation note: could be optimised, like 'q_rho_red_d'.
q_rho_inv_red_d :: IdRedDistQ -> Circ (IdRedDistQ,IdRedDistQ) 
q_rho_inv_red_d (ii,del) = do
  ii <- q_forget_reduced ii
  ((ii,del), (ii',del')) <- q_rho_inv_d (ii,del)
  ii <- q_assert_reduced ii
  ii' <- q_assert_reduced ii'
  return ((ii,del), (ii',del'))

-- ======================================================================
-- * Products of ideals

-- | Compute the ordinary (not necessarily reduced) product of two reduced
-- fractional ideals.
-- 
-- This is /I/⋅/J/ of [Jozsa 2003], Sec 7.1, following the description
-- given in Prop. 34.
q_dot_prod :: IdealRedQ -> IdealRedQ -> Circ (IdealRedQ,IdealRedQ,IdealQ)
q_dot_prod = box "q_dot_prod" $ \(IdealRed bigD1 a1 b1) (IdealRed bigD2 a2 b2) -> do
  assertM (all_eq [bigD1,bigD2]) "Error: mismatched Δ’s in q_dot_prod."
  let bigD = bigD1
      n = qdint_length a1

  label (a1,b1,a2,b2) ("a1","b1","a2","b2")
  ((a1,a2,b1,b2),(k,l,a3,b3)) <- with_computed_fun (a1,a2,b1,b2)
    (\(a1,a2,b1,b2) -> do
      comment "q_dot_prod, step 1: (khat,uhat,vhat) <- ExtendedEuclid(a1,a2)"
      (a1,a2,khat,uhat,vhat) <- q_ext_euclid a1 a2
      label (khat,uhat,vhat) ("khat","uhat","vhat")
      comment "q_dot_prod, step 2: (k,u,v) <- ExtendedEuclid(khat,(b1+b2)/2)"
      (b1,b2,b1b2) <- q_add b1 b2
      b1b2 <- q_div2 b1b2
      label (b1b2) ("(b1 + b2)/2")
      (khat,b1b2,k,x,w) <- q_ext_euclid khat b1b2
      label (k,x,w) ("k","x","w")
      comment "q_dot_prod, step 3: a3 := a1a2/k^2.  [This should always be an integer.]"
      (a1,a2,a1a2) <- q_mult a1 a2
      label (a1a2) ("a1*a2")
      (k,k_sq) <- q_square k
      label (k_sq) ("k^2")
      (a1a2,k_sq,a3) <- q_div_exact a1a2 k_sq
      label (a1a2,k_sq,a3) ("a3")
      comment "q_dot_prod, step 4: t = (long formula, requiring many intermediate calculations)"
      (((a1,b1,a2,b2),(uhat,vhat,k,x,w)),t) <- with_computed_fun
        ((a1,b1,a2,b2),(uhat,vhat,k,x,w))

        (\((a1,b1,a2,b2),(uhat,vhat,k,x,w)) -> do
          comment "q_dot_prod, step 4, first summand: x * uhat * a1 * b2"
          (x,uhat,x_uhat) <- q_mult x uhat
          label x_uhat "x * uhat"
          (x_uhat,a1,x_uhat_a1) <- q_mult x_uhat a1
          label x_uhat_a1 "x * uhat * a1"
          (x_uhat_a1,b2,x_uhat_a1_b2) <- q_mult x_uhat_a1 b2
          label x_uhat_a1_b2 "x * uhat * a1 * b2"
          comment "q_dot_prod, step 4, second summand: x * vhat * a2 * b1"
          (x,vhat,x_vhat) <- q_mult x vhat
          label x_vhat "x * vhat"
          (x_vhat,a2,x_vhat_a2) <- q_mult x_vhat a2
          label x_vhat_a2 "x * vhat * a2"
          (x_vhat_a2,b1,x_vhat_a2_b1) <- q_mult x_vhat_a2 b1
          label x_vhat_a2_b1 "x * vhat * a2 * b1"
          comment "q_dot_prod, step 4, third summand: w * (b1 * b2 + Delta) / 2"
          (b1,b2,b1_b2) <- q_mult b1 b2
          label b1_b2 "b1 * b2" 
          b1_b2_D <- q_add_param_in_place (fromInteger $ toInteger bigD) b1_b2
          label b1_b2_D "b1 * b2 + Delta" 
          b1_b2_D_by2 <- q_div2 b1_b2_D
          label b1_b2_D_by2 "(b1 * b2 + Delta) / 2" 
          (w,b1_b2_D_by2,w_b1_b2_D_by2) <- q_mult w b1_b2_D_by2
          label b1_b2_D_by2 "w * (b1 * b2 + Delta) / 2" 
          comment "q_dot_prod, step 4, sum of all summands:"
          (x_uhat_a1_b2,x_vhat_a2_b1,s) <- q_add x_uhat_a1_b2 x_vhat_a2_b1
          (w_b1_b2_D_by2,s) <- q_add_in_place w_b1_b2_D_by2 s
          label s "big sum from step 4"
          return ((a1,b1,a2,b2),
                  (uhat,vhat,k,x,w),
                  (x_uhat,x_uhat_a1,x_uhat_a1_b2),
                  (x_vhat,x_vhat_a2,x_vhat_a2_b1),
                  (b1_b2_D_by2,w_b1_b2_D_by2),
                  s))

        (\(inputs, (uhat,vhat,k,x,w), subterm1, subterm2, subterm3, s) -> do
            comment "q_dot_prod, step 4, final division: t := (big sum) / k"
            (s,k,t) <- q_div s k
            label t "t"
            return ((inputs, (uhat,vhat,k,x,w), subterm1, subterm2, subterm3, s), t))
      
      comment "q_dot_prod, step 5: set b3 <- (t mod 2a3) - (a3 - 1)."
      (a3,twice_a3) <- q_mult_param 2 a3
      (t,twice_a3,b3) <- q_mod_unsigned t twice_a3
      (a3,b3) <- q_sub_in_place a3 b3
      b3 <- q_increment b3
      label b3 "b3"

      comment "q_dot_prod, step 6: test if (a3 > root Delta), store result as case_a3"
      (a3,case_a3) <- q_gt_param a3 (floor (sqrt (fromIntegral bigD)))
      label case_a3 "case_a3"

      comment "q_dot_prod, step 7: if (a3 > root Delta), then b3 <- b3 + (floor root Delta) - a3"      
      b3 <- q_add_param_in_place
              (floor (sqrt (fromIntegral bigD)))
              b3 `controlled` case_a3  
      (a3,b3) <- q_sub_in_place a3 b3 `controlled` case_a3
      
      return ((a1,a2,b1,b2),(khat,uhat,vhat),(k,x,w),(a1a2,b1b2,k_sq,t,case_a3,twice_a3),(a3,b3)))
    
    (\(inputs,temp1,(k,x,w),temp3,(a3,b3)) -> do
      comment "q_dot_prod, step 8: copy computed values into place for I3 = I1.I2"
      (a3,a3_out) <- qc_copy_fun a3
      (b3,b3_out) <- qc_copy_fun b3
      (k,k_out) <- qc_copy_fun k
      l_out <- qinit (intm n 1)
      label (k_out,l_out,a3_out,b3_out) "I3"
      comment "q_dot_prod: uncompute garbage."
      return ((inputs,temp1,(k,x,w),temp3,(a3,b3))
             ,(k_out,l_out,a3_out,b3_out)))
  
  return (IdealRed bigD1 a1 b1, IdealRed bigD1 a2 b2, Ideal bigD1 k l a3 b3)

-- | Compute the dot-product of two reduced fractional ideals, all with distance.
q_dot_prod_with_dist :: IdRedDistQ -> IdRedDistQ -> Circ (IdRedDistQ, IdRedDistQ, IdDistQ)
q_dot_prod_with_dist = box "q_dot_prod_with_dist" $ \(ii,dist_ii) (jj,dist_jj) -> do
  (ii, jj, ii_jj) <- q_dot_prod ii jj
  (dist_ii, dist_jj, dist_ii_jj) <- q_mult dist_ii dist_jj
  return ( (ii,dist_ii), (jj,dist_jj), (ii_jj,dist_ii_jj) )

-- | Given two reduced ideals-with-distance, compute their star-product, with distance.
--
-- This is /I/*/J/ of [Jozsa 2003], Sec. 7.1, defined as the first reduced
-- ideal-with-distance following /I/⋅/J/.
q_star_prod :: IdRedDistQ -> IdRedDistQ -> Circ (IdRedDistQ, IdRedDistQ, IdRedDistQ)
q_star_prod = box "q_star_prod" $ \iid jjd -> do 
  let bigD = bigD_of_IdealRed $ fst iid

  ((iid,jjd), kkd_out) <- with_computed_fun
    (iid,jjd) 
    (\(iid,jjd) -> do
      comment "q_star_prod, step 1: K <- 1/ka (I . J)"
      label (iid,jjd) (("I","δ(I)"),("J","δ(J)"))
      (iid,jjd,ii_jjd) <- q_dot_prod_with_dist iid jjd
      label (ii_jjd) ("II.JJ")
      (ii_jjd,kkd) <- q_normalize ii_jjd
      label (kkd) ("1/ka (II.JJ)")

      comment "q_star_prod, step 2: while K not reduced, set K <- rho(K)"
      (kkd_initial,kkd_reduced) <- q_bounded_while_with_garbage
        (\(kk,dist) -> do
          comment "q_star_prod, step 2, loop conditional: is K reduced yet?"
          (kk,c) <- q_is_reduced kk
          c <- qnot c
          return ((kk,dist),c))
        ((ceiling $ (logBase 2 $ fromIntegral bigD) / 2) + 1) 
-- Generally, reduction may require log_2 (a/√D) steps, 
-- but here a is a_3 from the dot-product I.J,
-- so a = a_3 = (a1 * a2) / k^2 ≤ a1 * a2;
-- but now a1, a2 ≤ √D since they come from reduced ideals,
-- so a ≤ √D * √D = D, and the bound simplifies.
        kkd 
        (\kkd_old -> do 
          comment "q_star_prod, step 2, loop body: compute ρ(Κ)"
          (kkd_old,kkd_new) <- q_rho_d kkd_old 
          return (kkd_new,kkd_old))

      let (ii_jj,dist_ij) = ii_jjd
          (kk_reduced,dist_k) = kkd_reduced

      comment "q_star_prod, step 2c: assert that K is now reduced."
      kk <- q_assert_reduced kk_reduced

      comment "q_star_prod, step 3: pull K backwards or forwards to be as close as possible to I.J"
      -- NB: implementation of the conditional + whiles could almost certainly be improved.

      (dist_k, dist_ij, k_lt_ij) <- q_lt dist_k dist_ij
      label k_lt_ij "Initially, δ(K) ≤ δ(I.J)?"
      let ii_jjd = (ii_jj,dist_ij)
          kkd = (kk,dist_k)

      comment "q_star_prod, step 3a: pull-forwards loop"
      ((dist_ij, kkd), (dij', kkd_forwards)) <- q_bounded_while_with_garbage
        (\(dist_ij,(kk,dist_k)) -> do
          comment "q_star_prod, step 3a, loop condition: is δ(K) ≤ δ(II.JJ) still?"
          (dist_k, dist_ij, k_lt_ij) <- q_lt dist_k dist_ij
          return ((dist_ij,(kk,dist_k)),k_lt_ij))
        (ceiling $ 3 * (logBase 2 $ fromIntegral bigD) / 2) 
        (dist_ij,kkd) 
        (\(dij,kkd_old) -> do 
          comment "q_star_prod, step 3a, loop body: compute ρ(Κ)"
          (kkd_old,kkd_new) <- q_rho_red_d kkd_old 
          return ((dij,kkd_new),kkd_old))

      comment "q_star_prod, step 3b: pull-backwards loop"
      ((dist_ij, kkd), (dij'', kkd_too_far_back)) <- q_bounded_while_with_garbage
        (\(dist_ij,(kk,dist_k)) -> do
          comment "q_star_prod, step 3b, loop condition: is δ(K) ≥ δ(II.JJ) still?"
          (dist_k, dist_ij, k_gt_ij) <- q_gt dist_k dist_ij
          return ((dist_ij,(kk,dist_k)),k_gt_ij))
        (ceiling $ 3 * (logBase 2 $ fromIntegral bigD) / 2) 
        (dist_ij,kkd) 
        (\(dij,kkd_old) -> do 
          comment "q_star_prod, step 3b, loop body: compute ρ^-1(Κ)"
          (kkd_old,kkd_new) <- q_rho_inv_red_d kkd_old 
          return ((dij,kkd_new),kkd_old))
      comment "q_star_prod, step 3b, cleanup: apply ρ once to the output of this loop"
      (kkd_too_far_back, kkd_back) <- q_rho_red_d kkd_too_far_back

      return ((iid, jjd, ii_jjd, kkd_initial, kkd, dij', dij'', kkd_too_far_back), k_lt_ij, kkd_forwards, kkd_back))

    (\(stuff, k_lt_ij, kkd_forwards, kkd_back) -> do
      comment "q_star_prod, step 4: Return the result of either first or second loop, depending on test."
      kkd_out <- qinit $ qc_false kkd_forwards
      (kkd_out,kkd_forwards) <- controlled_not kkd_out kkd_forwards `controlled` k_lt_ij .==. True
      (kkd_out,kkd_backwards) <- controlled_not kkd_out kkd_back `controlled` k_lt_ij .==. False
      label kkd_out "kkd_out"
      return ((stuff, k_lt_ij, kkd_forwards, kkd_back),kkd_out))

  return (iid, jjd, kkd_out)

-- | Compute /I/ * /I/, where /I/ is a reduced ideal/distance pair.
q_star_square :: IdRedDistQ -> Circ (IdRedDistQ, IdRedDistQ)
q_star_square = \iid -> with_computed_fun iid qc_copy_fun
  (\(iid, iid_copy) -> do
    (iid, iid_copy, iid_square) <- q_star_prod iid iid_copy
    return ((iid, iid_copy), iid_square))

-- ======================================================================
-- * The function f[sub /N/]

-- |  @'q_fN' Δ /s/ /n/ /l/ /qi/ /j/@: find the minimal ideal-with-distance (/J/,δ[sub /J/]) such that δ[sub /J/] > /x/, where /x/ = /i/\//N/ + /j/\//L/, where /N/ = 2[sup /n/], /L/ = 2[sup /l/].  /qi/ is quantum; other inputs are classical parameters.  Return (/i/,/J/,δ[sub /J/]–/x/).  Work under the assumption that /R/ < 2[sup /s/].
--
-- This is the function /h/ of [Jozsa 2003], Sec. 9, discretized with precision 1\//N/ = 2[sup −/n/],
-- and perturbed by the jitter parameter /j/\//L/.
q_fN :: CLIntP -> Int -> Int -> QDInt -> IntM -> Circ (QDInt,(IdealRedQ,FPRealQ))
q_fN bigD n l qi j = do
  let p = precision_for_fN bigD n l
      nn = 2^n
      ll = 2^l
      q = qdint_length qi
-- Need to figure out a bound /p/ on the precision of the real arithmetic required.
-- It’s tempting to take /p/ = max(/n/,/l/); but I [pll] think we need larger, since if
-- I understand correctly, we want the /final output/ with precision of 2^-n, which 
-- requires higher precision in intermediate calculations.

  (qi, (jj, diff)) <- with_computed_fun
    qi
    (\qi -> do
      comment "q_fN, step 1: Precompute x := i/N + j/L, as it used many times."
      qi <- return $ fprealx (-n) qi
      qj <- qinit (fprealx (-l) j)
      (qi,qj,qx) <- fprealq_add_het (-p) (q - n + p) qi qj
      label qx "x := i/N + j/L"

      comment "q_fN, step 2: J <- ρ^2(O)."
      oo <- qinit $ fix_sizes_IdealRed $ unit_idealRed bigD
      dist_o <- qinit $ (fprealx (-p) (intm (q - n + p) 0))
      let ood = (oo,dist_o)
      label ood ("O", "δ_O = 0")

      (ood,jjd0) <- q_rho_red_d ood
      label jjd0 ("J0", "δ_J0)")
      (jjd0,jjd1) <- q_rho_red_d jjd0
      label jjd1 ("J1", "δ_J1)")
      
      comment "q_fN, step 3: compute the iterated squares of (J1,δ_J1)."
      -- Note: quantumly, it is cheaper to compute them all unconditionally, rather than
      -- using a conditional loop that stops early, as one might classically.
      jjds <- loop_with_indexM
        (ceiling $ (fromIntegral q) * (log 2) / (nn * 
          (snd $ rho_d $ rho_d $ (unit_ideal bigD, 0))))
        [jjd1]
        (\i (jjd_prev:jjds_earlier) -> do
          (jjd_prev,jjd_new) <- q_star_square jjd_prev
          label jjd_new ("J_" ++ show (i+2), "δ_" ++ show (i+2))
          return (jjd_new:jjd_prev:jjds_earlier))

      comment "q_fN, step 4: compute the greatest product of these ≤ x"
      -- Again, it is quantumly cheaper to start at the maximum possible bound, instead of k = M.

      let jjd_star = ood
      label jjd_star ("J_*, δ_*")

      (qx, jjd_star, garbage) <- foldM 
        (\(qx, jjd_star_old, garbage) jjd_k -> do
          (jjd_star_old, jjd_k, jjd_star_candidate) <- q_star_prod jjd_star_old jjd_k
          let (jj_star_candidate, dist_candidate) = jjd_star_candidate 
          (dist_candidate, qx, test) <- q_lt dist_candidate qx
          let jjd_star_candidate = (jj_star_candidate, dist_candidate) 
          jjd_star_new <- qinit (qc_false jjd_star_old)
          (jjd_star_new, jjd_star_candidate) <- 
            controlled_not jjd_star_new jjd_star_candidate `controlled` test .==. True
          (jjd_star_new, jjd_star_old) <-
            controlled_not jjd_star_new jjd_star_old `controlled` test .==. False
          label jjd_star_new ("J_*, δ(J_*)")
          return (qx, jjd_star_new, (jjd_star_old,jjd_star_candidate,jjd_k,test):garbage))
        (qx, jjd_star, [])
        jjds
    
      label jjd_star ("J_*, δ_*)")
      comment "q_fN: (J_*,δ_*) is now the greatest ideal/distance pair ≤ x constructible from the iterated star-squares (J_k,δ_k)."

      comment "q_fN, step 5: apply ρ^2 to (J_*,δ_*) as long as δ_* ≤ x."
      ((jjd_star_initial, qx), (jjd_star, qx_copy)) <- q_bounded_while_with_garbage
        -- conditional test:
        (\((jj_star, dist_star), qx) -> do
          (dist_star, qx, test) <- q_le dist_star qx
          return (((jj_star, dist_star), qx), test))
        -- bound
        (ceiling $ 3 * logBase 2 (fromIntegral bigD) / 2)
        -- starting value
        (jjd_star, qx)
        -- body of loop
        (\(jjd_star_old, qx) -> do
          (jjd_star_old, rho_jjd_star_old) <- q_rho_red_d jjd_star_old
          (rho_jjd_star_old, jjd_star_new) <- q_rho_red_d rho_jjd_star_old
          return ((jjd_star_new, qx), (jjd_star_old, rho_jjd_star_old)))
      qx <- qc_uncopy_fun qx qx_copy

      comment "q_fN, step 6: apply ρ^{-1} once more if necessary."
      (jjd_star_candidate1, jjd_star_candidate2) <- q_rho_inv_red_d jjd_star
      
      let (jj_star_candidate1, dist_star_candidate1) = jjd_star_candidate1
      (dist_star_candidate1, qx, final_test) <- q_le dist_star_candidate1 qx
      let jjd_star_candidate1 = (jj_star_candidate1, dist_star_candidate1)
      
      -- End of the computation part of the 'with_computed_fun'.  
      -- Pass on everything we’ve constructed, with the relevant stuff put first.  
      return (qx, jjd_star_candidate1, jjd_star_candidate2, final_test,
              (qi, qj, garbage, jjd0, jjd1, jjd_star_initial, jjd_star_initial)))

    (\(qx, jjd_star_candidate1, jjd_star_candidate2, test, irrelevant) -> do
      jjd_star_out <- qinit (qc_false jjd_star_candidate1)
      (jjd_star_out, jjd_star_candidate1) <- controlled_not jjd_star_out jjd_star_candidate1 `controlled` test .==. False
      (jjd_star_out, jjd_star_candidate1) <- controlled_not jjd_star_out jjd_star_candidate2 `controlled` test .==. True

      let (jj_out, dist_jj) = jjd_star_out
      (qx,diff_out) <- fprealq_sub_in_place qx dist_jj

      return ((qx, jjd_star_candidate1, jjd_star_candidate2, test, irrelevant),
              (jj_out, diff_out)))
  
  return (qi, (jj, diff))
