-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | This module implements an efficient single-qubit Clifford+/T/
-- approximation algorithm. The algorithm is described here:
-- 
-- * Peter Selinger. Efficient Clifford+/T/ approximation of
-- single-qubit operators. <http://arxiv.org/abs/1212.6253>.

module Libraries.Synthesis.Newsynth where

import Libraries.Synthesis.Ring
import Libraries.Synthesis.Ring.FixedPrec
import Libraries.Synthesis.Matrix
import Libraries.Synthesis.CliffordT
import Libraries.Synthesis.EuclideanDomain
import Libraries.Synthesis.SymReal

import System.Random
import Data.Maybe
import Data.Number.FixedPrec
import Data.Time
import System.Locale
import System.IO

-- ----------------------------------------------------------------------
-- * Miscellaneous functions

-- | A useful operation for the 'Maybe' monad, used to ensure that
-- some condition holds (i.e., return 'Nothing' if the condition is
-- false). To be used like this:
-- 
-- > do
-- >   x <- something
-- >   y <- something_else
-- >   ensure (x > y)
-- >   ...
ensure :: Bool -> Maybe ()
ensure True = Just ()
ensure False = Nothing

-- | Return the head of a list, if non-empty, or else 'Nothing'.
maybe_head :: [a] -> Maybe a
maybe_head [] = Nothing
maybe_head (h:t) = Just h

-- | Exponentiation via repeated squaring, parameterized by a
-- multiplication function and a unit. Given an associative
-- multiplication function @*@ with unit @e@, the function 'power'
-- @(*)@ /e/ /a/ /n/ efficiently computes /a/[sup /n/] = /a/ @*@ (/a/
-- @*@ (… @*@ (/a/ @*@ /e/)…)).
power :: (a -> a -> a) -> a ->  a -> Integer -> a
power mul unit = aux where
  aux x n
    | n <= 0 = unit
    | n == 1 = x
    | odd n = x `mul` (x `aux` (n-1))
    | otherwise = y `mul` y where y = x `aux` (n `div` 2)
  
-- | Given positive numbers /b/ and /x/, return (/n/, /r/) such that
-- 
-- * /x/ = /r/ /b/[sup /n/] and                           
--                                   
-- * 1 ≤ /r/ < /b/.                                  
--                                   
-- In other words, let /n/ = ⌊log[sub /b/] /x/⌋ and 
-- /r/ = /x/ /b/[sup −/n/]. This can be more efficient than 'floor'
-- ('logBase' /b/ /x/) depending on the type; moreover, it also works
-- for exact types such as 'Rational' and 'EReal'.
floorlog :: (Fractional b, Ord b) => b -> b -> (Integer, b)
floorlog b x 
    | x <= 0            = error "floorlog: argument not positive"    
    | 1 <= x && x < b   = (0, x)
    | 1 <= x*b && x < 1 = (-1, b*x)
    | r < b             = (2*n, r)
    | otherwise         = (2*n+1, r/b)
    where
      (n, r) = floorlog (b^2) x

-- ----------------------------------------------------------------------
-- * Randomized algorithms

-- | A combinator for turning a probabilistic function that succeeds
-- with some small probability into a probabilistic function that
-- always succeeds, by trying again and again.
keeptrying :: (RandomGen g) => (g -> Maybe a) -> (g -> a)
keeptrying f g = case f g1 of
  Just res -> res
  Nothing -> keeptrying f g2
  where
    (g1, g2) = split g

-- | Like 'keeptrying', but also returns a count of the number of attempts.
keeptrying_count :: (RandomGen g) => (g -> Maybe a) -> (g -> (a, Integer))
keeptrying_count f g = aux g 1 where
  aux g n = case f g1 of
    Just res -> (res, n)
    Nothing -> aux g2 n1
    where
      (g1, g2) = split g
      !n1 = n + 1

-- | A combinator for turning a probabilistic function that succeeds
-- with some small probability into a probabilistic function that
-- succeeds with a higher probability, by repeating it /n/ times. 
try_for :: (RandomGen g) => Integer -> (g -> Maybe a) -> (g -> Maybe a)
try_for n f g
  | n <= 0 = Nothing
  | otherwise = case f g1 of
      Just res -> Just res
      Nothing -> try_for (n-1) f g2
  where
    (g1, g2) = split g    

-- ----------------------------------------------------------------------
-- * Square roots in ℤ[√2]

-- | Return a square root of an element of ℤ[√2], if such a square
-- root exists, or else 'Nothing'.
dinteger_root :: DInteger -> Maybe DInteger
dinteger_root z@(RootTwo a b) = res where
  d = a^2 - 2*b^2
  r = intsqrt d
  x1 = intsqrt ((a + r) `div` 2)
  x2 = intsqrt ((a - r) `div` 2)
  y1 = intsqrt ((a - r) `div` 4)
  y2 = intsqrt ((a + r) `div` 4)
  w1 = RootTwo x1 y1
  w2 = RootTwo x2 y2
  w3 = RootTwo x1 (-y1)
  w4 = RootTwo x2 (-y2)
  res 
    | w1*w1 == z = Just w1
    | w2*w2 == z = Just w2
    | w3*w3 == z = Just w3
    | w4*w4 == z = Just w4
    | otherwise  = Nothing
  
-- ----------------------------------------------------------------------  
-- * Roots of −1 in ℤ[sub /p/]
  
-- | Input an integer /p/, and maybe output a root of −1 modulo /p/.
-- This succeeds with probability at least 1\/2 if /p/ is a positive
-- prime ≡ 1 (mod 4); otherwise, the success probability is
-- unspecified (and may be 0).
root_minus_one_step :: (RandomGen g) => Integer -> g -> Maybe Integer
root_minus_one_step p g = do
  let (b, _) = randomR (1, p-1) g
  let h = power mul 1 b ((p-1) `div` 4)
  ensure $ h `mul` h == p-1  -- succeeds with probability 1/2
  return h
    where
      mul :: Integer -> Integer -> Integer
      mul a b = (a*b) `mod` p
      
-- | Input a positive prime /p/ ≡ 1 (mod 4), and output a root of −1.
root_minus_one :: (RandomGen g) => Integer -> g -> Integer
root_minus_one p = keeptrying (root_minus_one_step p)

-- ----------------------------------------------------------------------
-- * Solving a Diophantine equation

-- | Input ξ ∈ ℤ[√2], and maybe output some t ∈ ℤ[ω] such that 
-- t[sup †]t = ξ. If ξ ≥ 0, ξ[sup •] ≥ 0, and /p/ = ξ[sup •]ξ is a
-- prime ≡ 1 (mod 4) in ℤ, then this succeeds with probability at least
-- 1\/2.  Otherwise, the success probability is unspecified and may be
-- 0.
dioph_step :: (RandomGen g) => DInteger -> g -> Maybe ZOmega
dioph_step xi g = do
  h <- root_minus_one_step (norm xi) g
  let s = euclid_gcd (fromInteger h+i) (fromDInteger xi) :: ZOmega
      ss = dinteger_of_zomega (adj s * s)
      u = euclid_div xi ss
  v <- dinteger_root u
  let t = fromDInteger v * s
  ensure $ adj t * t == fromDInteger xi -- check the answer, just in case
  return t

-- | Input ξ ∈ ℤ[√2] such that ξ ≥ 0, ξ[sup •] ≥ 0, and /p/ = 
-- ξ[sup •]ξ is a prime ≡ 1 (mod 4) in ℤ. Output t ∈ ℤ[ω] such that
-- t[sup †]t = ξ. If the hypotheses are not satisfied, this will
-- likely loop forever.
dioph :: (RandomGen g) => DInteger -> g -> ZOmega
dioph xi = keeptrying (dioph_step xi)

-- ----------------------------------------------------------------------
-- * Approximations in ℤ[√2]

-- | Input two intervals [/x/₀, /x/₁] ⊆ ℝ and [/y/₀, /y/₁] ⊆ ℝ. Output
-- a list of all points /z/ = /a/ + √2/b/ ∈ ℤ[√2] such that /z/ ∈
-- [/x/₀, /x/₁] and /z/[sup •] ∈ [/y/₀, /y/₁]. The list will be
-- produced lazily, and will be sorted in order of increasing /z/.
-- 
-- It is a theorem that there will be at least one solution if ΔxΔy ≥ (1
-- + √2)², and at most one solution if ΔxΔy < 1, where Δx = /x/₁ − /x/₀ ≥ 0
-- and Δy = /y/₁ − /y/₀ ≥ 0. Asymptotically, the expected number of
-- solutions is ΔxΔy/\√8.
-- 
-- This function is formulated so that the intervals can be specified
-- exactly (using a type such as 'EReal'), or approximately (using a
-- type such as 'Double' or 'FixedPrec' /e/).
gridpoints :: (RootTwoRing r, Fractional r, Floor r, Ord r, ToReal r) => (r, r) -> (r, r) -> [DInteger]
gridpoints (x0, x1) (y0, y1)
  | dy <= 0 && dx > 0 = 
        map adj2 $ gridpoints (y0, y1) (x0, x1)
  | dy >= lambda && even n =
        map (lambdainv^n *) $ gridpoints (lambda^n*x0, lambda^n*x1) (lambda'^n*y0, lambda'^n*y1)
  | dy >= lambda && odd n =
        map (lambdainv^n *) $ gridpoints (lambda^n*x0, lambda^n*x1) (lambda'^n*y1, lambda'^n*y0)
  | dy > 0 && dy < 1 && even n = 
        map (lambda^m *) $ gridpoints (lambdainv^m*x0, lambdainv^m*x1) (lambdainv'^m*y0, lambdainv'^m*y1)
  | dy > 0 && dy < 1 && odd n = 
        map (lambda^m *) $ gridpoints (lambdainv^m*x0, lambdainv^m*x1) (lambdainv'^m*y1, lambdainv'^m*y0)
  | otherwise =
        [ RootTwo a b | a <- [amin..amax], b <- [bmin a..bmax a], test a b ] 
  where
    dx = x1 - x0
    dy = y1 - y0
    (n, _) = floorlog lambda dy
    m = -n
    
    lambda :: (RootTwoRing r) => r
    lambda = 1 + roottwo
    lambda' :: (RootTwoRing r) => r
    lambda' = 1 - roottwo
    lambdainv :: (RootTwoRing r) => r
    lambdainv = -1 + roottwo
    lambdainv' :: (RootTwoRing r) => r
    lambdainv' = -1 - roottwo

    within x (x0, x1) = x0 <= x && x <= x1
    amin = ceiling_of ((x0 + y0) / 2)
    amax = floor_of ((x1 + y1) / 2)
    bmin a = ceiling_of ((fromInteger a - y1) / roottwo)
    bmax a = floor_of ((fromInteger a - y0) / roottwo)
    test a b = fromDInteger x `within` (x0, x1) && fromDInteger (adj2 x) `within` (y0, y1)
      where x = RootTwo a b

-- | Input two intervals [/x/₀, /x/₁] ⊆ ℝ and [/y/₀, /y/₁] ⊆ ℝ and a
-- source of randomness. Output a random element /z/ = /a/ + √2/b/
-- ∈ ℤ[√2] such that /z/ ∈ [/x/₀, /x/₁] and /z/[sup •] ∈ [/y/₀,
-- /y/₁]. 
-- 
-- Note: the randomness will not be uniform. To ensure that the set of
-- solutions is non-empty, we must have ΔxΔy ≥ (1 + √2)², where Δx =
-- /x/₁ − /x/₀ ≥ 0 and Δy = /y/₁ − /y/₀ ≥ 0. If there are no solutions
-- at all, the function will return 'Nothing'.
-- 
-- This function is formulated so that the intervals can be specified
-- exactly (using a type such as 'EReal'), or approximately (using a
-- type such as 'Double' or 'FixedPrec' /e/).
gridpoint_random :: (RootTwoRing r, Fractional r, Floor r, Ord r, ToReal r, RandomGen g) => (r, r) -> (r, r) -> g -> Maybe DInteger
gridpoint_random (x0, x1) (y0, y1) g = z
  where
    dx = max 0 (x1 - x0)
    dy = max 0 (y1 - y0)
    area = dx * dy
    n = floor_of (area + 1)
    (i,_) = randomR (0, n-1) g
    r = fromInteger i / fromInteger n
    pts = gridpoints (x0 + r * dx, x1) (y0, y1) ++ gridpoints (x0, x1) (y0, y1)
    z = maybe_head pts

-- | Input an integer /e/, two intervals [/x/₀, /x/₁] ⊆ ℝ and [/y/₀,
-- /y/₁] ⊆ ℝ, and a source of randomness. Output random /z/ = /a/ +
-- √2/b/ ∈ ℤ[√2] such that /a/ + √2/b/ ∈ [/x/₀, /x/₁], /a/ - √2/b/ ∈
-- [/y/₀, /y/₁], and /a/-/e/ is even.
-- 
-- Note: the randomness will not be uniform. To ensure that the set of
-- solutions is non-empty, we must have ΔxΔy ≥ 2(√2 + 1)², where Δx =
-- /x/₁ − /x/₀ ≥ 0 and Δy = /y/₁ − /y/₀ ≥ 0. If there are no solutions
-- at all, the function will return 'Nothing'.
-- 
-- This function is formulated so that the intervals can be specified
-- exactly (using a type such as 'EReal'), or approximately (using a
-- type such as 'Double' or 'FixedPrec' /e/).
gridpoint_random_parity :: (RootTwoRing r, Fractional r, Floor r, Ord r, ToReal r, RandomGen g) => Integer -> (r, r) -> (r, r) -> g -> Maybe DInteger
gridpoint_random_parity e (x0,x1) (y0,y1) g = do
  z' <- gridpoint_random (x0', x1') (-y1', -y0') g
  return (roottwo * z' + fromInteger e2)
  where 
    x0' = (x0 - e') / roottwo
    x1' = (x1 - e') / roottwo
    y0' = (y0 - e') / roottwo
    y1' = (y1 - e') / roottwo
    e' = fromInteger e2
    e2 = e `mod` 2

-- ----------------------------------------------------------------------
-- * Approximate synthesis
  
-- ----------------------------------------------------------------------
-- ** The main algorithm

-- | The internal implementation of the approximate synthesis
-- algorithm. The parameters are:
-- 
-- * an angle θ, to implement a /R/[sub /z/](θ) = [exp −/i/θ/Z/\/2]
-- gate;
--   
-- * a precision /p/ ≥ 0 in bits, such that ε = 2[sup -/p/];
-- 
-- * a source of randomness /g/.
-- 
-- With some probability, output a unitary operator in the
-- Clifford+/T/ group that approximates /R/[sub /z/](θ) to within ε in
-- the operator norm. This operator can then be converted to a list of
-- gates with 'to_gates'. Also output log[sub 0.1] of the actual
-- error, or 'Nothing' if the error is 0.
-- 
-- This implementation does not use seeding.
-- 
-- As a special case, if the /R/[sub /z/](θ) is a Clifford operator
-- (to within the given ε), always return this operator directly.
-- 
-- Note: the parameter θ must be of a real number type that has enough
-- precision to perform intermediate calculations; the typically
-- requires precision O(ε[sup 2]).  A more user-friendly function that
-- does this automatically is 'newsynth'.
newsynth_step :: forall r g.(RealFrac r, Floating r, RootHalfRing r, Floor r, Adjoint r, ToReal r, RandomGen g) => r -> r -> g -> Maybe (U2 DOmega, Maybe Double)
newsynth_step prec theta = payload where
  -- We are careful to do all computations that depend only on epsilon
  -- and theta (but not g) outside of aux, to avoid re-computing them
  -- with each attempt.
  
  -- Calculate ε.
  epsilon = 2 ** (-prec)
  
  -- Convert prec to a Double
  dprec = fromRational (toRational prec)
  
  -- Determine k.
  const = 3 + 2 * logBase 2 (1 + sqrt 2) :: Double
  k = ceiling (const + 2 * dprec)
  scale = roottwo^k
  
  -- Normalize θ to be in [-π/4, π/4].
  n = round(theta / (pi/2))
  theta1 = theta - fromInteger n * pi/2
  
  -- Describe the ε-region.
  z @ (x,y) = (cos (theta1 / 2), -sin (theta1 / 2))
  e2 = 1 - epsilon^2/2
  e4 = 1 - epsilon^2/4
  z1 @ (x1,y1) = (e4 * x, e4 * y)
  e' = epsilon / roottwo
  f = e' * sqrt((1+e'/2)*(1-e'/2)) -- == sqrt(1-e4^2)
  w @ (wx,wy) = (-f * y, f * x)
  y_min = y1 - wy
  y_max = y1 + wy
  y'_min = y_min * scale
  y'_max = y_max * scale
  dx = (e4 - e2) * x
  
  find_uU_step = 
    -- As a special case, if (1,0) is in the ε-region, return the
    -- identity operator.
    if x >= e2 then \g -> Just 1 else aux

  -- The rest of the computation depends on the random seed g.
  payload g = do
    uU1 <- find_uU_step g  
    let uU = correct uU1 n
    let err = calc_error uU theta
    return (uU, err)
  
  aux g = do
    -- Find a random grid point in the ε-region.
    let (g0,g1) = split g
    beta <- gridpoint_random (y'_min, y'_max) (-roothalf * scale, roothalf * scale) g0
    let  
      beta' = fromDInteger beta / scale
      tmp = (beta' - e2 * y) / wy
      x0 = e2 * x + tmp * wx
      x1 = x0 + dx
      x0' = x0 * scale
      x1' = x1 * scale
      (g2,g3) = split g1
      RootTwo c _ = beta
    alpha <- gridpoint_random_parity (c+1) (x0', x1') (-roothalf * scale, roothalf * scale) g2
    
    -- Calculate u, ξ, and solve Diophantine equation to calculate t.
    let  
      u = (fromDInteger alpha) + i * (fromDInteger beta) :: ZOmega
      xi = dinteger_of_zomega (2^k - u * adj u)
    t <- dioph_step xi g3
    
    -- If Diophantine equation solved successfully, calculate matrix U.
    let
      u' = fromZOmega u * roothalf^k :: DOmega
      t' = fromZOmega t * roothalf^k :: DOmega
      uU1 = matrix2x2 (u', -(adj t'))
                      (t',  (adj u'))
           
    return uU1
    
  -- Correct for when θ wasn't in [-π/4, π/4].
  correct uU1 n = uU1 * rR^(n `mod` 8) where
    rR = matrix2x2 (omega^7, 0)
                   (0,   omega)
    
  -- Calculate the actual error. Since this is done lazily, this
  -- incurs no overhead in case the error is not actually used.
  calc_error uU theta = log_err where
    uU_fixed = matrix_map fromDOmega uU :: U2 (Cplx r)
    zrot_fixed = zrot theta :: U2 (Cplx r)
    err = sqrt (real (hs_sqnorm (uU_fixed - zrot_fixed)) / 2)
    log_err 
      | err <= 0  = Nothing
      | otherwise = Just (log_double err / log 0.1)

-- ----------------------------------------------------------------------
-- ** User-friendly functions

-- | A user-friendly interface to the approximate synthesis
-- algorithm. The parameters are:
-- 
-- * an angle θ, to implement a /R/[sub /z/](θ) = [exp −/i/θ/Z/\/2]
-- gate;
--   
-- * a precision /b/ ≥ 0 in bits, such that ε = 2[sup -/b/];
-- 
-- * a source of randomness /g/.
-- 
-- Output a unitary operator in the Clifford+/T/ group that
-- approximates /R/[sub /z/](θ) to within ε in the operator norm. This
-- operator can then be converted to a list of gates with
-- 'to_gates'.
-- 
-- This implementation does not use seeding.
-- 
-- Note: the argument /theta/ is given as a symbolic real number. It
-- will automatically be expanded to as many digits as are necessary
-- for the internal calculation. In this way, the caller can specify,
-- e.g., an angle of 'pi'\/128 @::@ 'SymReal', without having to worry
-- about how many digits of π to specify.
newsynth :: (RandomGen g) => Double -> SymReal -> g -> U2 DOmega
newsynth prec theta g = m where
  (m, _, _) = newsynth_stats prec theta g

-- | A version of 'newsynth' that also returns some statistics:
-- log[sub 0.1] of the actual approximation error (or 'Nothing' if the
-- error is 0), and the number of candidates tried.
newsynth_stats :: (RandomGen g) => Double -> SymReal -> g -> (U2 DOmega, Maybe Double, Integer)
newsynth_stats prec theta g = dynamic_fixedprec2 digits f prec theta where
  digits = ceiling (10 + 2 * prec * logBase 10 2)
  f prec theta = (m, err, ct) where
    ((m, err), ct) = keeptrying_count (newsynth_step prec theta) g

-- | A version of 'newsynth' that returns a list of gates instead of a
-- matrix. The inputs are the same as for 'newsynth'.
-- 
-- Note: the list of gates will be returned in right-to-left order,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
newsynth_gates :: (RandomGen g) => Double -> SymReal -> g -> [Gate]
newsynth_gates prec theta g = synthesis_u2 (newsynth prec theta g)
