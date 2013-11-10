-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

-- | This module provides functions for the representation and exact
-- synthesis of multi-qubit Clifford+/T/ operators. 
-- 
-- The multi-qubit Clifford+/T/ exact synthesis algorithm is described
-- in the paper:
-- 
-- * Brett Giles, Peter Selinger. Exact synthesis of multiqubit Clifford+T
-- circuits. /Physical Review A/ 87, 032332 (7 pages), 2013. Available
-- from <http://arxiv.org/abs/1212.0506>.
-- 
-- It generalizes the single-qubit exact synthesis algorithm of
-- Kliuchnikov, Maslov, and Mosca.

module Libraries.Synthesis.MultiQubitSynthesis where

import Libraries.Synthesis.Matrix
import Libraries.Synthesis.Ring
import Data.List
import Data.Ord

-- ----------------------------------------------------------------------
-- * Residues

-- | A type class for things that have residues. In a typical
-- instance, /a/ is a ring whose elements are expressed with
-- coefficients in ℤ, and /b/ is a corresponding ring whose elements
-- are expressed with coefficients in ℤ[sub 2].
class Residue a b | a -> b where
  -- | Return the residue of something.
  residue :: a -> b
  
instance Residue Integer Z2 where
  residue = parity
  
instance Residue a b => Residue (Omega a) (Omega b) where
  residue (Omega a b c d) = Omega (residue a) (residue b) (residue c) (residue d)

instance Residue a b => Residue (RootTwo a) (RootTwo b) where
  residue (RootTwo a b) = RootTwo (residue a) (residue b)
  
instance (Residue a a', Residue b b') => Residue (a,b) (a',b') where
  residue (x,y) = (residue x, residue y)
  
instance Residue () () where  
  residue = const ()
  
instance (Residue a b) => Residue [a] [b] where  
  residue = map residue
  
instance (Residue a b) => Residue (Cplx a) (Cplx b) where  
  residue (Cplx a b) = Cplx (residue a) (residue b)
  
instance (Residue a b) => Residue (Vector n a) (Vector n b) where  
  residue = vector_map residue
  
instance (Residue a b) => Residue (Matrix m n a) (Matrix m n b) where
  residue (Matrix m) = Matrix (residue m)
  
-- ----------------------------------------------------------------------
-- * One- and two-level operators
  
-- ----------------------------------------------------------------------  
-- ** Symbolic representation

-- | An index for a row or column of a matrix.
type Index = Int

-- | Symbolic representation of one- and two-level operators. Note
-- that the power /k/ in the 'TL_T' and 'TL_omega' constructors can be
-- positive or negative, and should be regarded modulo 8.
-- 
-- Note: when we use a list of 'TwoLevel' operators to express a
-- sequence of operators, the operators are meant to be applied
-- right-to-left, i.e., as in the mathematical notation for matrix
-- multiplication. This is the opposite of the quantum circuit
-- notation.
data TwoLevel = 
  TL_X Index Index -- ^ /X/[sub /i/,/j/]
  | TL_H Index Index -- ^ /H/[sub /i/,/j/]
  | TL_T Int Index Index -- ^ (/T/[sub /i/,/j/])[super /k/]
  | TL_omega Int Index -- ^ (ω[sub /i/])[super /k/]
  deriving (Show, Eq)

-- | Invert a 'TwoLevel' operator.
invert_twolevel :: TwoLevel -> TwoLevel
invert_twolevel (TL_X i j) = TL_X i j
invert_twolevel (TL_H i j) = TL_H i j
invert_twolevel (TL_T m i j) = TL_T (-m) i j
invert_twolevel (TL_omega m j) = TL_omega (-m) j

-- | Invert a list of 'TwoLevel' operators.
invert_twolevels :: [TwoLevel] -> [TwoLevel]
invert_twolevels = reverse . map invert_twolevel

-- ----------------------------------------------------------------------
-- ** Constructors for two-level matrices

-- | Construct a two-level matrix with the given entries.
twolevel_matrix :: (Ring a, Nat n) => (a,a) -> (a,a) -> Index -> Index -> Matrix n n a
twolevel_matrix (a,b) (c,d) i j = matrix_of_function f where
  f x y 
    | x == i && y == i = a
    | x == i && y == j = b
    | x == j && y == i = c
    | x == j && y == j = d
    | x == y = 1
    | otherwise = 0

-- | Construct a one-level matrix with the given entry.
onelevel_matrix :: (Ring a, Nat n) => a -> Index -> Matrix n n a
onelevel_matrix a i = matrix_of_function f where
  f x y
    | x == i && y == i = a
    | x == y = 1
    | otherwise = 0

-- | Convert a symbolic one- or two-level operator into a matrix.
matrix_of_twolevel :: (ComplexRing a, RootHalfRing a, Nat n) => TwoLevel -> Matrix n n a
matrix_of_twolevel (TL_X i j) = twolevel_matrix (0,1) (1,0) i j
matrix_of_twolevel (TL_H i j) = twolevel_matrix (s,s) (s,-s) i j
  where s = roothalf
matrix_of_twolevel (TL_T k i j) = twolevel_matrix (1,0) (0,omega^(k `mod` 8)) i j
matrix_of_twolevel (TL_omega k i) = onelevel_matrix (omega^(k `mod` 8)) i

-- | Convert a list of symbolic one- or two-level operators into a
-- matrix. Note that the operators are to be applied right-to-left,
-- exactly as in mathematical notation.
matrix_of_twolevels :: (ComplexRing a, RootHalfRing a, Nat n) => [TwoLevel] -> Matrix n n a
matrix_of_twolevels gs = foldl' (*) 1 [ matrix_of_twolevel g | g <- gs ]

-- ----------------------------------------------------------------------
-- * Auxiliary list functions

-- | Replace the /i/th element of a list by /x/.
list_insert :: Index -> a -> [a] -> [a]
list_insert 0 x (h:t) = x:t
list_insert n x (h:t) = h:(list_insert (n-1) x t)
list_insert n x [] = []

-- | Apply a unary operator to element /i/ of a list.
transform_at :: (a -> a) -> Index -> [a] -> [a]
transform_at op i lst = lst' where
  x = lst !! i
  x' = op x
  lst' = list_insert i x' lst

-- | Apply a binary operator to elements /i/ and /j/ of a list.
transform_at2 :: ((a,a) -> (a,a)) -> Index -> Index -> [a] -> [a]
transform_at2 op i j lst = lst' where
  (x,y) = (lst !! i, lst !! j)
  (x',y') = op (x,y)
  lst' = list_insert i x' (list_insert j y' lst)

-- | Split a list into pairs. Return a list of pairs, and a final
-- element if the length of the list was odd.
list_pairs :: [a] -> ([(a,a)], Maybe a)
list_pairs [] = ([], Nothing)
list_pairs [h] = ([], Just h)
list_pairs (h:k:t) = ((h,k):t',r') where (t',r') = list_pairs t

-- ----------------------------------------------------------------------
-- * Functions on ℤ[ω]

-- | Given an element of the form ω[sup /m/], return /m/ ∈ {0,…,7}, or
-- 'Nothing' if not of that form.
log_omega :: ZOmega -> Maybe Int
log_omega (Omega 0 0 0 1) = Just 0
log_omega (Omega 0 0 1 0) = Just 1
log_omega (Omega 0 1 0 0) = Just 2
log_omega (Omega 1 0 0 0) = Just 3
log_omega (Omega 0 0 0 (-1)) = Just 4
log_omega (Omega 0 0 (-1) 0) = Just 5
log_omega (Omega 0 (-1) 0 0) = Just 6
log_omega (Omega (-1) 0 0 0) = Just 7
log_omega _ = Nothing

-- | Multiply a scalar by ω[sup /n/].
omega_power :: (OmegaRing a) => Int -> a -> a
omega_power n x = x * omega^(n `mod` 8)

-- | Divide an element of 'ZOmega' by √2, or throw an error if it is
-- not divisible.
reduce_ZOmega :: ZOmega -> ZOmega
reduce_ZOmega (Omega a b c d) 
  | even (a-c) && even (b-d) = Omega a' b' c' d'
  | otherwise = error "reduce_ZOmega: element not reducible"
  where
    a' = (b-d) `div` 2
    b' = (c+a) `div` 2
    c' = (b+d) `div` 2
    d' = (c-a) `div` 2

-- | Apply the /X/ operator to a 2-dimensional vector over 'ZOmega'.
opX_zomega :: (ZOmega, ZOmega) -> (ZOmega, ZOmega)
opX_zomega (x,y) = (y,x)

-- | Apply the /H/ operator to a 2-dimensional vector over
-- 'ZOmega'. This throws an error if the result is not well-defined
-- over 'ZOmega'.
opH_zomega :: (ZOmega, ZOmega) -> (ZOmega, ZOmega)
opH_zomega (x,y) = (reduce_ZOmega (x+y), reduce_ZOmega (x-y))

-- | Apply a 'TwoLevel' operator to a 'ZOmega'-vector, represented as
-- a list. Throws an error if any operation produces a scalar that is
-- not in 'ZOmega'.
apply_twolevel_zomega :: TwoLevel -> [ZOmega] -> [ZOmega]
apply_twolevel_zomega (TL_X i j) w = transform_at2 opX_zomega i j w
apply_twolevel_zomega (TL_H i j) w = transform_at2 opH_zomega i j w
apply_twolevel_zomega (TL_T k i j) w = transform_at (omega_power k) j w
apply_twolevel_zomega (TL_omega k i) w = transform_at (omega_power k) i w

-- | Apply a list of 'TwoLevel' operators to a 'ZOmega'-vector,
-- represented as a list. Throws an error if any operation produces a
-- scalar that is not in 'ZOmega'.
apply_twolevels_zomega :: [TwoLevel] -> [ZOmega] -> [ZOmega]
apply_twolevels_zomega gs w = foldr apply_twolevel_zomega' w gs
  where apply_twolevel_zomega' g w = apply_twolevel_zomega g w

-- ----------------------------------------------------------------------
-- * Functions on residues

-- | The /residue type/ of /t/ ∈ ℤ[ω] is the residue of /t/[sup †]/t/.
-- It is 0000, 0001, or 1010.
data ResidueType = RT_0000 | RT_0001 | RT_1010
                                       deriving (Eq, Ord)

-- | Return the residue's 'ResidueType'.
residue_type :: Omega Z2 -> ResidueType
residue_type r = t where
  (t, _) = residue_type_shift r
  
-- | Return the residue's /shift/.
-- 
-- The shift is defined so that: 
-- 
-- * 0001, 1110, 0011 have shift 0,
-- 
-- * 0010, 1101, 0110 have shift 1,
-- 
-- * 0100, 1011, 1100 have shift 2, and
-- 
-- * 1000, 0111, 1001 have shift 3.
-- 
-- Residues of type 'RT_0000' have shift 0.
residue_shift :: Omega Z2 -> Int
residue_shift r = s where
  (_, s) = residue_type_shift r

-- | Return the residue's 'ResidueType' and the shift.
residue_type_shift :: Omega Z2 -> (ResidueType, Int)
residue_type_shift (Omega 0 0 0 0) = (RT_0000, 0)
residue_type_shift (Omega 0 0 0 1) = (RT_0001, 0)
residue_type_shift (Omega 0 0 1 0) = (RT_0001, 1)
residue_type_shift (Omega 0 0 1 1) = (RT_1010, 0)
residue_type_shift (Omega 0 1 0 0) = (RT_0001, 2)
residue_type_shift (Omega 0 1 0 1) = (RT_0000, 0)
residue_type_shift (Omega 0 1 1 0) = (RT_1010, 1)
residue_type_shift (Omega 0 1 1 1) = (RT_0001, 3)
residue_type_shift (Omega 1 0 0 0) = (RT_0001, 3)
residue_type_shift (Omega 1 0 0 1) = (RT_1010, 3)
residue_type_shift (Omega 1 0 1 0) = (RT_0000, 0)
residue_type_shift (Omega 1 0 1 1) = (RT_0001, 2)
residue_type_shift (Omega 1 1 0 0) = (RT_1010, 2)
residue_type_shift (Omega 1 1 0 1) = (RT_0001, 1)
residue_type_shift (Omega 1 1 1 0) = (RT_0001, 0)
residue_type_shift (Omega 1 1 1 1) = (RT_0000, 0)
residue_type_shift _ = undefined  -- to turn off a compiler warning

-- | Given two irreducible residues /a/ and /b/ of the same type, find
-- an index /m/ such that /a/ + ω[sup /m/]/b/ = 0000. If no such index
-- exists, find an index /m/ such that /a/ + ω[sup /m/]/b/ = 1111.
residue_offset :: Omega Z2 -> Omega Z2 -> Int
residue_offset a b = (residue_shift a - residue_shift b) `mod` 4

-- | Check whether a residue is reducible. A residue /r/ is called /reducible/
-- if it is of the form /r/ = √2 ⋅ /r/', i.e., /r/ ∈ {0000, 0101, 1010, 1111}.
reducible :: Omega Z2 -> Bool
reducible (Omega a b c d) = (a==c) && (b==d)

-- ----------------------------------------------------------------------
-- * Exact synthesis

-- | Perform a single row operation as in Lemma 4, applied to rows /i/
-- and /j/.  The entries at rows /i/ and /j/ are /x/ and /y/,
-- respectively, with respective residues /a/ and /b/. A precondition
-- is that /x/ and /y/ are of the same residue type. Returns a list of
-- two-level operations that decreases the denominator exponent.
row_step :: ((Index, Omega Z2, ZOmega), (Index, Omega Z2, ZOmega)) -> [TwoLevel]
row_step ((i,a,x), (j,b,y))
  | reducible a && reducible b = []
  | offs /= 0 = (TL_T offs i j) : row_step ((i,a,x), (j,b',y'))
  | otherwise = (TL_H i j) : row_step ((i,a1,x1), (j,b1,y1))
  where
    offs = residue_offset b a
    y' = omega_power (-offs) y
    b' = residue y'
    (x1,y1) = opH_zomega (x,y)
    (a1,b1) = residue (x1,y1)

-- | Row reduction: Given a unit column vector /v/, generate a
-- sequence of two-level operators that reduces the /i/th standard
-- basis vector /e/[sub /i/] to /v/. Any rows that are already 0 in
-- both vectors are guaranteed not to be touched.
reduce_column :: (Nat n) => Matrix n One (DOmega) -> Index -> [TwoLevel]
reduce_column v i = aux w k where
  vlist = list_of_vector (vector_head (unMatrix v))
  (w, k) = denomexp_decompose vlist
  aux w 0 = m1 ++ m2 where
    j = case findIndices (/= 0) w of
      [j] -> j
      _ -> error "reduce_column: not a unit vector"
    wj = w !! j
    l = case log_omega wj of
      Just l -> l
      Nothing -> error "reduce_column: not a unit vector"
    m1 = if i==j then [] else [TL_X i j]
    m2 = [TL_omega l i]
  aux w k = gates ++ aux w' (k-1) where
    res = residue w
    idx_res = zip3 [0..] res w
    res1010 = [ (i,a,x) | (i,a,x) <- idx_res, residue_type a == RT_1010 ]
    res0001 = [ (i,a,x) | (i,a,x) <- idx_res, residue_type a == RT_0001 ]
    res1010_pairs = case list_pairs res1010 of
      (p, Nothing) -> p
      _ -> error "reduce_column: not a unit vector"
    res0001_pairs = case list_pairs res0001 of
      (p, Nothing) -> p
      _ -> error "reduce_column: not a unit vector"
    m1010 = concat $ map row_step res1010_pairs
    m0001 = concat $ map row_step res0001_pairs
    gates = m1010 ++ m0001
    w' = map (reduce_ZOmega) (apply_twolevels_zomega (invert_twolevels gates) w)

-- | Input an exact /n/×/n/ unitary operator with coefficients in
-- [bold D][ω], and output an equivalent sequence of two-level
-- operators.  This is the algorithm from the Giles-Selinger paper. It
-- has superexponential complexity.
-- 
-- Note: the list of 'TwoLevel' operators will be returned in
-- right-to-left order, i.e., as in the mathematical notation for
-- matrix multiplication. This is the opposite of the quantum circuit
-- notation.
synthesis_nqubit :: (Nat n) => Matrix n n DOmega -> [TwoLevel]
synthesis_nqubit m = aux (unMatrix m) 0 where
  aux :: (Nat m) => Vector n (Vector m DOmega) -> Index -> [TwoLevel]
  aux Nil i = []
  aux (c `Cons` cs) i = gates ++ aux (unMatrix m') (i+1)
    where
      gates = reduce_column (column_matrix c) i
      gates_matrix = matrix_of_twolevels (invert_twolevels gates)
      m' = gates_matrix .*. (Matrix cs)
