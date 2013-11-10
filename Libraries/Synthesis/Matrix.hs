-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE IncoherentInstances #-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | This module provides fixed but arbitrary sized vectors and
-- matrices. The dimensions of the vectors and matrices are determined
-- by the type, for example,
-- 
-- > Matrix Two Three Complex
-- 
-- for complex 2×3-matrices. The type system ensures that there are no
-- run-time dimension errors.

module Libraries.Synthesis.Matrix where

import Libraries.Synthesis.Ring

-- ----------------------------------------------------------------------
-- * Type-level natural numbers
  
-- $ Note: with Haskell 7.4.2 data-kinds, this could be replaced by a
-- tighter definition; however, the following works just fine in
-- Haskell 7.2.

-- | Type-level representation of zero.
data Zero

-- | Type-level representation of successor.
data Succ a

-- | The natural number 1 as a type.
type One = Succ Zero

-- | The natural number 2 as a type.
type Two = Succ One

-- | The natural number 3 as a type.
type Three = Succ Two

-- | The natural number 4 as a type.
type Four = Succ Three

-- | The natural number 5 as a type.
type Five = Succ Four

-- | The natural number 6 as a type.
type Six = Succ Five

-- | The natural number 7 as a type.
type Seven = Succ Six

-- | The natural number 8 as a type.
type Eight = Succ Seven

-- | The natural number 9 as a type.
type Nine = Succ Eight

-- | The natural number 10 as a type.
type Ten = Succ Nine

-- | The 10th successor of a natural number type. For example, the
-- natural number 18 as a type is
-- 
-- > Ten_and Eight
type Ten_and a = Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ a)))))))))

-- | A data type for the natural numbers. Specifically, if /n/ is a
-- type-level natural number, then
-- 
-- > NNat n
-- 
-- is a singleton type containing only the natural number /n/.
data NNat :: * -> * where
  Zero :: NNat Zero
  Succ :: (Nat n) => NNat n -> NNat (Succ n)

-- | Convert an 'NNat' to an 'Integer'.
fromNNat :: NNat n -> Integer
fromNNat Zero = 0
fromNNat (Succ n) = 1 + fromNNat n

instance Show (NNat n) where
  show = show . fromNNat

-- | A type class for the natural numbers. The members are exactly the
-- type-level natural numbers.
class Nat n where
  -- | Return a term-level natural number corresponding to this
  -- type-level natural number.
  nnat :: NNat n
  
  -- | Return a term-level integer corresponding to this type-level
  -- natural number. The argument is just a dummy argument and is not
  -- evaluated.
  nat :: n -> Integer
  
instance Nat Zero where
  nnat = Zero
  nat n = 0
instance (Nat a) => Nat (Succ a) where
  nnat = Succ nnat
  nat n = 1 + nat (un n) where
    un :: Succ a -> a
    un = undefined

-- | Addition of type-level natural numbers.
type family Plus n m
type instance Zero `Plus` m = m
type instance (Succ n) `Plus` m = Succ (n `Plus` m)

-- | Multiplication of type-level natural numbers.
type family Times n m
type instance Zero `Times` m = Zero
type instance (Succ n) `Times` m = m `Plus` (n `Times` m)

-- ----------------------------------------------------------------------
-- * Fixed-length vectors

-- | @Vector /n/ /a/@ is the type of lists of length /n/ with elements
-- from /a/. We call this a \"vector\" rather than a tuple or list for
-- two reasons: the vectors are homogeneous (all elements have the
-- same type), and they are strict: if any one component is undefined,
-- the whole vector is undefined.
data Vector :: * -> * -> * where
  Nil :: Vector Zero a
  Cons :: !a -> !(Vector n a) -> Vector (Succ n) a

infixr 5 `Cons`

instance (Eq a) => Eq (Vector n a) where
  Nil == Nil = True
  Cons a as == Cons b bs = a == b && as == bs

instance (Show a) => Show (Vector n a) where
  show = show . list_of_vector

instance (ToDyadic a b) => ToDyadic (Vector n a) (Vector n b) where
  maybe_dyadic as = vector_sequence (vector_map maybe_dyadic as)

instance (WholePart a b) => WholePart (Vector n a) (Vector n b) where  
  from_whole = vector_map from_whole
  to_whole = vector_map to_whole
  
instance (DenomExp a) => DenomExp (Vector n a) where
  denomexp as = denomexp (list_of_vector as)
  denomexp_factor as k = vector_map (\a -> denomexp_factor a k) as
  
-- | Construct a vector of length 1.
vector_singleton :: a -> Vector One a
vector_singleton x = x `Cons` Nil

-- | Return the length of a vector. Since this information is
-- contained in the type, the vector argument is never evaluated and
-- can be a dummy (undefined) argument.
vector_length :: (Nat n) => Vector n a -> Integer
vector_length = nat . un where
  un :: Vector n a -> n
  un = undefined

-- | Convert a fixed-length list to an ordinary list.
list_of_vector :: Vector n a -> [a]
list_of_vector Nil = []
list_of_vector (Cons h t) = h : list_of_vector t

-- | Zip two equal length lists.
vector_zipwith :: (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
vector_zipwith f Nil Nil = Nil
vector_zipwith f (Cons a as) (Cons b bs) = Cons c cs where
  c = f a b
  cs = vector_zipwith f as bs

-- | Map a function over a fixed-length list.
vector_map :: (a -> b) -> Vector n a -> Vector n b
vector_map f Nil = Nil
vector_map f (Cons a as) = Cons (f a) (vector_map f as)

-- | Create the vector (0, 1, …, /n/-1).
vector_enum :: (Num a, Nat n) => Vector n a
vector_enum = aux nnat 0 where
  aux :: (Num a) => NNat n -> a -> Vector n a
  aux Zero a = Nil
  aux (Succ n) a = Cons a (aux n (a+1))

-- | Create the vector (/f/(0), /f/(1), …, /f/(/n/-1)).
vector_of_function :: (Num a, Nat n) => (a -> b) -> Vector n b
vector_of_function f = vector_map f vector_enum

-- | Construct a vector from a list. Note: since the length of the
-- vector is a type-level integer, it cannot be inferred from the
-- length of the input list; instead, it must be specified explicitly
-- in the type. It is an error to apply this function to a list of
-- the wrong length.
vector :: (Nat n) => [a] -> Vector n a
vector = aux nnat where
  aux :: NNat n -> [a] -> Vector n a
  aux Zero [] = Nil
  aux (Succ n) (h:t) = Cons h (aux n t)
  aux _ _ = error "vector: length mismatch"

-- | Return the /i/th element of the vector. Counting starts from 0.
-- Throws an error if the index is out of range.
vector_index :: (Integral i) => Vector n a -> i -> a
vector_index v i = list_of_vector v !! fromIntegral i

-- | Return a fixed-length list consisting of a repetition of the
-- given element. Unlike 'replicate', no count is needed, because this
-- information is already contained in the type. However, the type
-- must of course be inferable from the context.
vector_repeat :: (Nat n) => a -> Vector n a
vector_repeat x = vector_of_function (const x)

-- | Turn a list of columns into a list of rows.
vector_transpose :: (Nat m) => Vector n (Vector m a) -> Vector m (Vector n a)
vector_transpose Nil = vector_repeat Nil
vector_transpose (Cons a as) = vector_zipwith Cons a (vector_transpose as)

-- | Left strict fold over a fixed-length list.
vector_foldl :: (a -> b -> a) -> a -> Vector n b -> a
vector_foldl f x l = foldl f x (list_of_vector l)

-- | Right fold over a fixed-length list.
vector_foldr :: (a -> b -> b) -> b -> Vector n a -> b
vector_foldr f x l = foldr f x (list_of_vector l)

-- | Return the tail of a fixed-length list. Note that the type system
-- ensures that this never fails.
vector_tail :: Vector (Succ n) a -> Vector n a
vector_tail (Cons h t) = t

-- | Return the head of a fixed-length list. Note that the type system
-- ensures that this never fails.
vector_head :: Vector (Succ n) a -> a
vector_head (Cons h t) = h

-- | Append two fixed-length lists.
vector_append :: Vector n a -> Vector m a -> Vector (n `Plus` m) a
vector_append Nil v = v
vector_append (Cons h t) v = Cons h (vector_append t v)

-- | Version of 'sequence' for fixed-length lists.
vector_sequence :: (Monad m) => Vector n (m a) -> m (Vector n a)
vector_sequence Nil = return Nil
vector_sequence (Cons a as) = do
  a' <- a
  as' <- vector_sequence as
  return (Cons a' as')

-- ----------------------------------------------------------------------
-- * Matrices

-- | An /m/×/n/-matrix is a list of /n/ columns, each of which is a
-- list of /m/ scalars.  The type of square matrices of any fixed
-- dimension is an instance of the 'Ring' class, and therefore the
-- usual symbols, such as \"'+'\" and \"'*'\" can be used on
-- them. However, the non-square matrices, the symbols \"'.+.'\" and
-- \"'.*.'\" must be used.
data Matrix m n a = Matrix !(Vector n (Vector m a))
               deriving (Eq)

instance (Nat m, Show a) => Show (Matrix m n a) where
  show m = "Matrix" ++ string_of_rows rows where
    rows = from_matrix (matrix_transpose m)
    
    string_of_rows = string_of_list "(" "," ")" "()" string_of_elts
    string_of_elts = string_of_list "(" "," ")" "()" show
    
    string_of_list :: String -> String -> String -> String -> (t -> String) -> [t] -> String
    string_of_list lpar comma rpar nil string_of_elt lst =
      case lst of
        [] -> nil
        h:t -> lpar ++ string_of_elt h ++ string_of_tail t ++ rpar
      where string_of_tail lst =
              case lst of
                [] -> ""
                h:t -> comma ++ string_of_elt h ++ string_of_tail t
  
-- This is an overlapping instance.
instance (Nat m) => Show (Matrix m n DReal) where
  showsPrec = showsPrec_DenomExp
  
-- This is an overlapping instance.
instance (Nat m) => Show (Matrix m n DComplex) where
  showsPrec = showsPrec_DenomExp

-- This is an overlapping instance.
instance (Nat m) => Show (Matrix m n DOmega) where
  showsPrec = showsPrec_DenomExp
  
instance (ToDyadic a b) => ToDyadic (Matrix m n a) (Matrix m n b) where
  maybe_dyadic (Matrix a) = do
    b <- maybe_dyadic a
    return (Matrix b)

instance (WholePart a b) => WholePart (Matrix m n a) (Matrix m n b) where
  from_whole (Matrix m) = Matrix (from_whole m)
  to_whole (Matrix m) = Matrix (to_whole m)

instance (DenomExp a) => DenomExp (Matrix m n a) where
  denomexp (Matrix m) = denomexp m
  denomexp_factor (Matrix m) k = Matrix (denomexp_factor m k)

-- | Decompose a matrix into a list of columns.
unMatrix :: Matrix m n a -> (Vector n (Vector m a))
unMatrix (Matrix m) = m

-- | Return the size (/m/, /n/) of a matrix, where /m/ is the number
-- of rows, and /n/ is the number of columns. Since this information
-- is contained in the type, the matrix argument is not evaluated and
-- can be a dummy (undefined) argument.
matrix_size :: (Nat m, Nat n) => Matrix m n a -> (Integer, Integer)
matrix_size op = (nat (m op), nat (n op)) where
  m :: Matrix m n a -> m
  m = undefined
  n :: Matrix m n a -> n
  n = undefined

-- ----------------------------------------------------------------------
-- ** Basic matrix operations

-- | Addition of /m/×/n/-matrices. We use a special symbol because
-- /m/×/n/-matrices do not form a ring; only /n/×/n/-matrices form a
-- ring (in which case the normal symbol \"'+'\" also works).
(.+.) :: (Num a) => Matrix m n a -> Matrix m n a -> Matrix m n a
Matrix a .+. Matrix b = Matrix c where
  c = vector_zipwith (vector_zipwith (+)) a b

infixl 6 .+.

-- | Subtraction of /m/×/n/-matrices. We use a special symbol because
-- /m/×/n/-matrices do not form a ring; only /n/×/n/-matrices form a
-- ring (in which case the normal symbol \"'-'\" also works).
(.-.) :: (Num a) => Matrix m n a -> Matrix m n a -> Matrix m n a
Matrix a .-. Matrix b = Matrix c where
  c = vector_zipwith (vector_zipwith (-)) a b

infixl 6 .-.

-- | Map some function over every element of a matrix.
matrix_map :: (a -> b) -> Matrix m n a -> Matrix m n b
matrix_map f (Matrix a) = Matrix b where
  b = vector_map (vector_map f) a

-- | Create the matrix whose /i/,/j/-entry is (/i/,/j/). Here /i/ and
-- /j/ are 0-based, i.e., the top left entry is (0,0).
matrix_enum :: (Num a, Nat n, Nat m) => Matrix m n (a,a)
matrix_enum = Matrix (vector_of_function f) where
  f i = vector_of_function (\j -> (j,i))

-- | Create the matrix whose /i/,/j/-entry is @f i j@. Here /i/ and
-- /j/ are 0-based, i.e., the top left entry is @f 0 0@.
matrix_of_function :: (Num a, Nat n, Nat m) => (a -> a -> b) -> Matrix m n b
matrix_of_function f = matrix_map (uncurry f) matrix_enum

-- | Multiplication of a scalar and an /m/×/n/-matrix.
scalarmult :: (Num a) => a -> Matrix m n a -> Matrix m n a
scalarmult x m = matrix_map (x *) m

infixl 7 `scalarmult`

-- | Multiplication of /m/×/n/-matrices. We use a special symbol
-- because /m/×/n/-matrices do not form a ring; only /n/×/n/-matrices
-- form a ring (in which case the normal symbol \"'*'\" also works).
(.*.) :: (Num a, Nat m) => Matrix m n a -> Matrix n p a -> Matrix m p a
Matrix a .*. Matrix b = Matrix c where
  c = vector_map (a `mmv`) b
  
  mmv :: (Num a, Nat m) => Vector n (Vector m a) -> Vector n a -> Vector m a
  Nil `mmv` Nil = vector_repeat 0
  (Cons h Nil) `mmv` (Cons k Nil) = k `msv` h
  (Cons h t) `mmv` (Cons k s) = (k `msv` h) `avv` (t `mmv` s)
  
  msv :: (Num b) => b -> Vector n b -> Vector n b
  k `msv` h = vector_map (k*) h
  
  avv :: (Num c) => Vector n c -> Vector n c -> Vector n c
  v `avv` w = vector_zipwith (+) v w

infixl 7 .*.

-- | Return the 0 matrix of the given dimension.
null_matrix :: (Num a, Nat n, Nat m) => Matrix m n a
null_matrix = Matrix (vector_repeat (vector_repeat 0))

-- | Take the transpose of an /m/×/n/-matrix.
matrix_transpose :: (Nat m) => Matrix m n a -> Matrix n m a
matrix_transpose (Matrix a) = Matrix b where
  b = vector_transpose a

-- | Take the adjoint of an /m/×/n/-matrix. Unlike 'adj', this can be
-- applied to non-square matrices.
adjoint :: (Nat m, Adjoint a) => Matrix m n a -> Matrix n m a
adjoint (Matrix a) = Matrix c where
  b = vector_map (vector_map adj) a
  c = vector_transpose b
  
-- | Return the element in the /i/th row and /j/th column of the
-- matrix. Counting of rows and columns starts from 0. Throws an error
-- if the index is out of range.
matrix_index :: (Integral i) => Matrix m n a -> i -> i -> a
matrix_index (Matrix a) i j = a `vector_index` j `vector_index` i

-- | Return a list of all the entries of a matrix, in some fixed but
-- unspecified order.
matrix_entries :: Matrix m n a -> [a]
matrix_entries (Matrix m) = 
  concat $ map list_of_vector $ list_of_vector m

-- | Version of 'sequence' for matrices.
matrix_sequence :: (Monad m) => Matrix n p (m a) -> m (Matrix n p a)
matrix_sequence (Matrix m) = do
  m' <- vector_sequence (vector_map vector_sequence m)
  return (Matrix m')

-- | Return the trace of a square matrix.
tr :: (Ring a) => Matrix n n a -> a
tr (Matrix a) = aux a where
  aux :: (Num a) => Vector n (Vector n a) -> a
  aux Nil = 0
  aux ((h `Cons` t) `Cons` s) = h + aux (vector_map vector_tail s)

-- | Return the square of the Hilbert-Schmidt norm of an
-- /m/×/n/-matrix, defined by ‖/M/‖² = tr /M/[sup †]/M/.
hs_sqnorm :: (Ring a, Adjoint a, Nat n) => Matrix n m a -> a
hs_sqnorm m = tr (m .*. adjoint m)

-- ----------------------------------------------------------------------
-- Class instances for the ring of square matrices

instance (Num a, Nat n) => Num (Matrix n n a) where
  (+) = (.+.)
  (*) = (.*.)
  negate = scalarmult (-1)
  (-) = (.-.)
  fromInteger x = matrix_of_function (\i j -> if i == j then fromInteger x else 0)
  abs a = a
  signum a = 1
        
instance (Nat n, Adjoint a) => Adjoint (Matrix n n a) where
  adj (Matrix a) = Matrix c where
    b = vector_map (vector_map adj) a
    c = vector_transpose b

instance (Nat n, Adjoint2 a) => Adjoint2 (Matrix n n a) where
  adj2 (Matrix a) = Matrix b where
    b = vector_map (vector_map adj2) a

instance (HalfRing a, Nat n) => HalfRing (Matrix n n a) where
  half = scalarmult half 1

instance (RootHalfRing a, Nat n) => RootHalfRing (Matrix n n a) where
  roothalf = scalarmult roothalf 1

instance (RootTwoRing a, Nat n) => RootTwoRing (Matrix n n a) where
  roottwo = scalarmult roottwo 1

instance (ComplexRing a, Nat n) => ComplexRing (Matrix n n a) where
  i = scalarmult i 1

-- ----------------------------------------------------------------------
-- ** Operations on block matrices

-- | Stack matrices vertically.
stack_vertical :: Matrix m n a -> Matrix p n a -> Matrix (m `Plus` p) n a
stack_vertical (Matrix a) (Matrix b) = (Matrix c) where
  c = vector_zipwith vector_append a b

-- | Stack matrices horizontally.
stack_horizontal :: Matrix m n a -> Matrix m p a -> Matrix m (n `Plus` p) a
stack_horizontal (Matrix a) (Matrix b) = (Matrix c) where
  c = vector_append a b
  
-- | Repeat a matrix vertically, according to some vector of scalars.
tensor_vertical :: (Num a, Nat n) => Vector p a -> Matrix m n a -> Matrix (p `Times` m) n a
tensor_vertical v m = concat_vertical (vector_map (`scalarmult` m) v)
                               
-- | Vertically concatenate a vector of matrices.
concat_vertical :: (Num a, Nat n) => Vector p (Matrix m n a) -> Matrix (p `Times` m) n a
concat_vertical Nil = null_matrix
concat_vertical (Cons h t) = stack_vertical h (concat_vertical t)

-- | Repeat a matrix horizontally, according to some vector of scalars.
tensor_horizontal :: (Num a, Nat m) => Vector p a -> Matrix m n a -> Matrix m (p `Times` n) a
tensor_horizontal v m = concat_horizontal (vector_map (`scalarmult` m) v)
  
-- | Horizontally concatenate a vector of matrices.
concat_horizontal :: (Num a, Nat m) => Vector p (Matrix m n a) -> Matrix m (p `Times` n) a
concat_horizontal Nil = null_matrix
concat_horizontal (Cons h t) = stack_horizontal h (concat_horizontal t)

-- | Kronecker tensor of two matrices.
tensor :: (Num a, Nat n, Nat (p `Times` m)) => Matrix p q a -> Matrix m n a -> Matrix (p `Times` m) (q `Times` n) a
tensor a b = ab3 where
  Matrix ab1 = matrix_map (`scalarmult` b) a
  ab2 = vector_map concat_vertical ab1
  ab3 = concat_horizontal ab2

-- | Form a diagonal block matrix.
oplus :: (Num a, Nat m, Nat q, Nat n, Nat p) => Matrix p q a -> Matrix m n a -> Matrix (p `Plus` m) (q `Plus` n) a
oplus (a :: Matrix p q a) (b :: Matrix m n a) = 
  (a `stack_vertical` (null_matrix :: Matrix m q a)) `stack_horizontal` ((null_matrix :: Matrix p n a) `stack_vertical` b)

-- | Form a controlled gate.
matrix_controlled :: (Eq a, Num a, Nat n) => Matrix n n a -> Matrix (n `Plus` n) (n `Plus` n) a
matrix_controlled (m :: Matrix n n a) = oplus (1 :: Matrix n n a) m

-- ----------------------------------------------------------------------
-- ** Constructors and destructors

-- | A convenient abbreviation for the type of 2×2-matrices.
type U2 a = Matrix Two Two a

-- | A convenient abbreviation for the type of 3×3-matrices.
type SO3 a = Matrix Three Three a

-- | A convenience constructor for matrices: turn a list of columns
-- into a matrix. 
-- 
-- Note: since the dimensions of the matrix are type-level integers,
-- they cannot be inferred from the dimensions of the input; instead,
-- they must be specified explicitly in the type. It is an error to
-- apply this function to a list of the wrong dimension.
matrix :: (Nat n, Nat m) => [[a]] -> Matrix n m a
matrix columns = Matrix m where
  m = vector $ map vector columns

-- | Turn a matrix into a list of columns.
from_matrix :: Matrix n m a -> [[a]]
from_matrix (Matrix m) = 
  map list_of_vector (list_of_vector m)

-- | A convenience constructor for 2×2-matrices. The arguments are by
-- rows.
matrix2x2 :: (a, a) -> (a, a) -> Matrix Two Two a
matrix2x2 (a, b) (c, d) = matrix [[a,c], [b,d]]

-- | A convenience destructor for 2×2-matrices. The result is by rows.
from_matrix2x2 :: Matrix Two Two a -> ((a, a), (a, a))
from_matrix2x2 (Matrix ((a `Cons` c `Cons` Nil) `Cons` (b `Cons` d `Cons` Nil) `Cons` Nil)) = ((a, b), (c, d))  

-- | A convenience constructor for 3×3-matrices. The arguments are by
-- rows.
matrix3x3 :: (a, a, a) -> (a, a, a) -> (a, a, a) -> Matrix Three Three a
matrix3x3 (a0, a1, a2) (b0, b1, b2) (c0, c1, c2) = 
  matrix [[a0, b0, c0], [a1, b1, c1], [a2, b2, c2]]

-- | A convenience constructor for 4×4-matrices. The arguments are by
-- rows.
matrix4x4 :: (a, a, a, a) -> (a, a, a, a) -> (a, a, a, a) -> (a, a, a, a) -> Matrix Four Four a
matrix4x4 (a0, a1, a2, a3) (b0, b1, b2, b3) (c0, c1, c2, c3) (d0, d1, d2, d3) = 
  matrix [[a0, b0, c0, d0], [a1, b1, c1, d1], [a2, b2, c2, d2], [a3, b3, c3, d3]]

-- | A convenience constructor for 3-dimensional column vectors.
column3 :: (a, a, a) -> Matrix Three One a
column3 (a, b, c) = matrix [[a, b, c]]

-- | A convenience destructor for 3-dimensional column vectors. This
-- is the inverse of 'column3'.
from_column3 :: Matrix Three One a -> (a, a, a)
from_column3 (Matrix ((a `Cons` b `Cons` c `Cons` Nil) `Cons` Nil)) = (a, b, c)

-- | A convenience constructor for turning a vector into a column matrix.
column_matrix :: Vector n a -> Matrix n One a
column_matrix v = Matrix (vector_singleton v)

-- ----------------------------------------------------------------------
-- ** Particular matrices

-- | Controlled-not gate.
cnot :: (Num a) => Matrix Four Four a
cnot = matrix4x4 (1,0,0,0)
                 (0,1,0,0)
                 (0,0,0,1)
                 (0,0,1,0)

-- | Swap gate.
swap :: (Num a) => Matrix Four Four a
swap = matrix4x4 (1,0,0,0)
                 (0,0,1,0)
                 (0,1,0,0)
                 (0,0,0,1)

-- | A /z/-rotation gate, /R/[sub /z/](θ) = [exp −/i/θ/Z/\/2].
zrot :: (Eq r, Floating r, Adjoint r) => r -> Matrix Two Two (Cplx r)
zrot theta = matrix2x2 (u, 0)
                       (0, adj u)
  where
    u = Cplx (cos (theta/2)) (-sin (theta/2))
