-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module contains a data type to represent the four Pauli operators,
-- along with various operations on them, including commutativity relations.
module Libraries.Stabilizers.Pauli where

import Prelude hiding (negate)
import Quantum.Synthesis.Ring (Cplx (..), i)

-- | The Pauli operators can be used to generate a stabilizer group for
-- the Clifford operators.
data Pauli = I | X | Y | Z deriving (Show,Eq)

-- | The generators of a stabilizer group require a sign.
data Sign = Plus | Minus deriving (Ord,Eq)

instance Show Sign where
 show Plus = "+"
 show Minus = "-"

-- | Returns a boolean as to whether a 'Sign' is negative (i.e.. 'Minus').
negative :: Sign -> Bool
negative Plus = False
negative Minus = True

-- | Returns the negation of a 'Sign'.
negate :: Sign -> Sign
negate Plus = Minus
negate Minus = Plus

-- | Two signs can be multiplied.
multiply_sign :: Sign -> Sign -> Sign
multiply_sign Plus s = s
multiply_sign Minus s = negate s

--------------------------------------
-- Helper Functions for Commutation --
--------------------------------------

-- | In general, Pauli operators can commute, or anti-commute, so we
-- need to add signs or ±/i/.
data SignPlus = MinusI | PlusI | One Sign

instance Show SignPlus where
  show (One x) = " " ++ show x
  show PlusI = "+i"
  show MinusI = "-i"

-- | Two 'signPlus's can be multiplied.
multiply_signPlus :: SignPlus -> SignPlus -> SignPlus
multiply_signPlus (One Plus) s = s
multiply_signPlus (One Minus) (One Minus) = One Plus
multiply_signPlus (One Minus) PlusI = MinusI
multiply_signPlus (One Minus) MinusI = PlusI
multiply_signPlus PlusI PlusI = One Minus
multiply_signPlus PlusI MinusI = One Plus
multiply_signPlus MinusI MinusI = One Minus
multiply_signPlus s1 s2 = multiply_signPlus s2 s1

-- | Extract a 'Sign' embedded in a 'SignPlus', or throw an error
-- if the argument is not an embedded 'Sign'.
signPlus_to_sign :: SignPlus -> Sign
signPlus_to_sign (One s) = s
signPlus_to_sign _ = error "signPlus_to_sign: i in sign"

-- | The Levi-Civita symbol, for the permutations of three Pauli operators.
levi_civita :: Pauli -> Pauli -> Pauli -> SignPlus
levi_civita X Y Z = PlusI
levi_civita X Z Y = MinusI
levi_civita Y X Z = MinusI
levi_civita Y Z X = PlusI
levi_civita Z X Y = PlusI
levi_civita Z Y X = MinusI
levi_civita _ _ _ = One Plus

-- | The Kronecker delta for two Pauli operators.
kronecker_delta :: Pauli -> Pauli -> Bool
kronecker_delta x y = x == y

-- | The combination of the commutation and anti-commutation operators can
-- be used to essentially multiply an (ordered) pair of Pauli operators.
commute :: Pauli -> Pauli -> (SignPlus,Pauli)
commute I p = (One Plus,p)
commute p I = (One Plus,p)
commute x y = 
 if kronecker_delta x y then (One Plus,I) 
 else case (levi_civita x y X,levi_civita x y Y,levi_civita x y Z) of
       (s,One _,One _) -> (s,X)
       (One _,s,One _) -> (s,Y)
       (One _,One _,s) -> (s,Z)
       _ -> error "commute: Impossible clause reached, somehow"

-- map (\(x,y) -> (x,y,commute x y)) [(x,y) | x <- [I,X,Y,Z], y <- [I,X,Y,Z]]
-- [(I,I,( +,I)),(I,X,( +,X)),(I,Y,( +,Y)),(I,Z,( +,Z)),(X,I,( +,X)),(X,X,( +,I)),(X,Y,(+i,Z)),(X,Z,(-i,Y)),(Y,I,( +,Y)),(Y,X,(-i,Z)),(Y,Y,( +,I)),(Y,Z,(+i,X)),(Z,I,( +,Z)),(Z,X,(+i,Y)),(Z,Y,(-i,X)),(Z,Z,( +,I))]

-- | Represent a 2×2-matrix as a 4-tuple.
type Matrix1 a = (a,a,a,a)



-- | Give the matrix for each Pauli operator.
toMatrix1 :: (Floating r) => Pauli -> Matrix1 (Cplx r)
toMatrix1 I = (1,0,0,1)
toMatrix1 X = (0,1,1,0)
toMatrix1 Y = (0,-i,i,0)
toMatrix1 Z = (1,0,0,-1)

-- | Scale a 2-by-2 matrix.
scale1 :: (Num a) => a -> Matrix1 a -> Matrix1 a
scale1 x (a,b,c,d) = (x*a,x*b,x*c,x*d)

-- | If a matrix is Pauli, then return the Pauli operator, otherwise
-- throw an error.
fromMatrix1 :: (Floating r, Eq r,Show r) => Matrix1 (Cplx r) -> (Sign,Pauli)
fromMatrix1 m = case filter (\(b,_) -> b) [(toMatrix1 x == m,x) | x <- ixyz] of
  [(_,p)] -> (Plus,p)
  _ -> case filter (\(b,_) -> b) [((scale1 (-1) (toMatrix1 x)) == m,x) | x <- ixyz] of
        [(_,p)] -> (Minus,p)
        _ -> error ("fromMatrix1: " ++ show m ++ " is not a pauli matrix")
 where
  ixyz = [I,X,Y,Z]

-- | Matrix multiplication for 2×2-matrices.
multiplyMatrix1 :: (Num a) => Matrix1 a -> Matrix1 a -> Matrix1 a
multiplyMatrix1 (a00,a01,a10,a11) (b00,b01,b10,b11) = (c00,c01,c10,c11)
 where
  c00 = a00*b00 + a01*b10
  c01 = a00*b01 + a01*b11
  c10 = a10*b00 + a11*b10
  c11 = a10*b01 + a11*b11

-- | Compute the transpose of a 2×2 complex-valued matrix.
transpose1 :: (Num r) => Matrix1 (Cplx r) -> Matrix1 (Cplx r)
transpose1 (a00,a01,a10,a11) = (conjugate a00, conjugate a10, conjugate a01, conjugate a11)
 where
  conjugate (Cplx a b) = Cplx a (-b) 

-- | Return the matrix for Pauli-/Y/, which is /iXZ/.
my_Y :: (Floating r) => Matrix1 (Cplx r)
my_Y = scale1 i $ multiplyMatrix1 (toMatrix1 X) (toMatrix1 Z)

-- | A 4×4-matrix is represented as a 2×2-matrix of 2×2-matrices.
type Matrix2 a = Matrix1 (Matrix1 a)

-- | The tensor product of two 2×2-matrices is a 4×4 matrix.
tensor1 :: (Num a) => Matrix1 a -> Matrix1 a -> Matrix2 a
tensor1 (a,b,c,d) m = (scale1 a m,scale1 b m,scale1 c m,scale1 d m) 

-- | A controlled operation can be expressed with just the operation to be controlled.
control1 :: (Num a) => Matrix1 a -> Matrix2 a
control1 m1 = ((1,0,0,1),(0,0,0,0),(0,0,0,0),m1)

-- | Take the tensor of a pair of Pauli operators, and return a 4×4 matrix.
toMatrix2 :: (Floating r) => (Pauli,Pauli) -> Matrix2 (Cplx r)
toMatrix2 (x,y) = tensor1 (toMatrix1 x) (toMatrix1 y)

-- | Scale a 4×4 matrix.
scale2 :: (Num a) => a -> Matrix2 a -> Matrix2 a
scale2 x (a,b,c,d) = (scale1 x a,scale1 x b,scale1 x c,scale1 x d)

-- | If a matrix is the tensor product of two Pauli operators, then
-- return the pair of Pauli operators, otherwise throw an error.
fromMatrix2 :: (Floating r, Eq r, Show r) => Matrix2 (Cplx r) -> (Sign,Pauli,Pauli)
fromMatrix2 m = case filter (\(b,_) -> b) [(toMatrix2 (x,y)  == m,(x,y)) | x <- ixyz, y <- ixyz] of
  [(_,(p1,p2))] -> (Plus,p1,p2)
  _ -> case filter (\(b,_) -> b) [(scale2 (-1) (toMatrix2 (x,y))  == m,(x,y)) | x <- ixyz, y <- ixyz] of
      [(_,(p1,p2))] -> (Minus,p1,p2)
      _ -> error ("fromMatrix2: " ++ show m ++ " is not a tensor product of two Pauli matrices")
 where
  ixyz = [I,X,Y,Z]

-- | Matrix multiplication for 4×4 matrices.
multiplyMatrix2 :: (Num a) => Matrix2 a -> Matrix2 a -> Matrix2 a
multiplyMatrix2 ((a00,a01,a10,a11),(a02,a03,a12,a13),(a20,a21,a30,a31),(a22,a23,a32,a33)) ((b00,b01,b10,b11),(b02,b03,b12,b13),(b20,b21,b30,b31),(b22,b23,b32,b33)) = ((c00,c01,c10,c11),(c02,c03,c12,c13),(c20,c21,c30,c31),(c22,c23,c32,c33))
 where
  c00 = a00*b00 + a01*b10 + a02*b20 + a03*b30
  c01 = a00*b01 + a01*b11 + a02*b21 + a03*b31
  c02 = a00*b02 + a01*b12 + a02*b22 + a03*b32
  c03 = a00*b03 + a01*b13 + a02*b23 + a03*b33
  c10 = a10*b00 + a11*b10 + a12*b20 + a13*b30
  c11 = a10*b01 + a11*b11 + a12*b21 + a13*b31
  c12 = a10*b02 + a11*b12 + a12*b22 + a13*b32
  c13 = a10*b03 + a11*b13 + a12*b23 + a13*b33
  c20 = a20*b00 + a21*b10 + a22*b20 + a23*b30
  c21 = a20*b01 + a21*b11 + a22*b21 + a23*b31
  c22 = a20*b02 + a21*b12 + a22*b22 + a23*b32
  c23 = a20*b03 + a21*b13 + a22*b23 + a23*b33
  c30 = a30*b00 + a31*b10 + a32*b20 + a33*b30
  c31 = a30*b01 + a31*b11 + a32*b21 + a33*b31
  c32 = a30*b02 + a31*b12 + a32*b22 + a33*b32
  c33 = a30*b03 + a31*b13 + a32*b23 + a33*b33

-- | The transpose of a 4×4 complex valued matrix.
transpose2 :: (Floating r) => Matrix2 (Cplx r) -> Matrix2 (Cplx r)
transpose2 ((a00,a01,a10,a11),(a02,a03,a12,a13),(a20,a21,a30,a31),(a22,a23,a32,a33)) = ((conjugate a00,conjugate a10,conjugate a01,conjugate a11),(conjugate a20,conjugate a30,conjugate a21,conjugate a31),(conjugate a02,conjugate a12,conjugate a03,conjugate a13),(conjugate a22,conjugate a32,conjugate a23,conjugate a33))
 where
  conjugate (Cplx a b) = Cplx a (-b) 

-- | The tensor product /IY/ can be defined by /i/(/IX/)(/IZ/).
my_IY :: (Floating r) => Matrix2 (Cplx r)  
my_IY = scale2 i $ multiplyMatrix2 (toMatrix2 (I,X)) (toMatrix2 (I,Z))
