-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module provides a representation of the single-qubit
-- Clifford+/T/ operators, Matsumoto-Amano normal forms, and functions
-- for the exact synthesis of single-qubit Clifford+/T/ operators.
--
-- Matsumoto-Amano normal forms and the Matsumoto-Amano exact
-- synthesis algorithm are described in the paper:
--
-- * Ken Matsumoto, Kazuyuki Amano. Representation of Quantum Circuits
-- with Clifford and π\/8 Gates. <http://arxiv.org/abs/0806.3834>.

module Libraries.Synthesis.CliffordT where

import Libraries.Synthesis.Ring
import Libraries.Synthesis.Matrix
import Libraries.Synthesis.Clifford
import Libraries.Synthesis.MultiQubitSynthesis

import Data.List
import Data.Bits

-- ----------------------------------------------------------------------
-- * Clifford+/T/ interchange format

-- $ It is convenient to have a simple but exact \"interchange
-- format\" for operators in the single-qubit Clifford+/T/
-- group. Different operator representations can be converted to and
-- from this format.
--
-- Our format is simply a list of gates from /X/, /Y/, /Z/, /H/, /S/,
-- /T/, and /E/ = /H//S/[sup 3]ω[sup 3], with the obvious
-- interpretation as a matrix product. We also include the global
-- phase gate /W/ = ω = [exp /i/π\/4]. The /W/ gate is ignored when
-- converting to or from representations that cannot represent global
-- phase (such as the Bloch sphere representation).

-- | An enumeration type to represent symbolic basic gates (/X/, /Y/,
-- /Z/, /H/, /S/, /T/, /W/, /E/).
-- 
-- Note: when we use a list of 'Gate's to express a sequence of
-- operators, the operators are meant to be applied right-to-left,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
data Gate = X | Y | Z | H | S | T | E | W
          deriving (Show, Eq)

-- | A type class for all things that can be exactly converted to a
-- list of gates. These are the exact representations of the
-- single-qubit Clifford+/T/ group.
class ToGates a where
  -- | Convert any suitable thing to a list of gates.
  to_gates :: a -> [Gate]

instance ToGates Gate where
  to_gates x = [x]

instance (ToGates a) => ToGates [a] where
  to_gates x = concat [ to_gates y | y <- x ]

instance ToGates Char where
  to_gates 'X' = [X]
  to_gates 'Y' = [Y]
  to_gates 'Z' = [Z]
  to_gates 'H' = [H]
  to_gates 'S' = [S]
  to_gates 'T' = [T]
  to_gates 'E' = [E]
  to_gates 'W' = [W]
  to_gates 'I' = []
  to_gates '-' = [W,W,W,W]
  to_gates 'i' = [W,W]
  to_gates x = error $ "to_gates[Char]: undefined -- " ++ (show x)

instance ToGates Axis where
  to_gates Axis_I = []
  to_gates Axis_H = [H]
  to_gates Axis_SH = [S,H]

instance ToGates Clifford where
  to_gates op = as ++ xs ++ ss ++ ws where
    (k, b, c, d) = clifford_decompose_coset op
    as = to_gates k
    xs  = replicate b X
    ss  = replicate c S
    ws  = replicate d W

-- | A type class for all things that a list of gates can be converted
-- to. For example, a list of gates can be converted to an element of
-- /U/(2) or an element of /SO/(3), using various (exact or
-- approximate) representations of the matrix entries.
class FromGates a where
  -- | Convert a list of gates to any suitable type.
  from_gates :: [Gate] -> a

instance FromGates String where
  from_gates = concat . map show

instance FromGates [Gate] where
  from_gates = id

-- | Invert a gate list.
invert_gates :: [Gate] -> [Gate]
invert_gates gs = aux [] gs where
  aux acc [] = acc
  aux acc (X:t) = aux (X:acc) t
  aux acc (Y:t) = aux (Y:acc) t
  aux acc (Z:t) = aux (Z:acc) t
  aux acc (H:t) = aux (H:acc) t
  aux acc (S:t) = aux (Z:S:acc) t
  aux acc (T:t) = aux (Z:S:T:acc) t
  aux acc (E:t) = aux (E:E:acc) t
  aux acc (W:t) = aux (W:W:W:W:W:W:W:acc) t

-- | Convert any precise format to any format.
convert :: (ToGates a, FromGates b) => a -> b
convert = from_gates . to_gates

-- ----------------------------------------------------------------------
-- * Matrices in /U/(2) and /SO/(3)

-- ----------------------------------------------------------------------
-- ** Matrices in /U/(2)

-- | The Pauli /X/ operator.
u2_X :: (Ring a) => U2 a
u2_X = matrix2x2 (0, 1)
                 (1, 0)

-- | The Pauli /Y/ operator.
u2_Y :: (ComplexRing a) => U2 a
u2_Y = matrix2x2 (0, -i)
                 (i,  0)

-- | The Pauli /Z/ operator.
u2_Z :: (Ring a) => U2 a
u2_Z = matrix2x2 (1,  0)
                 (0, -1)

-- | The Hadamard operator.
u2_H :: (RootHalfRing a) => U2 a
u2_H = roothalf * matrix2x2 (1,  1)
                            (1, -1)

-- | The /S/ operator.
u2_S :: (ComplexRing a) => U2 a
u2_S = matrix2x2 (1, 0)
                 (0, i)

-- | The /T/ operator.
u2_T :: (OmegaRing a) => U2 a
u2_T = matrix2x2 (1,     0)
                 (0, omega)

-- | The /E/ operator.
u2_E :: (OmegaRing a, RootHalfRing a) => U2 a
u2_E = roothalf * matrix2x2 (omega^3,  omega)
                            (omega^3, -omega)

-- | The /W/ = [exp /i/π\/4] global phase operator.
u2_W :: (OmegaRing a) => U2 a
u2_W = matrix2x2 (omega,     0)
                 (0,     omega)

-- | Convert a symbolic gate to the corresponding operator.
u2_of_gate :: (RootHalfRing a, ComplexRing a) => Gate -> U2 a
u2_of_gate X = u2_X
u2_of_gate Y = u2_Y
u2_of_gate Z = u2_Z
u2_of_gate H = u2_H
u2_of_gate S = u2_S
u2_of_gate T = u2_T
u2_of_gate E = u2_E
u2_of_gate W = u2_W

instance (RootHalfRing a, ComplexRing a) => FromGates (U2 a) where
  from_gates = product' . map u2_of_gate where
    product' = foldl' (*) 1

-- ----------------------------------------------------------------------
-- ** Matrices in /SO/(3)

-- $ This is the Bloch sphere representation of single qubit
-- operators.

-- | The Pauli /X/ operator.
so3_X :: (Ring a) => SO3 a
so3_X = matrix3x3 (1,  0,  0)
                  (0, -1,  0)
                  (0,  0, -1)

-- | The Pauli /Y/ operator.
so3_Y :: (Ring a) => SO3 a
so3_Y = matrix3x3 (-1, 0,  0)
                  ( 0, 1,  0)
                  ( 0, 0, -1)

-- | The Pauli /Z/ operator.
so3_Z :: (Ring a) => SO3 a
so3_Z = matrix3x3 (-1,  0, 0)
                  ( 0, -1, 0)
                  ( 0,  0, 1)

-- | The Hadamard operator.
so3_H :: (Ring a) => SO3 a
so3_H = matrix3x3 (0,  0, 1)
                  (0, -1, 0)
                  (1,  0, 0)

-- | The operator /S/.
so3_S :: (Ring a) => SO3 a
so3_S = matrix3x3 (0, -1, 0)
                  (1,  0, 0)
                  (0,  0, 1)

-- | The operator /E/.
so3_E :: (Ring a) => SO3 a
so3_E = matrix3x3 (0, 0, 1)
                  (1, 0, 0)
                  (0, 1, 0)

-- | The /T/ operator.
so3_T :: (RootHalfRing a) => SO3 a
so3_T = matrix3x3 (r, -r,  0)
                  (r,  r,  0)
                  (0,  0,  1)
  where r = roothalf

-- | Convert a symbolic gate to the corresponding Bloch sphere
-- operator.
so3_of_gate :: (RootHalfRing a) => Gate -> SO3 a
so3_of_gate X = so3_X
so3_of_gate Y = so3_Y
so3_of_gate Z = so3_Z
so3_of_gate H = so3_H
so3_of_gate S = so3_S
so3_of_gate T = so3_T
so3_of_gate E = so3_E
so3_of_gate W = 1

instance (RootHalfRing a) => FromGates (SO3 a) where
  from_gates = product . map so3_of_gate

-- ----------------------------------------------------------------------
-- ** Conversions

-- | Conversion from /U/(2) to /SO/(3).
so3_of_u2 :: (Adjoint a, ComplexRing a, RealPart a b, HalfRing b) => U2 a -> SO3 b
so3_of_u2 u = matrix_of_function f where
  f i j = half * (real $ tr (sigma i * u * sigma j * adj u))
  sigma 0 = u2_X
  sigma 1 = u2_Y
  sigma 2 = u2_Z
  sigma _ = error "so3_of_u2" -- not reached

-- | Convert a Clifford operator to a matrix in /SO/(3).
so3_of_clifford :: (ToClifford a, Ring b) => a -> SO3 b
so3_of_clifford m = so3_E^a * so3_X^b * so3_S^c where
  (a,b,c,d) = clifford_decompose m

-- | Convert a matrix in /SO/(3) to a Clifford gate. Throw an error if
-- the matrix isn't Clifford.
clifford_of_so3 :: (Ring a, Eq a, Adjoint a) => SO3 a -> Clifford
clifford_of_so3 m = case from_matrix m of
  [_, _, [ 1, 0, 0]] -> with "H"
  [_, _, [-1, 0, 0]] -> with "HX"
  [_, _, [ 0, 1, 0]] -> with "SH"
  [_, _, [ 0,-1, 0]] -> with "SHX"
  [_, _, [ 0, 0,-1]] -> with "X"
  [_, [-1, 0, 0], _] -> with "S"
  [_, [ 0,-1, 0], _] -> with "SS"
  [_, [ 1, 0, 0], _] -> with "SSS"
  [[1, 0, 0], [0, 1, 0], [0, 0, 1]] -> clifford_id
  _ -> error "clifford_of_so3: not a Clifford operator"
  where
    with s = op `clifford_mult` op1 where
      op = to_clifford s
      m1 = adj (so3_of_clifford op) * m
      op1 = clifford_of_so3 m1

instance (Ring a, Eq a, Adjoint a) => ToClifford (SO3 a) where
  to_clifford = clifford_of_so3

-- ----------------------------------------------------------------------
-- * Matsumoto-Amano normal forms

-- $ A Matsumoto-Amano normal form is a sequence of Clifford+/T/
-- operators that is of the form
--
-- * (ε | /T/) (/HT/ | /SHT/)[sup *] /C/.
--
-- Here, ε is the empty sequence, /C/ is any Clifford operator, and
-- the meanings of @\"|\"@ and @\"*\"@ are as for regular
-- expressions. Every single-qubit Clifford+/T/ operator has a unique
-- Matsumoto-Amano normal form.

-- ----------------------------------------------------------------------
-- ** Representation of normal forms

-- | A representation of normal forms, optimized for right
-- multiplication.
data NormalForm = NormalForm Syllables Clifford
                  deriving (Eq)

-- | Syllables is a circuit of the form (ε|/T/) (/HT/|/SHT/)[sup *].
data Syllables =
  S_I                  -- ^ The empty sequence ε.
  | S_T                -- ^ The sequence /T/.
  | SApp_HT Syllables  -- ^ A sequence of the form …/HT/.
  | SApp_SHT Syllables -- ^ A sequence of the form …/SHT/.
            deriving (Eq, Show)

instance ToGates NormalForm where
  to_gates (NormalForm ts c) = to_gates ts ++ to_gates c

instance ToGates Syllables where
  to_gates S_I = []
  to_gates S_T = [T]
  to_gates (SApp_HT ts) = to_gates ts ++ [H, T]
  to_gates (SApp_SHT ts) = to_gates ts ++ [S, H, T]

instance Show NormalForm where
  show x = case to_gates x of
    [] -> "ε"
    gs -> concat $ map show gs

-- | Right-multiply the given normal form by a gate.
normalform_append :: NormalForm -> Gate -> NormalForm
normalform_append (NormalForm ts c) X =
  NormalForm ts (c `clifford_mult` clifford_X)
normalform_append (NormalForm ts c) Y =
  NormalForm ts (c `clifford_mult` clifford_Y)
normalform_append (NormalForm ts c) Z =
  NormalForm ts (c `clifford_mult` clifford_Z)
normalform_append (NormalForm ts c) H =
  NormalForm ts (c `clifford_mult` clifford_H)
normalform_append (NormalForm ts c) S =
  NormalForm ts (c `clifford_mult` clifford_S)
normalform_append (NormalForm ts c) E =
  NormalForm ts (c `clifford_mult` clifford_E)
normalform_append (NormalForm ts c) W =
  NormalForm ts (c `clifford_mult` clifford_W)
normalform_append (NormalForm ts c) T
  | k == Axis_H = NormalForm (SApp_HT ts) c'
  | k == Axis_SH = NormalForm (SApp_SHT ts) c'
  | otherwise = case ts of
      S_I -> NormalForm S_T c'
      S_T -> NormalForm S_I (clifford_S `clifford_mult` c')
      SApp_HT ts' -> NormalForm ts' (clifford_HS `clifford_mult` c')
      SApp_SHT ts' -> NormalForm ts' (clifford_SHS `clifford_mult` c')
  where
    (k, c') = clifford_tconj c
    clifford_HS = to_clifford "HS"
    clifford_SHS = to_clifford "SHS"

-- ----------------------------------------------------------------------
-- ** Group operations on normal forms

-- | The identity as a normal form.
nf_id :: NormalForm
nf_id = NormalForm S_I clifford_id

-- | Multiply two normal forms. The right factor can be any
-- 'ToGates'.
nf_mult :: (ToGates b) => NormalForm -> b -> NormalForm
nf_mult a b = foldl' normalform_append a (to_gates b)

-- | Invert a normal form. The input can be any 'ToGates'.
nf_inv :: (ToGates a) => a -> NormalForm
nf_inv = from_gates . invert_gates . to_gates

-- ----------------------------------------------------------------------
-- ** Conversion to normal form

-- | Convert any 'ToGates' list to a 'NormalForm', thereby normalizing it.
normalize :: (ToGates a) => a -> NormalForm
normalize = nf_mult nf_id

instance FromGates NormalForm where
  from_gates = normalize

-- ----------------------------------------------------------------------
-- * Exact synthesis

-- ----------------------------------------------------------------------
-- ** Synthesis from /SO/(3)

-- | Input an exact matrix in /SO/(3), and output the corresponding
-- Clifford+/T/ normal form. It is an error if the given matrix is not
-- an element of /SO/(3), i.e., orthogonal with determinant 1.
--
-- This implementation uses the Matsumoto-Amano algorithm.
-- 
-- Note: the list of gates will be returned in right-to-left order,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
synthesis_bloch :: SO3 DReal -> [Gate]
synthesis_bloch m = aux m1 k
  where
    (m1, k) = denomexp_decompose m

    aux :: SO3 DInteger -> Integer -> [Gate]    
    aux m 0 = to_gates (clifford_of_so3 m)
    aux m k = to_gates axis ++ [T] ++ aux m4 (k-1)
      where
        Matrix p = matrix_map parity m
        v1 = vector_head p
        v2 = vector_head (vector_tail p)
        v = list_of_vector $ vector_zipwith (\x y -> x + y - x*y) v1 v2
        axis = case v of
          [1, 1, 0] -> Axis_I
          [0, 1, 1] -> Axis_H
          [1, 0, 1] -> Axis_SH
          _ -> error "synthesis_bloch: not unitary"
        m2 = adj (so3_of_clifford axis) * m
        m3 = adj sqrt2T * m2
        m4 = matrix_map half_DInteger m3
    sqrt2T = matrix3x3 (1, -1, 0) (1, 1, 0) (0, 0, roottwo)

    -- Divide a 'DInteger' of the form 2/a/ + 2/b/√2 by 2, or throw an
    -- error if it is not of the required form.
    half_DInteger :: DInteger -> DInteger
    half_DInteger (RootTwo a b)
      | even a && even b = RootTwo a' b'
      | otherwise = error "synthesis_bloch: not unitary"
      where
        a' = a `div` 2
        b' = b `div` 2

instance (ToEComplex a) => ToGates (SO3 a) where
  to_gates = synthesis_bloch . to_dyadic . matrix_map (to_real . toEComplex)
    where
      to_real (Cplx a 0) = a
      to_real _ = error "to_gates: not a real number"

-- ----------------------------------------------------------------------
-- ** Synthesis from /U/(2)

instance ToGates TwoLevel where
  to_gates (TL_X 0 1) = [X]
  to_gates (TL_X 1 0) = [X]
  to_gates (TL_H 0 1) = [H]
  to_gates (TL_H 1 0) = [X,H,X]
  to_gates (TL_T k 0 1)
    | k `mod` 2 == 1 = [T] ++ to_gates (TL_T (k-1) 0 1)
    | k `mod` 4 == 2 = [S] ++ to_gates (TL_T (k-2) 0 1)
    | k `mod` 8 == 4 = [Z]
    | otherwise = []
  to_gates (TL_T k 1 0) = [X] ++ to_gates (TL_T k 0 1) ++ [X]
  to_gates (TL_omega k 1) = to_gates (TL_T k 0 1)
  to_gates (TL_omega k 0) = to_gates (TL_T k 1 0)
  to_gates _ = error $ "ToGates TwoLevel: invalid gate"

-- | Input an exact matrix in /U/(2), and output the corresponding
-- Clifford+/T/ normal form. The behavior is undefined if the given
-- matrix is not an element of /U/(2), i.e., unitary with determinant
-- 1.
--
-- We use a variant of the Kliuchnikov-Maslov-Mosca algorithm, as
-- implemented in "Libraries.Synthesis.MultiQubitSynthesis".
-- 
-- Note: the list of gates will be returned in right-to-left order,
-- i.e., as in the mathematical notation for matrix multiplication.
-- This is the opposite of the quantum circuit notation.
synthesis_u2 :: U2 DOmega -> [Gate]
synthesis_u2 = to_gates . normalize . synthesis_nqubit

instance (ToEComplex a) => ToGates (U2 a) where
  to_gates = synthesis_u2 . matrix_map (fromDComplex . to_dyadic . toEComplex)

-- ----------------------------------------------------------------------
-- * Compact representation of normal forms

-- $ It is sometimes useful to store Clifford+/T/ operators in a file;
-- for this purpose, we provide a very succinct encoding of
-- Clifford+/T/ operators as bit strings, which are in turns
-- represented as integers.
--
-- Our bitwise encoding is as follows. The first regular expression
-- represents the set of Matsumoto-Amano normal forms (with a
-- particular presentation of the rightmost Clifford operator). The
-- second regular expression, which has the same form, defines the
-- corresponding bit string encoding.
--
-- * (ε|/T/) (/HT/|/SHT/)[sup *] (ε|/H/|/SH/) (ε|/X/) (ε|/S²/) (ε|/S/) (ε|ω⁴) (ε|ω²) (ε|ω)
--
-- * (10|11) (0|1)[sup *] (00|01|10) (0|1) (0|1) (0|1) (0|1) (0|1) (0|1)
--
-- As a special case, the leading bits 10 are omitted in case the
-- encoded operator is a Clifford operator. This ensures that the
-- encoding of a Clifford operator is an integer from 0 to 191.
-- 
-- This format has the property that the encoded Clifford+/T/
-- operator can, in principle, be read off directly from the hexadecimal
-- representation of the bit string, with the following decoding:
--
-- Leftmost one or two hexadecimal digits:
--
-- >  0 = n/a             4 = HT              8 = HTHT            c = THTHT
-- >  1 = see below       5 = SHT             9 = HTSHT           d = THTSHT
-- >  2 = ε               6 = THT             a = SHTHT           e = TSHTHT
-- >  3 = T               7 = TSHT            b = SHTSHT          f = TSHTSHT
-- >
-- >  10 = HTHTHT         14 = SHTHTHT        18 = THTHTHT        1c = TSHTHTHT
-- >  11 = HTHTSHT        15 = SHTHTSHT       19 = THTHTSHT       1d = TSHTHTSHT
-- >  12 = HTSHTHT        16 = SHTSHTHT       1a = THTSHTHT       1e = TSHTSHTHT
-- >  13 = HTSHTSHT       17 = SHTSHTSHT      1b = THTSHTSHT      1f = TSHTSHTSHT
--
-- Central hexadecimal digit:
--
-- >  0 = HTHTHTHT        4 = HTSHTHTHT       8 = SHTHTHTHT       c = SHTSHTHTHT
-- >  1 = HTHTHTSHT       5 = HTSHTHTSHT      9 = SHTHTHTSHT      d = SHTSHTHTSHT
-- >  2 = HTHTSHTHT       6 = HTSHTSHTHT      a = SHTHTSHTHT      e = SHTSHTSHTHT
-- >  3 = HTHTSHTSHT      7 = HTSHTSHTSHT     b = SHTHTSHTSHT     f = SHTSHTSHTSHT
--
-- Second-to-rightmost hexadecimal digit:
--
-- >  0 = ε               4 = H               8 = SH              c = n/a
-- >  1 = SS              5 = HSS             9 = SHSS            d = n/a
-- >  2 = X               6 = HX              a = SHX             e = n/a
-- >  3 = XSS             7 = HXSS            b = SHXSS           f = n/a
--
-- Rightmost hexadecimal digit:
--
-- >  0 = ε               4 = ω⁴              8 = S               c = Sω⁴
-- >  1 = ω               5 = ω⁵              9 = Sω              d = Sω⁵
-- >  2 = ω²              6 = ω⁶              a = Sω²             e = Sω⁶
-- >  3 = ω³              7 = ω⁷              b = Sω³             f = Sω⁷
--
-- For example, the hexadecimal integer
--
-- > 6bf723e31
--
-- encodes the Clifford+/T/ operator
--
-- > THT SHTHTSHTSHT SHTSHTSHTSHT HTSHTSHTSHT HTHTSHTHT HTHTSHTSHT SHTSHTSHTHT XSS ω.

-- | Compactly encode a 'NormalForm' as an 'Integer'.
normalform_pack :: NormalForm -> Integer
normalform_pack (NormalForm S_I op) = clifford_pack op
normalform_pack (NormalForm s op) = 256 * syllables_pack s + clifford_pack op
  where
    syllables_pack :: Syllables -> Integer
    syllables_pack S_I = 2
    syllables_pack S_T = 3
    syllables_pack (SApp_HT s) = (syllables_pack s `shiftL` 1) + 0
    syllables_pack (SApp_SHT s) = (syllables_pack s `shiftL` 1) + 1

-- | Decode a 'NormalForm' from its 'Integer' encoding. This is the
-- inverse of 'normalform_pack'.
normalform_unpack :: Integer -> NormalForm
normalform_unpack n 
  | n < 0 = error "normalform_unpack: invalid encoding"
  | n < 192 = NormalForm S_I op
  | n < 768 = error "normalform_unpack: invalid encoding"
  | otherwise = NormalForm s op 
  where
    s = syllables_unpack (n `shiftR` 8)
    op = clifford_unpack (n .&. 0xff)

    syllables_unpack :: Integer -> Syllables
    syllables_unpack 0 = error "normalform_unpack: invalid encoding"
    syllables_unpack 1 = error "normalform_unpack: invalid encoding"
    syllables_unpack 2 = S_I
    syllables_unpack 3 = S_T
    syllables_unpack n
      | even n     = SApp_HT s
      | otherwise  = SApp_SHT s
      where
        s = syllables_unpack (n `shiftR` 1)

-- | Encode a Clifford operator as an integer in the range 0−191.
clifford_pack :: Clifford -> Integer
clifford_pack op = toInteger (64 * encode k + 32*b + 8*c + d)
  where
    (k, b, c, d) = clifford_decompose_coset op
    encode Axis_I = 0
    encode Axis_H = 1
    encode Axis_SH = 2

-- | Decode a Clifford operator from its integer encoding. This is the
-- inverse of 'clifford_pack'
clifford_unpack :: Integer -> Clifford
clifford_unpack n 
  | n < 0 || n > 191 = error "clifford_unpack: invalid encoding"
  | otherwise = decode k * (clifford_X^b) * (clifford_S^c) * (clifford_W^d)
  where
    d = n .&. 0x7
    c = (n `shiftR` 3) .&. 0x3
    b = (n `shiftR` 5) .&. 0x1
    k = (n `shiftR` 6) .&. 0x3
    decode 0 = clifford_id
    decode 1 = clifford_H
    decode _ = clifford_SH
    (*) = clifford_mult
    (^) x n = foldl (*) clifford_id (genericReplicate n x)

instance ToGates Integer where
  to_gates = to_gates . normalform_unpack

instance FromGates Integer where
  from_gates = normalform_pack . from_gates
