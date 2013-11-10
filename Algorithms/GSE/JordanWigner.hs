-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides the Jordan-Wigner transformation and
-- symbolic derivation of circuit templates for second quantized
-- interaction terms. It is essentially a fully automated version of
-- the calculations from
-- 
-- * James D. Whitfield, Jacob Biamonte, and Alán
-- Aspuru-Guzik. \"Simulation of electronic structure Hamiltonians
-- using quantum computers.\" 
-- /Molecular Physics/ 109(5):735–750, 2011.
-- See also <http://arxiv.org/abs/1001.3855v3>.


module Algorithms.GSE.JordanWigner where

import Quipper

import QuipperLib.Decompose

import Data.Complex
import qualified Data.Map as Map
import Data.Map (Map)

import Libraries.Auxiliary (sequence_right_)

import Text.Printf

-- ----------------------------------------------------------------------
-- * Overview

-- $ For a given tuple of orbital indices, (/p/,/q/) in case of
-- one-electron interactions, or (/p/,/q/,/r/,/s/) in case of two-electron
-- interactions, we first calculate the Jordan-Wigner transformation
-- of the second quantized hermitian interaction terms
-- 
-- /a/[sub /p/][sup †]/a/[sub /p/], 
-- 
-- /a/[sub /p/][sup †]/a/[sub /q/] + /a/[sub /q/][sup †]/a/[sub /p/],
-- 
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /q/]/a/[sub /p/],
-- 
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /r/]/a/[sub /s/] + 
-- /a/[sub /s/][sup †]/a/[sub /r/][sup †]/a/[sub /q/]/a/[sub /p/].
-- 
-- Next, we decompose each operator into a linear combination /H/ =
-- λ[sub 1]/M/[sub 1] + ... + λ[sub /n/]/M/[sub /n/] of mutually
-- commuting hermitian tensors. At this point, each summand /M/[sub /j/]
-- in the linear combination will be a tensor product of the following
-- operators (not necessarily in this order):
-- 
-- * an even number (possibly zero) of Pauli /X/ operators;
-- 
-- * an even number (possibly zero) of Pauli /Y/ operators;
-- 
-- * zero or more Pauli /Z/ operators, and
-- 
-- * zero or more /D/ operators, where /D/ = σ[sup −]σ[sup +] = (/I/−/Z/)\/2.
-- 
-- Note that there may be zero terms in the summation; this happens,
-- for example, for 
-- /a/[sub /p/][sup †]/a/[sub /p/][sup †]/a/[sub /r/]/a/[sub /s/],
-- because two electrons cannot occupy the same spin orbital due to
-- their fermionic nature. In this case, /H/ = 0 and [exp -/i/θ/H/] = /I/.
-- 
-- Next, we calculate [exp -/i/θ/H/]. Because the summands /M/[sub /j/]
-- commute, we can exponentiate each summand separately, using the formula
-- [exp -/i/θ/H/] = [exp -/i/θλ[sub 1]/M/[sub 1]]⋯[exp -/i/θλ[sub /n/]/M/[sub /n/]].
-- 
-- We then generate the circuit for [exp -/i/θλ[sub /j/]/M/[sub /j/]]
-- by applying a sequence of basis changes until the problem is
-- reduced to a controlled rotation. The basis changes are, in this
-- order:
-- 
-- 1. Change each Pauli /X/ operator in /M/[sub /j/] to a Pauli /Z/
-- operator, and apply a Hadamard basis change to the corresponding
-- qubit. This uses the relation /HXH/ = /Z/.
-- 
-- 2. Change each Pauli /Y/ operator in /M/[sub /j/] to a Pauli /Z/
-- operator, and apply a [bold Y] basis change to the corresponding
-- qubit. Note: the [bold Y] basis change operator is defined in
-- [Whitfield et al.] as /R/[sub /x/](-π\/2) = (/I/+/iX/)\/√2, or
-- equivalently [bold Y] = /SHS/, and satisfies [bold Y][super †]/Y/[bold Y] =
-- /Z/. It should not be confused with the Pauli /Y/ operator.
-- 
-- 3. If the operator /M/[sub /j/] contains one or more Pauli /Z/ operators
-- (including those obtained in steps 1 and 2), then do a basis change
-- by a cascade of controlled-not gates to reduce this to a single /Z/
-- operator. This uses the relation /CNot/ (/Z/⊗/Z/) /CNot/ = /I/⊗/Z/.
-- 
-- After these basis changes, the operator /M/[sub /j/] consists of
-- exactly zero or one Pauli /Z/ operator, together with zero or more
-- /D/ operators.  To see how to translate this into a controlled
-- rotation, note that for any operator /A/, we have
-- 
-- \[image expDA.png]
-- 
-- Therefore, each /D/ operator in /M/[sub /j/] turns into a control
-- after exponentiation. The final rotation is then computed by
-- distinguishing two cases:
-- 
-- * If /M/[sub /j/] contains a Pauli /Z/ operator, then use the
-- relation [exp -/i/θ/Z/] = /R/[sub /z/](2θ). In this case, the circuit
-- for [exp -/i/θ/M/[sub /j/]] is a controlled /R/[sub /z/](2θ) gate in
-- the position of the /Z/ operator, with zero or more controls in the
-- positions of any /D/ operators.
-- 
-- * If /M/[sub /j/] does not contain a Pauli /Z/ operator, then the
-- operation to be performed is a phase change [exp -/i/θ], controlled
-- by the qubits in the positions of the /D/ operators. Note that
-- there must be at least one /D/ operator in this case. Also note
-- that a controlled [exp -/i/θ] gate is identical to a /T/(θ) gate.

-- ----------------------------------------------------------------------
-- * Correctness of the templates

-- $ As outlined above, the functions in this module generate each
-- circuit from first principles, based on the Jordan-Wigner
-- representation of operators and on algebraic transformations. They
-- do not rely on pre-fabricated circuit templates.
-- 
-- Based on the automated calculations provided by this module, we
-- have found small typos in the 5 templates provided by [Whitfield
-- et al.] (Table 3, or Table A1 in the arXiv version). 
-- 
-- * The template for the number-excitation operator is missing a
-- control on its rotation gate. 
-- 
-- * In the template for the Coulomb operator, the angles are wrong. 
-- Moreover, this program finds a simpler template.
-- 
-- * In the template for the double excitation operator, the angles
-- are wrong; they should be ±θ\/4 instead of θ.
-- 
-- The corrected templates generated by our code are as follows:
-- 
-- * Number operator /h/[sub /pp/] /a/[sub /p/][sup †]/a/[sub /p/].
-- 
-- > [image b0-template.png]
-- 
-- * Excitation operator /h/[sub /pq/] /a/[sub /p/][sup †]/a/[sub /q/].
-- 
-- > [image b1-template.png]
-- 
-- * Coulomb and exchange operators /h/[sub /pqqp/]
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /q/]/a/[sub /p/].
-- 
-- > [image b2-template.png]
-- 
-- * Number-excitation operator /h/[sub /pqqr/]
-- (/a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /q/]/a/[sub /r/] +
-- /a/[sub /r/][sup †]/a/[sub /q/][sup †]/a/[sub /q/]/a/[sub /p/]).
-- The sign of ±θ depends on the relative ordering of the indices /p,q,r/.
-- 
-- > [image b3-template.png]
-- 
-- * Double excitation operator 
-- /h/[sub /pqrs/]
-- (/a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /r/]/a/[sub /s/] +
-- /a/[sub /s/][sup †]/a/[sub /r/][sup †]/a/[sub /q/]/a/[sub /p/]).
-- The sign of ±θ\/4 in each of the eight terms depends on the relative ordering of the indices /p,q,r,s/.
-- 
-- > [image b4-template.png] 

-- ----------------------------------------------------------------------
-- * Alternate Coulomb templates

-- $ As noted above, our algorithm found the following template for the
-- Coulomb operator 
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /q/]/a/[sub /p/]:
-- 
-- > [image b2-template.png]
-- 
-- This is simpler than the template given in [Whitfield et al.], even
-- after one accounts for the cost of decomposing the additional
-- controlled /T/(θ) gate into elementary gates. However, an
-- equivalent circuit can also be given that is more similar to the
-- one in [Whitfield et al.] (but with corrected rotation angles):
-- 
-- > [image b2-orthodox.png]
-- 
-- We call this the \"orthodox\" template, because it is closer to the
-- one specified by Whitfield et al. The program will use the orthodox
-- template if the command line option @--orthodox@ is given, and it
-- will use the simplified template otherwise.

-- ----------------------------------------------------------------------
-- * General-purpose auxiliary functions

-- | Construct a list consisting of /n/ repetitions of some element.
power :: Int -> a -> [a]
power n x = take n $ repeat x

-- | Extract a list of /n/-1 consecutive pairs from an /n/-element list:
-- 
-- > consecutive_pairs [] = []
-- > consecutive_pairs [1] = []
-- > consecutive_pairs [1,2] = [(1,2)]
-- > consecutive_pairs [1,2,3] = [(1,2),(2,3)]
-- > consecutive_pairs [1,2,3,4] = [(1,2),(2,3),(3,4)]
consecutive_pairs :: [a] -> [(a,a)]
consecutive_pairs [] = []
consecutive_pairs [h] = []
consecutive_pairs (h1:h2:t) = (h1,h2) : consecutive_pairs (h2:t)

-- ----------------------------------------------------------------------
-- * Scalars          
          
-- | The type of complex numbers. Here, we use a floating point
-- representation, although a symbolic representation would also be
-- possible. Since for the purpose of this algorithm, all denominators
-- are powers of 2, the floating point representation is in fact exact.
type Scalar = Complex Double

-- | The complex number /i/.
i :: Scalar
i = 0 :+ 1

-- ----------------------------------------------------------------------
-- * Basic Gates

-- | Apply a /R/[sub z](θ)=[exp -/i/θ/Z/\/2] gate. The parameter θ is a
-- Bloch sphere angle.
-- 
-- \[image Rz.png]
rotZ_at :: Double -> Qubit -> Circ ()
rotZ_at theta q = named_rotation_at "Rz(%)" theta q

-- | Apply a /G/(θ) gate. This is a global phase change of [exp -/i/θ],
-- so this gate only \"does\" something when it is controlled.
-- Although it is logically a 0-ary gate, we give it a qubit argument
-- to specify where the gate can be drawn in circuit diagrams.
-- 
-- \[image G.png]
gse_G_at :: Double -> Qubit -> Circ ()
gse_G_at theta q = named_rotation_at "G(%)" theta q

-- | Apply a /T/(θ) gate. This is a /Z/-rotation, but differs
-- from /R/[sub z](-θ) by a global phase.
-- 
-- \[image T.png]
gse_T_at :: Double -> Qubit -> Circ ()
gse_T_at theta q = named_rotation_at "T(%)" theta q

-- | Apply a [bold Y] basis change gate. This is defined as [bold Y] = /SHS/, 
-- or equivalently,
-- 
-- \[image Y.png]
-- 
-- This should not be confused with the Pauli /Y/ gate.
gse_Y_at :: Qubit -> Circ ()
gse_Y_at q = named_gate_at "YY" q

-- ----------------------------------------------------------------------
-- * Basic operators

-- | This type provides a symbolic representation of certain
-- operators, generated by the Pauli operators, /P/ = σ[sup +], and
-- /M/ = σ[sup −]. For lack of a better term, we call these the
-- \"basic\" operators. Note that apart from /P/ and /M/, all of these
-- are hermitian.
data Op = 
  I -- ^ Identity operator.
  | X  -- ^ Pauli /X/ operator.  
  | Y  -- ^ Pauli /Y/ operator.
  | Z  -- ^ Pauli /Z/ operator.
  | P  -- ^ σ[sup +] operator = (0,1;0,0).
  | M  -- ^ σ[sup −] operator = (0,0;1,0).
  | A  -- ^ σ[sup +]σ[sup −] operator = (1,0;0,0).
  | D  -- ^ σ[sup −]σ[sup +] operator = (0,0;0,1).
  deriving (Show, Eq, Ord)

-- | A type to represent scalar multiples. An element of ('Scaled'
-- /a/) is a pair (λ, /x/) of a complex scalar λ and an element /x/ ∈
-- /a/. 
data Scaled a = Scaled Scalar a

-- | Multiplication of basic operators. Note that the product of two
-- basic operators is not usually itself a basic operator, but a
-- scalar multiple thereof. This multiplication encodes the algebraic
-- laws of basic operators in symbolic form.
          
-- Implementation note: the multiplication laws are currently
-- implemented as a long case distinction. Perhaps it could be done
-- more cleverly.
mult :: Op -> Op -> Scaled Op

-- The Pauli group
mult I x = Scaled 1 x
mult x I = Scaled 1 x

mult X X = Scaled 1 I
mult X Y = Scaled i Z
mult X Z = Scaled (-i) Y

mult Y X = Scaled (-i) Z
mult Y Y = Scaled 1 I
mult Y Z = Scaled i X

mult Z X = Scaled i Y
mult Z Y = Scaled (-i) X
mult Z Z = Scaled 1 I

-- P, M, D, and A
mult X P = Scaled 1 D
mult X M = Scaled 1 A
mult X A = Scaled 1 M
mult X D = Scaled 1 P

mult Y P = Scaled i D
mult Y M = Scaled (-i) A
mult Y A = Scaled i M
mult Y D = Scaled (-i) P

mult Z P = Scaled 1 P
mult Z M = Scaled (-1) M
mult Z A = Scaled 1 A
mult Z D = Scaled (-1) D

mult P X = Scaled 1 A
mult M X = Scaled 1 D
mult A X = Scaled 1 P
mult D X = Scaled 1 A

mult P Y = Scaled i A
mult M Y = Scaled (-i) D
mult A Y = Scaled (-i) P
mult D Y = Scaled i M

mult P Z = Scaled (-1) P
mult M Z = Scaled 1 M
mult A Z = Scaled 1 A
mult D Z = Scaled (-1) D

mult P P = Scaled 0 I
mult P M = Scaled 1 A
mult P A = Scaled 0 I
mult P D = Scaled 1 P
  
mult M P = Scaled 1 D
mult M M = Scaled 0 I
mult M A = Scaled 1 M
mult M D = Scaled 0 I
  
mult A P = Scaled 1 P
mult A M = Scaled 0 I
mult A A = Scaled 1 A
mult A D = Scaled 0 I
  
mult D P = Scaled 0 I
mult D M = Scaled 1 M
mult D A = Scaled 0 I
mult D D = Scaled 1 D
  
-- ----------------------------------------------------------------------
-- * Tensors of basic operators

-- | We use a list of basic operators to represent a tensor
-- product. The convention is that infinitely many identity operators
-- are implicitly appended at the end of the list.
type Tensor = [Op]

-- | Normalize a tensor, by stripping away trailing identities.
normalize_tensor :: Tensor -> Tensor
normalize_tensor [] = []
normalize_tensor (h:t) =
  if h == I && null n 
  then [] 
  else (h:n)
    where n = normalize_tensor t

-- | The identity tensor.
tensor_id :: Tensor
tensor_id = []

-- | Multiply two tensors. This returns a scaled tensor.
mult_tensor :: Tensor -> Tensor -> Scaled Tensor
mult_tensor [] bs = Scaled 1 bs
mult_tensor as [] = Scaled 1 as
mult_tensor (a:as) (b:bs) = Scaled (x*y) (c:cs) where
  Scaled x c = mult a b
  Scaled y cs = mult_tensor as bs

-- | Multiply two scaled tensors.
mult_scaled_tensor :: Scaled Tensor -> Scaled Tensor -> Scaled Tensor
mult_scaled_tensor (Scaled x a) (Scaled y b) = Scaled (x*y*z) c where
  Scaled z c = a `mult_tensor` b

-- ----------------------------------------------------------------------
-- * Linear combinations of tensors

-- | A type to represent complex linear combinations of tensors. 
type TensorLC = Map Tensor Scalar

-- | The origin.
lc_zero :: TensorLC
lc_zero = Map.empty

-- | Add a tensor to a linear combination.
lc_insert :: TensorLC -> Scaled Tensor -> TensorLC
lc_insert lc (Scaled lambda t) =
  if newvalue == 0
  then
    Map.delete m lc
  else
    Map.insert m newvalue lc
      where
        m = normalize_tensor t
        newvalue = case Map.lookup m lc of
          Nothing -> lambda
          Just x -> lambda + x
    
-- | Turn a list of scaled tensors into a 'TensorLC'.
lc_from_list :: [Scaled Tensor] -> TensorLC    
lc_from_list = foldl lc_insert lc_zero

-- | Turn a 'TensorLC' into a list of scaled tensors.
lc_to_list :: TensorLC -> [Scaled Tensor]
lc_to_list lc = [Scaled x y | (y,x) <- Map.toList lc]

-- ----------------------------------------------------------------------
-- * Jordan-Wigner representation

-- $ The next two functions provide the Jordan-Wigner representation of
-- (Fock-space) annihilation and creation operators.

-- | Construct the Jordan-Wigner annihilation operator /a/[sub /p/] =
-- /IIIIPZZZZZ.../ for spin-orbital index /p/. The first parameter is
-- /p/, and the second one is /M/ (the number of spin-orbitals).
-- Precondition: 0 ≤ /p/ < /M/.
jw :: Int -> Int -> Scaled Tensor
jw p m = Scaled 1 (power p I ++ [P] ++ power (m-p-1) Z)

-- | Construct the Jordan-Wigner creation operator /a/[sub /p/][sup †]
-- = /IIIIMZZZZ.../ for spin-orbital index /p/.  The first parameter
-- is /p/, and the second one is /M/ (the number of spin-orbitals).
-- Precondition: 0 ≤ /p/ < /M/.
jw_dagger :: Int -> Int -> Scaled Tensor
jw_dagger p m = Scaled 1 (power p I ++ [M] ++ power (m-p-1) Z)

-- ----------------------------------------------------------------------
-- * Second quantized interaction terms

-- ** Simple interaction terms

-- | Construct the one-electron second quantized non-hermitianized
-- interaction term /a/[sub /p/][sup †]/a/[sub /q/].  The parameters
-- are /p,q/.
one_electron_operator_simple :: Int -> Int -> Scaled Tensor
one_electron_operator_simple p q = ap * aq
  where
    ap = jw_dagger p m    
    aq = jw q m
    m = maximum [p,q] + 1
    (*) = mult_scaled_tensor

-- | Construct the two-electron second quantized non-hermitianized
-- interaction term
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /r/]/a/[sub /s/].
-- The parameters are /p,q,r,s/.
two_electron_operator_simple :: Int -> Int -> Int -> Int -> Scaled Tensor
two_electron_operator_simple p q r s = ap * aq * ar * as
  where
    ap = jw_dagger p m 
    aq = jw_dagger q m 
    ar = jw r m 
    as = jw s m
    m = maximum [p,q,r,s] + 1
    (*) = mult_scaled_tensor

-- ** Hermitian interaction terms

-- | Construct
-- /a/[sub /p/][sup †]/a/[sub /q/] 
-- if /p/ = /q/, and 
-- /a/[sub /p/][sup †]/a/[sub /q/] + /a/[sub /q/][sup †]/a/[sub /p/] 
-- otherwise.
one_electron_operator :: Int -> Int -> TensorLC    
one_electron_operator p q =
  if p == q
  then lc_from_list [a_pq]
  else lc_from_list [a_pq, a_qp]
    where  
      a_pq = one_electron_operator_simple p q 
      a_qp = one_electron_operator_simple q p
       
-- | Construct
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /r/]/a/[sub /s/]
-- if (/p/,/q/) = (/s/,/r/), and 
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /r/]/a/[sub /s/] +
-- /a/[sub /s/][sup †]/a/[sub /r/][sup †]/a/[sub /q/]/a/[sub /p/]
-- otherwise.
two_electron_operator :: Int -> Int -> Int -> Int -> TensorLC
two_electron_operator p q r s =
  if (p,q) == (s,r)
  then lc_from_list [a_pqrs]
  else lc_from_list [a_pqrs, a_srqp]
    where
    a_pqrs = two_electron_operator_simple p q r s 
    a_srqp = two_electron_operator_simple s r q p

-- ----------------------------------------------------------------------
-- * /XYZD/ decomposition

-- | Decompose a basic operator into linear combinations of hermitian basic operators.
-- This uses the relations /P/ = 1\/2 /X/ + /i/\/2 /Y/ and 
-- /M/ = 1\/2 /X/ - /i/\/2 /Y/.
decompose_basis :: Op -> [Scaled Op]
decompose_basis P = [Scaled (1/2) X, Scaled (i/2) Y]
decompose_basis M = [Scaled (1/2) X, Scaled (-i/2) Y]
decompose_basis x = [Scaled 1 x]  -- default case: the remaining operators are already hermitian

-- | Decompose a tensor into a linear combination of hermitian
-- tensors. Due to sign alternation, the individual tensors all come
-- out to commute with each other.
decompose_tensor :: Tensor -> TensorLC
decompose_tensor [] = lc_from_list [Scaled 1 tensor_id]
decompose_tensor (h:t) =
  lc_from_list [Scaled (x*y) (g:gs) | 
                Scaled x g <- decompose_basis h, 
                Scaled y gs <- lc_to_list (decompose_tensor t)]

-- | Decompose a linear combination of tensors into a linear
-- combination of hermitian tensors.
decompose_tensor_lc :: TensorLC -> TensorLC
decompose_tensor_lc lc =                 
  lc_from_list [ Scaled (x*y) g | 
                 Scaled x gs <- lc_to_list lc,
                 Scaled y g <- lc_to_list (decompose_tensor gs)]

-- ----------------------------------------------------------------------
-- * Exponentiation and circuit generation

-- | Given a simple hermitian tensor /H/ and an angle θ, generate a
-- circuit for [exp -/i/θ/H/].  The given list of input qubits is in
-- the same order as the operators in /H/. Precondition: /H/ is made
-- up of zero or more identity operators and one or more of the
-- operators /X/, /Y/, /Z/, and /D/. The last parameter is a list of
-- additional controls.

exponentiate_simple :: Scaled Tensor -> Double -> [Qubit] -> [Qubit] -> Circ ()
exponentiate_simple (Scaled s ms) theta qs ctl = do
  -- First analyze the tensor:
  let
    -- Find all X positions
    xs = [ i | (m, i) <- zip ms [0,1..], m == X ]
    -- Find all Y positions
    ys = [ i | (m, i) <- zip ms [0,1..], m == Y ]
    -- Find all X, Y, Z positions
    zs = [ i | (m, i) <- zip ms [0,1..], m `elem` [X, Y, Z] ]
    -- Find all D positions
    ds = [ i | (m, i) <- zip ms [0,1..], m == D ]
  basischange xs ys zs qs
  rotation alpha ds zs `controlled` ctl
  reverse_generic_imp (basischange xs ys zs) qs
  where
    alpha = theta * realPart s
    basischange :: [Int] -> [Int] -> [Int] -> [Qubit] -> Circ ()
    basischange xs ys zs qs = do
      -- for every X or Y in the operator, apply the appropriate basis
      -- change to change it to Z.
      sequence_ [ hadamard_at (qs !! i) | i <- xs ]
      sequence_ [ gse_Y_at (qs !! i) | i <- ys ]      
      -- apply a cascade of c-not operators to all X, Y, or Z in the
      -- operator
      sequence_right_ [ qnot_at (qs !! i0) `controlled` (qs !! i1) | (i0,i1) <- consecutive_pairs zs]
    rotation :: Timestep -> [Int] -> [Int] -> Circ ()
    rotation alpha ds zs = do
      case zs of
        [] -> -- if there are no Z operators, produce a controlled
              -- e^{-iα} gate.
          case ds of
            [] -> error "exponentiate_simple: precondition violated"
            d:ds' -> gse_T_at alpha (qs !! d) `controlled` [qs !! d' | d' <- ds']
        z:zs' -> -- if there are Z operators, produce a controlled
                 -- e^{-iαZ} gate.
          rotZ_at (2*alpha) (qs !! z) `controlled` [qs !! d | d <- ds]

-- | Given a tensor /H/ (already decomposed into commuting simple
-- tensors) and an angle θ, generate a circuit for [exp -/i/θ/H/].
-- The given list of input qubits is in the same order as the
-- operators in /H/.
exponentiate :: TensorLC -> Double -> [Qubit] -> [Qubit] -> Circ ()
exponentiate lc theta qs ctl =
  sequence_ [ exponentiate_simple a theta qs ctl | a <- lc_to_list lc ]

-- ----------------------------------------------------------------------
-- * Generate top-level templates

-- | @'one_electron_circuit' theta p q@: Generate the circuit for the
-- hermitianized one-electron interaction with spin-orbital indices
-- /p/, /q/. More precisely, generate [exp -/i/θ/H/], where
-- /H/ = /a/[sub /p/][sup †]/a/[sub /q/] if /p/ = /q/ and 
-- /H/ = /a/[sub /p/][sup †]/a/[sub /q/] 
-- + /a/[sub /q/][sup †]/a/[sub /p/] otherwise.
-- 
-- This function recognizes an important special case: if θ=0.0, don't
-- generate any gates at all. The case θ=0.0 frequently arises because
-- of the conversion from spatial orbitals to spin orbitals.
one_electron_circuit :: Double -> Int -> Int -> [Qubit] -> [Qubit] -> Circ ()
one_electron_circuit 0.0 p q qs ctl = return ()
one_electron_circuit theta p q qs ctl = do
  comment_with_label (printf "ENTER: one_electron_circuit (theta=%.3e, p=%d, q=%d)" theta p q) (qs,ctl) ("qs","ctl")
  exponentiate op theta qs ctl
  comment_with_label "EXIT: one_electron_circuit" (qs,ctl) ("qs","ctl")
  where
    op = decompose_tensor_lc (one_electron_operator p q)
      
-- | @'two_electron_circuit' theta p q r s@:
-- Generate the circuit for the hermitianized two-electron interaction
-- with spin-orbital indices /p/, /q/, /r/, /s/. More precisely, generate 
-- [exp -/i/θ/H/], where 
-- /H/ = /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /r/]/a/[sub /s/] if 
-- (/p/,/q/) = (/s/,/r/) and /H/ =
-- /a/[sub /p/][sup †]/a/[sub /q/][sup †]/a/[sub /r/]/a/[sub /s/] +
-- /a/[sub /s/][sup †]/a/[sub /r/][sup †]/a/[sub /q/]/a/[sub /p/]
-- otherwise.
-- 
-- This function recognizes an important special case: if θ=0.0, don't
-- generate any gates at all. The case θ=0.0 frequently arises because
-- of the conversion from spatial orbitals to spin orbitals.
two_electron_circuit :: Double -> Int -> Int -> Int -> Int -> [Qubit] -> [Qubit] -> Circ ()
two_electron_circuit 0.0 p q r s qs ctl = return ()
two_electron_circuit theta p q r s qs ctl = do
  comment_with_label (printf "ENTER: two_electron_circuit (theta=%.3e, p=%d, q=%d, r=%d, s=%d)" theta p q r s) (qs,ctl) ("qs","ctl")
  exponentiate op theta qs ctl
  comment_with_label "EXIT: two_electron_circuit" (qs,ctl) ("qs","ctl")
  where
    op = decompose_tensor_lc (two_electron_operator p q r s)
      
-- | Like 'two_electron_circuit', but use the \"orthodox\" circuit
-- template for the Coulomb operator /a/[sub /p/][sup †]/a/[sub
-- /q/][sup †]/a/[sub /q/]/a/[sub /p/]. This generates a circuit using
-- three rotations, similar to [Whitfield et al.], but with corrected
-- angles,
--     
-- > [image b2-orthodox.png]
-- 
-- instead of the simpler circuit that 'two_electron_circuit' would
-- normally generate:
-- 
-- > [image b2-template.png]

two_electron_circuit_orthodox :: Double -> Int -> Int -> Int -> Int -> [Qubit] -> [Qubit] -> Circ ()
two_electron_circuit_orthodox 0.0 p q r s qs ctl = return ()
two_electron_circuit_orthodox theta p q r s qs ctl | q==r && p==s && p/=q = do
  comment_with_label (printf "ENTER: two_electron_circuit_orthodox(theta=%.3e, p=%d, q=%d, r=%d, s=%d)" theta p q r s) (qs,ctl) ("qs","ctl")
  let pp = qs !! p
      qq = qs !! q
  gse_G_at (theta/4) pp `controlled` ctl
  rotZ_at (-theta/2) pp `controlled` ctl
  rotZ_at (-theta/2) qq `controlled` ctl
  qnot_at qq `controlled` pp  -- control ctl is not needed
  rotZ_at (theta/2) qq `controlled` ctl
  qnot_at qq `controlled` pp  -- control ctl is not needed
  comment_with_label "EXIT: two_electron_circuit_orthodox" (qs,ctl) ("qs","ctl")
                                                                         
-- all other cases aren't Coulomb operators, so fall back to
-- two_electron_circuit.
two_electron_circuit_orthodox theta p q r s qs ctl = do
  two_electron_circuit theta p q r s qs ctl
  
-- ----------------------------------------------------------------------
-- * Testing

-- $ We provide two functions, accessible via command line options,
-- that allow the user to display individual templates. 

-- | Display the circuit for the hermitianized one-electron interaction,
-- with θ=1.
show_one_electron :: Format -> GateBase -> Int -> Int -> IO ()
show_one_electron format gatebase p q = 
  print_generic format (decompose_generic gatebase circuit) (replicate (n-m) qubit) where
    circuit qs = one_electron_circuit 1.0 (p-m) (q-m) qs []
    n = maximum [p,q] + 1
    m = minimum [p,q]

-- | Display the circuit for the hermitianized two-electron interaction, 
-- with θ=1. 
show_two_electron :: Format -> GateBase -> Int -> Int -> Int -> Int -> IO ()
show_two_electron format gatebase p q r s = 
  print_generic format (decompose_generic gatebase circuit) (replicate (n-m) qubit) where
    circuit qs = two_electron_circuit 1.0 (p-m) (q-m) (r-m) (s-m) qs []
    n = maximum [p,q,r,s] + 1
    m = minimum [p,q,r,s]

-- | Like 'show_two_electron', but use the \"orthodox\" template for
-- the Coulomb operator.
show_two_electron_orthodox :: Format -> GateBase -> Int -> Int -> Int -> Int -> IO ()
show_two_electron_orthodox format gatebase p q r s = 
  print_generic format (decompose_generic gatebase circuit) (replicate (n-m) qubit) where
    circuit qs = two_electron_circuit_orthodox 1.0 (p-m) (q-m) (r-m) (s-m) qs []
    n = maximum [p,q,r,s] + 1
    m = minimum [p,q,r,s]
