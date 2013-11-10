-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

-- | This module contains an implementation of a quantum simulator that 
-- uses the stabilizer states of the Clifford group (i.e. the Pauli group),
-- to provide efficient simulation of quantum circuits constructed from
-- elements of the Clifford group. The module provides an implementation
-- of the Clifford group operators {x,y,z,h,s,controlled-x} which form a
-- generating set for the Clifford group.
module Libraries.Stabilizers.Clifford where

import Prelude hiding (lookup,negate)
import Libraries.Stabilizers.Pauli
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State
import System.Random
import Libraries.Synthesis.Ring (Cplx (..), i)

-- | A qubit is defined as an integer reference.
type Qubit = Int

-- | The state of the system is a representation of a stabilizer tableau.

-- note this isn't a record, so as to help with strictness annotations 
data Tableau = ST Qubit !(Map Qubit Sign) !(Map (Qubit,Qubit) Pauli) !(Map Qubit Sign) !(Map (Qubit,Qubit) Pauli)

-- | Accessor function for the next_qubit field of a Tableau
next_qubit :: Tableau -> Qubit
next_qubit (ST nq _ _ _ _) = nq

-- | Accessor function for the sign field of a Tableau
sign :: Tableau -> Map Qubit Sign
sign (ST _ s _ _ _) = s

-- | Accessor function for the tableau field of a Tableau
tableau :: Tableau -> Map (Qubit,Qubit) Pauli
tableau (ST _ _ t _ _) = t

-- | Accessor function for the de_sign field of a Tableau
de_sign :: Tableau -> Map Qubit Sign
de_sign (ST _ _ _ de_s _) = de_s

-- | Accessor function for the de_tableau field of a Tableau
de_tableau :: Tableau -> Map (Qubit,Qubit) Pauli
de_tableau (ST _ _ _ _ de_t) = de_t


-- | A local Map lookup function that throws an error if the key doesn't exist.
lookup :: (Ord k,Show k, Show v) => k -> Map k v -> v
lookup k m = 
 case Map.lookup k m of
  Just b -> b
  Nothing -> error ("key: " ++ show k ++ " not in map: " ++ show m)

-- | A tableau can be shown, by enumerating over the qubits in scope.
instance Show Tableau where
 show tab = unlines $ ("Stabilizer:":map show_row qs) ++ ("Destabilizer:":map show_de_row qs)
  where 
   qs :: [Qubit]
   qs = [0..(next_qubit tab) - 1]
   show_row :: Qubit -> String 
   show_row q_row = show (lookup q_row (sign tab)) 
                     ++ unwords (map (show_pauli q_row) qs)
   show_pauli :: Qubit -> Qubit -> String
   show_pauli q_row q_column = show (lookup (q_row,q_column) (tableau tab))
   show_de_row :: Qubit -> String 
   show_de_row q_row = show (lookup q_row (de_sign tab)) 
                        ++ unwords (map (show_de_pauli q_row) qs)
   show_de_pauli :: Qubit -> Qubit -> String
   show_de_pauli q_row q_column = show (lookup (q_row,q_column) (de_tableau tab))

-- | An initial (empty) tableau.
empty_tableau :: Tableau
empty_tableau = ST 0 Map.empty Map.empty Map.empty Map.empty

-- | A new qubit in the state |0〉 or |1〉 can be added to a tableau.
add_qubit :: Bool -> Tableau -> Tableau
add_qubit b tab = ST (nq + 1) sign' tableau' de_sign' de_tableau'
 where
  nq = next_qubit tab
  sign' = Map.insert nq (if b then Minus else Plus) (sign tab)
  de_sign' = Map.insert nq Plus (de_sign tab)
  tableau' = foldl' insertI (foldl' insertZ (tableau tab) [0..nq]) [0..nq-1]
  de_tableau' = foldl' insertI (foldl' insertX (de_tableau tab) [0..nq]) [0..nq-1]
  insertZ :: Map (Qubit,Qubit) Pauli -> Qubit -> Map (Qubit,Qubit) Pauli
  insertZ tab cq = Map.insert (nq,cq) (if nq == cq then Z else I) tab
  insertX :: Map (Qubit,Qubit) Pauli -> Qubit -> Map (Qubit,Qubit) Pauli
  insertX tab cq = Map.insert (nq,cq) (if nq == cq then X else I) tab
  insertI :: Map (Qubit,Qubit) Pauli -> Qubit -> Map (Qubit,Qubit) Pauli
  insertI tab cq = Map.insert (cq,nq) I tab

-- | A (Clifford) unitary can be defined as a function acting on Pauli operators.
type Unitary = Pauli -> (Sign,Pauli)

instance Eq Unitary where
  u1 == u2 = and [ u1 x == u2 x | x <- ixyz]
    where ixyz = [I,X,Y,Z] 

-- for a unitary U, the action on each Pauli (P) should be defined
-- as the result of UPU*. A complete set of generators for the Clifford
-- group is defined below, so defining a Unitary shouldn't be required
-- at the user-level

-- | The minimal definition of a unitary requires the actions on /X/ and /Z/.
data MinPauli = Xmin | Zmin

-- | The minimal definition of a unitary requires the actions on /X/ and /Z/.
type MinUnitary = MinPauli -> (Sign,Pauli)

-- | The definition of a 'Unitary' can be constructed from a 'MinimalUnitary'.
from_minimal :: MinUnitary -> Unitary
from_minimal f I = (Plus,I)
from_minimal f X = f Xmin
from_minimal f Z = f Zmin
from_minimal f Y = (sign,pauli)
 where
  (sx,px) = f Xmin
  (sz,pz) = f Zmin
  (spc,pauli) = commute px pz
  sign = signPlus_to_sign $ multiply_signPlus (multiply_signPlus (One sx) (One sz)) (multiply_signPlus (PlusI) (spc))

-- | It is possible to construct a 'Unitary' from a 2×2-matrix.
from_matrix :: (Floating r, Eq r, Show r) => Matrix1 (Cplx r) -> Unitary
from_matrix m = from_minimal minimal
 where
  minimal xy = sp
   where
    xy' = case xy of 
           Xmin -> X
           Zmin -> Z
    m_dagger = transpose1 m
    sp = fromMatrix1 $ multiplyMatrix1 m (multiplyMatrix1 (toMatrix1 xy') m_dagger)
 
-- | A unitary can be applied to a qubit in a given tableau. By folding through each row
apply_unitary :: Unitary -> Qubit -> Tableau -> Tableau
apply_unitary u q_column tab = foldl' (apply_unitary_row u q_column) tab [0..nq-1]
 where
  nq = next_qubit tab

-- | Apply the unitary to the given column, in the given row.
apply_unitary_row :: Unitary -> Qubit -> Tableau -> Qubit -> Tableau
apply_unitary_row u q_column tab q_row = ST (next_qubit tab) sign' tableau' de_sign' de_tableau'
   where 
    s = sign tab
    current_sign = lookup q_row s
    t = tableau tab
    current_pauli = lookup (q_row,q_column) t
    (change_sign,new_pauli) = u current_pauli
    new_sign = if negative change_sign then negate current_sign else current_sign
    sign' = Map.insert q_row new_sign s
    tableau' = Map.insert (q_row,q_column) new_pauli t
    de_s = de_sign tab
    de_current_sign = lookup q_row de_s
    de_t = de_tableau tab
    de_current_pauli = lookup (q_row,q_column) de_t
    (de_change_sign,de_new_pauli) = u de_current_pauli
    de_new_sign = if negative de_change_sign then negate de_current_sign else de_current_sign
    de_sign' = Map.insert q_row de_new_sign de_s
    de_tableau' = Map.insert (q_row,q_column) de_new_pauli de_t

-- | A two-qubit (Clifford) unitary can be defined as a function acting
-- on a pair of Pauli operators.
type Unitary2 = (Pauli,Pauli) -> (Sign,Pauli,Pauli)

instance Eq Unitary2 where
  u1 == u2 = and [ u1 (x,y) == u2 (x,y) | x <- ixyz, y <- ixyz]
    where ixyz = [I,X,Y,Z] 

-- | The minimal definition of a two-qubit unitary requires the actions on /IX/, /XI/, /IZ/, and /ZI/.
data MinPauli2 = IX | XI | IZ | ZI

-- | The minimal definition of a two-qubit unitary requires the actions on /IX/, /XI/, /IZ/, and /ZI/.
type MinUnitary2 = MinPauli2 -> (Sign,Pauli,Pauli)

-- | The definition of a 'Unitary2' can be constructed from a 'MinimalUnitary2'.
from_minimal2 :: MinUnitary2 -> Unitary2
from_minimal2 f (I,I) = (Plus,I,I)
from_minimal2 f (I,X) = f IX
from_minimal2 f (X,I) = f XI
from_minimal2 f (I,Z) = f IZ
from_minimal2 f (Z,I) = f ZI
from_minimal2 f (I,Y) = (sign,p1,p2)
  where
   (six,pix1,pix2) = from_minimal2 f (I,X) 
   (siz,piz1,piz2) = from_minimal2 f (I,Z)
   (spc1,p1) = commute pix1 piz1
   (spc2,p2) = commute pix2 piz2
   sign = signPlus_to_sign $ multiply_signPlus (PlusI) (multiply_signPlus (multiply_signPlus (One six) (One siz)) (multiply_signPlus (spc1) (spc2)))
from_minimal2 f (Y,I) = (sign,p1,p2)
  where
   (six,pix1,pix2) = from_minimal2 f (X,I) 
   (siz,piz1,piz2) = from_minimal2 f (Z,I)
   (spc1,p1) = commute pix1 piz1
   (spc2,p2) = commute pix2 piz2
   sign = signPlus_to_sign $ multiply_signPlus (PlusI) (multiply_signPlus (multiply_signPlus (One six) (One siz)) (multiply_signPlus (spc1) (spc2)))
from_minimal2 f (pauli1,pauli2) = (sign,p1,p2)
  where
   (six,pix1,pix2) = from_minimal2 f (pauli1,I) 
   (siz,piz1,piz2) = from_minimal2 f (I,pauli2)
   (spc1,p1) = commute pix1 piz1
   (spc2,p2) = commute pix2 piz2
   sign = signPlus_to_sign $ multiply_signPlus (multiply_signPlus (One six) (One siz)) (multiply_signPlus (spc1) (spc2))

-- | It is possible to construct a 'Unitary2' from a 4×4-matrix.
from_matrix2 :: (Floating r, Eq r, Show r) => Matrix2 (Cplx r) -> Unitary2
from_matrix2 m = from_minimal2 minimal
 where
  minimal xy = sp
   where
    xy' = case xy of 
           IX -> (I,X)
           XI -> (X,I) 
           IZ -> (I,Z)
           ZI -> (Z,I)
    m_dagger = transpose2 m
    sp = fromMatrix2 $ multiplyMatrix2 m (multiplyMatrix2 (toMatrix2 xy') m_dagger)

-- | It is possible to construct a 'Unitary2' from controlling a 2×2-matrix.
from_matrix_controlled :: (Floating r, Show r, Eq r) => Matrix1 (Cplx r) -> Unitary2
from_matrix_controlled m1 = from_matrix2 (control1 m1)

-- | A two-qubit unitary can be applied to a pair of qubits in a given tableau.
apply_unitary2 :: Unitary2 -> (Qubit,Qubit) -> Tableau -> Tableau
apply_unitary2 u (q1,q2) tab = foldl' apply_unitary2' tab [0..nq-1]
 where
  nq = next_qubit tab
  apply_unitary2' :: Tableau -> Qubit -> Tableau
  apply_unitary2' tab q_row = ST (next_qubit tab) sign' tableau'' de_sign' de_tableau''
   where
    s = sign tab
    current_sign = lookup q_row s
    t = tableau tab
    current_pauli1 = lookup (q_row,q1) t
    current_pauli2 = lookup (q_row,q2) t
    (change_sign,new_pauli1,new_pauli2) = u (current_pauli1,current_pauli2)
    new_sign = if negative change_sign then negate current_sign else current_sign
    sign' = Map.insert q_row new_sign s
    tableau' = Map.insert (q_row,q1) new_pauli1 t
    tableau'' = Map.insert (q_row,q2) new_pauli2 tableau'
    de_s = de_sign tab
    de_current_sign = lookup q_row de_s
    de_t = de_tableau tab
    de_current_pauli1 = lookup (q_row,q1) de_t
    de_current_pauli2 = lookup (q_row,q2) de_t
    (de_change_sign,de_new_pauli1,de_new_pauli2) = u (de_current_pauli1,de_current_pauli2)
    de_new_sign = if negative de_change_sign then negate de_current_sign else de_current_sign
    de_sign' = Map.insert q_row de_new_sign de_s
    de_tableau' = Map.insert (q_row,q1) de_new_pauli1 de_t
    de_tableau'' = Map.insert (q_row,q2) de_new_pauli2 de_tableau'

-- | A measurement, in the computational basis, can be made of a qubit
-- in the Tableau, returning the measurement result, and the resulting
-- Tableau.
measure :: Qubit -> Tableau -> IO (Bool,Tableau)
measure q tab = case anticommute_with_z of
  [] -> -- all of the stabilizers commute with z, so the measurement is 
    -- deterministic and doesn't change the tableau, 
    -- but we need to calculate the result! 
    -- the stabilzer either contains Z_q or -Z_q
   case (filter (\(row,_) -> row == z_row) z_rows) of
    [] -> do -- in this case, we need to see whether the generators form Z_q or -Z_q
     let tab' = reduce q tab
     (res,_) <- measure q tab'
     return (res,tab)
    [(_,row)] -> return (negative (lookup row s),tab)
    _ -> error "measure: multiple Zs found" -- should never occur!
    where
     z_row :: [Pauli]
     z_row = map (\q_col -> if q_col == q then Z else I) [0..(nq-1)]
     z_rows :: [([Pauli],Qubit)]
     z_rows = map (\q_row -> ((map (\q_col ->(lookup (q_row,q_col) t)) [0..(nq-1)]),q_row)) [0..(nq-1)] 
  [(_,q_row)] -> do -- exaclty one anti-commutes, measurement result is 50/50
    let de_s' = Map.insert q_row (lookup q_row s) de_s
    let de_t' = foldl' (\de_t q' -> Map.insert (q_row,q') (lookup (q_row,q') t) de_t) de_t [0..(nq-1)]
    b <- randomIO
    let eigen_value = if b then Minus else Plus
    let s' = Map.insert q_row eigen_value s
    let t' = foldl' (\t q' -> Map.insert (q_row,q') (if q == q' then Z else I) t) t [0..(nq-1)]
    let tab' = ST nq s' t' de_s' de_t'
    return (negative eigen_value,tab')
  ((_,q_row1):((_,q_row2):_)) -> -- more than one anti-commutes, so we update the set of stabilizers with the product of the first two anti-commuters
   measure q (multiply q_row2 q_row1 tab)
 where 
  nq = next_qubit tab
  t = tableau tab
  s = sign tab
  de_t = de_tableau tab
  de_s = de_sign tab
  gs = map (\q_row -> (lookup (q_row,q) t,q_row)) [0..(nq-1)]
  anticommute_with_z = filter (\(ixyz,_) -> ixyz == X || ixyz == Y) gs

-- | This function reduces a tableau so that it contains either plus
-- or minus /Z/[sub /q/]. Note that it is only called in the case
-- where /Z/[sub /q/] is generated by the tableau (i.e., during
-- measurement).
reduce :: Qubit -> Tableau -> Tableau
reduce qubit tab = foldl' (\t q -> multiply r q t) tab ows
 where
  nq = next_qubit tab
  t = tableau tab
  de_t = de_tableau tab
  (r:ows) = filter (\q_row -> isXY (lookup (q_row,qubit) de_t) ) [0..nq-1]
  isXY p = p == X || p == Y

-- | Multiply the stabilizers for the two given rows, in the given tableau, and
-- update the first row with the result of the multiplication.
multiply :: Qubit -> Qubit -> Tableau -> Tableau
multiply q_row1 q_row2 tab = ST nq s' t' (de_sign tab) (de_tableau tab)
 where
  nq = next_qubit tab
  t = tableau tab
  s = sign tab 
  sign1 = lookup q_row1 s
  sign2 = lookup q_row2 s
  sp = One (multiply_sign sign1 sign2)
  (t',sp') = foldl' mul_col (t,sp) [0..(nq-1)] 
  s' = Map.insert q_row1 (signPlus_to_sign sp') s
  mul_col :: (Map (Qubit,Qubit) Pauli, SignPlus) -> Qubit -> (Map (Qubit,Qubit) Pauli, SignPlus)
  mul_col (tab,sp) q_col = (Map.insert (q_row1,q_col) p' tab,multiply_signPlus sp sp')
    where
     p1 = lookup (q_row1,q_col) tab
     p2 = lookup (q_row2,q_col) tab
     (sp',p') = commute p1 p2

---------------------------------------
-- Generators for the Clifford group --
---------------------------------------

-- All Clifford group operators can be defined in terms of the
-- following gates. The Monadic interface can be used for this
-- purpose. For example.

-- | The Pauli /X/ operator is a Clifford group unitary.
x :: Unitary
x I = (Plus,I)
x X = (Plus,X)
x Y = (Minus,Y)
x Z = (Minus,Z)

-- | We can (equivalently) define Pauli-/X/ as a 'MinUnitary'.
x_min :: MinUnitary
x_min Xmin = (Plus,X)
x_min Zmin = (Minus,Z)

-- | We can (equivalently) construct Pauli-/X/ from a 'MinUnitary'.
x' :: Unitary
x' = from_minimal x_min

-- | We can (equivalently) construct Pauli-/X/ from a matrix.
x'' :: Unitary
x'' = from_matrix (0,1,1,0)

-- | The Pauli /Y/-operator is a Clifford group unitary.
y :: Unitary
y I = (Plus,I)
y X = (Minus,X)
y Y = (Plus,Y)
y Z = (Minus,Z)

-- | We can (equivalently) define Pauli-/Y/ as a 'MinUnitary'.
y_min :: MinUnitary
y_min Xmin = (Minus,X)
y_min Zmin = (Minus,Z)

-- | We can (equivalently) construct Pauli-/Y/ from a 'MinUnitary'.
y' :: Unitary
y' = from_minimal y_min

-- | We can (equivalently) construct Pauli-/Y/ from a matrix.
y'' :: Unitary
y'' = from_matrix (0,-i,i,0)

-- | The Pauli /Z/-operator is a Clifford group unitary.
z :: Unitary
z I = (Plus,I)
z X = (Minus,X)
z Y = (Minus,Y)
z Z = (Plus,Z)

-- | We can (equivalently) define Pauli-/Z/ as a 'MinUnitary'.
z_min :: MinUnitary
z_min Xmin = (Minus,X)
z_min Zmin = (Plus,Z)

-- | We can (equivalently) construct Pauli-/Z/ from a 'MinUnitary'.
z' :: Unitary
z' = from_minimal z_min

-- | We can (equivalently) construct Pauli-/Z/ from a matrix.
z'' :: Unitary
z'' = from_matrix (1,0,0,-1)

-- | The Hadamard-gate is a Clifford group unitary.
h :: Unitary
h I = (Plus,I)
h X = (Plus,Z)
h Y = (Minus,Y)
h Z = (Plus,X)

-- | We can (equivalently) define Hadamard as a 'MinUnitary'.
h_min :: MinUnitary
h_min Xmin = (Plus,Z)
h_min Zmin = (Plus,X)

-- | We can (equivalently) construct Hadamard from a 'MinUnitary'.
h' :: Unitary
h' = from_minimal h_min

-- | We can (equivalently) construct Hadamard from a matrix.
-- Although rounding errors break this!!!
h'' :: Unitary
h'' = from_matrix $ scale1 (Cplx (1/sqrt 2) 0) (1,1,1,-1)

-- | The phase-gate is a Clifford group unitary.
s :: Unitary
s I = (Plus,I) 
s X = (Plus,Y)
s Y = (Minus,X)
s Z = (Plus,Z)

-- | We can (equivalently) define phase gate as a 'MinUnitary'.
s_min :: MinUnitary
s_min Xmin = (Plus,Y)
s_min Zmin = (Plus,Z)

-- | We can (equivalently) construct phase gate from a 'MinUnitary'.
s' :: Unitary
s' = from_minimal s_min

-- | We can (equivalently) construct phase gate from a matrix.
s'' :: Unitary
s'' = from_matrix (1,0,0,i)

-- | The phase-gate is a Clifford group unitary.
e :: Unitary
e I = (Plus,I) 
e X = (Plus,Y)
e Y = (Plus,Z)
e Z = (Plus,X)

-- | We can (equivalently) define phase gate as a 'MinUnitary'.
e_min :: MinUnitary
e_min Xmin = (Plus,Y)
e_min Zmin = (Plus,X)

-- | We can (equivalently) construct phase gate from a 'MinUnitary'.
e' :: Unitary
e' = from_minimal e_min

-- | We can (equivalently) construct phase gate from a matrix.
e'' :: Unitary
e'' = from_matrix ((-1+i)/2, (1+i)/2, (-1+i)/2, (-1-i)/2)

-- | The controlled-not is a Clifford group 2-qubit unitary.
cnot :: Unitary2
cnot (I,I) = (Plus,I,I)
cnot (I,X) = (Plus,I,X)
cnot (I,Y) = (Plus,Z,Y)
cnot (I,Z) = (Plus,Z,Z)
cnot (X,I) = (Plus,X,X)
cnot (X,X) = (Plus,X,I)
cnot (X,Y) = (Plus,Y,Z)
cnot (X,Z) = (Minus,Y,Y)
cnot (Y,I) = (Plus,Y,X)
cnot (Y,X) = (Plus,Y,I)
cnot (Y,Y) = (Minus,X,Z)
cnot (Y,Z) = (Plus,X,Y)
cnot (Z,I) = (Plus,Z,I)
cnot (Z,X) = (Plus,Z,X)
cnot (Z,Y) = (Plus,I,Y)
cnot (Z,Z) = (Plus,I,Z)

-- | We can (equivalently) define CNot as a 'MinUnitary2'.
cnot_min :: MinUnitary2
cnot_min IX = (Plus,I,X)
cnot_min XI = (Plus,X,X)
cnot_min IZ = (Plus,Z,Z)
cnot_min ZI = (Plus,Z,I)

-- | We can (equivalently) construct CNot from a 'MinUnitary2'.
cnot' :: Unitary2
cnot' = from_minimal2 cnot_min

-- | We can (equivalently) construct CNot from a matrix.
cnot'' :: Unitary2
cnot'' = from_matrix2 ((1,0,0,1),(0,0,0,0),(0,0,0,0),(0,1,1,0))

-- | The controlled-/Z/ is a Clifford group 2-qubit unitary.
cz :: Unitary2
cz (I,I) = (Plus,I,I)
cz (I,X) = (Plus,Z,X)
cz (I,Y) = (Plus,Z,Y)
cz (I,Z) = (Plus,I,Z)
cz (X,I) = (Plus,X,Z)
cz (X,X) = (Plus,Y,Y)
cz (X,Y) = (Minus,Y,X)
cz (X,Z) = (Plus,X,I)
cz (Y,I) = (Plus,Y,Z)
cz (Y,X) = (Minus,X,Y)
cz (Y,Y) = (Plus,X,X)
cz (Y,Z) = (Plus,Y,I)
cz (Z,I) = (Plus,Z,I)
cz (Z,X) = (Plus,I,X)
cz (Z,Y) = (Plus,I,Y)
cz (Z,Z) = (Plus,Z,Z)

-- | We can (equivalently) define controlled-/Z/ as a 'MinUnitary2'.
cz_min :: MinUnitary2
cz_min IX = (Plus,Z,X)
cz_min XI = (Plus,X,Z)
cz_min IZ = (Plus,I,Z)
cz_min ZI = (Plus,Z,I)

-- | We can (equivalently) construct controlled-/Z/ from a 'MinUnitary2'.
cz' :: Unitary2
cz' = from_minimal2 cz_min

-- | We can (equivalently) construct controlled-/Z/ from a matrix.
cz'' :: Unitary2
cz'' = from_matrix2 ((1,0,0,1),(0,0,0,0),(0,0,0,0),(1,0,0,-1))

------------------------------------------------------------------
-- A Monadic Interface for constructing Clifford group circuits --
------------------------------------------------------------------

-- Larger Clifford group circuits can be defined in terms of the
-- following operations. It is envisaged that a Quipper Transformer
-- can be defined to translate appropriate Quipper circuits (i.e.
-- circuits that only use Clifford group operators) into a
-- CliffordCirc so that it can be simulated (efficiently).

-- | A Clifford group circuit is implicitly simulated using
-- a state monad over a 'Tableau'.
type CliffordCirc a = StateT Tableau IO a

-- | Initialize a new qubit.
init_qubit :: Bool -> CliffordCirc Qubit
init_qubit b = do
  tab <- get
  let nq = next_qubit tab
  put (add_qubit b tab)
  return nq 

-- | Initialize multiple qubits.
init_qubits :: [Bool] -> CliffordCirc [Qubit]
init_qubits = mapM init_qubit

-- | Apply a Pauli-/X/ gate to the given qubit.
gate_X :: Qubit -> CliffordCirc ()
gate_X q = do
  tab <- get
  put (apply_unitary x q tab)

-- | Apply a Pauli-/Y/ gate to the given qubit.
gate_Y :: Qubit -> CliffordCirc ()
gate_Y q = do
  tab <- get
  put (apply_unitary y q tab)

-- | Apply a Pauli-/Z/ gate to the given qubit.
gate_Z :: Qubit -> CliffordCirc ()
gate_Z q = do
  tab <- get
  put (apply_unitary z q tab)

-- | Apply a Hadamard gate to the given qubit.
gate_H :: Qubit -> CliffordCirc ()
gate_H q = do
  tab <- get
  put (apply_unitary h q tab)

-- | Apply a phase gate to the given qubit.
gate_S :: Qubit -> CliffordCirc ()
gate_S q = do
  tab <- get
  put (apply_unitary s q tab)

-- | Apply a given 'Unitary' to the given qubit.
gate_Unitary :: Unitary -> Qubit -> CliffordCirc ()
gate_Unitary u q = do
  tab <- get
  put (apply_unitary u q tab)

-- | Apply a controlled-/X/ gate to the given qubits.
controlled_X :: Qubit -> Qubit -> CliffordCirc ()
controlled_X q1 q2 = do
  tab <- get
  put (apply_unitary2 cnot (q1,q2) tab)

-- | Apply a controlled-/Z/ gate to the given qubits.
controlled_Z :: Qubit -> Qubit -> CliffordCirc ()
controlled_Z q1 q2 = do
  tab <- get
  put (apply_unitary2 cz (q1,q2) tab)

-- | Apply a given 'Unitary2' to the given qubits
gate_Unitary2 :: Unitary2 -> Qubit -> Qubit -> CliffordCirc ()
gate_Unitary2 u q1 q2 = do
  tab <- get
  put (apply_unitary2 u (q1,q2) tab)

-- | Measure the given qubit in the computational basis.
measure_qubit :: Qubit -> CliffordCirc Bool
measure_qubit q = do
  tab <- get
  (res,tab') <- lift $ measure q tab
  put tab'
  return res

-- | Measure the given list of qubits.
measure_qubits :: [Qubit] -> CliffordCirc [Bool]
measure_qubits = mapM measure_qubit

-- | For testing purposes, we can show the tableau during a simulation.
show_tableau :: CliffordCirc ()
show_tableau = do
  tab <- get
  lift $ putStrLn (show tab)

----------------------------------------------------
-- Evaluation and Simulation of Clifford circuits --
----------------------------------------------------

-- | Return the evaluated 'Tableau' for the given circuit.
eval :: CliffordCirc a -> IO Tableau
eval cc = execStateT cc empty_tableau

-- | Return the result of simulating the given circuit.
sim :: CliffordCirc a -> IO a
sim cc = evalStateT cc empty_tableau

---------------------------------
-- Some test Clifford circuits --
---------------------------------

-- | A swap gate can be defined in terms of three controlled-not gates.
swap :: Qubit -> Qubit -> CliffordCirc ()
swap q1 q2 = do
  controlled_X q1 q2
  controlled_X q2 q1
  controlled_X q1 q2

-- | A controlled-/Z/ gate can (equivalently) be defined in terms of
-- Hadamard and controlled-/X/.
controlled_Z' :: Qubit -> Qubit -> CliffordCirc ()
controlled_Z' q1 q2 = do
  gate_H q2
  controlled_X q1 q2
  gate_H q2


-- | Each of the four Bell states can be generated, indexed by a pair
-- of boolean values.
bell :: (Bool,Bool) -> CliffordCirc (Qubit,Qubit)
bell (bx,by) = do
  x <- init_qubit bx
  --show_tableau
  y <- init_qubit by
  --show_tableau
  gate_H x
  --show_tableau
  controlled_X x y
  --show_tableau
  return (x,y)

-- | Create a Bell state, and measure it.
measure_bell00 :: CliffordCirc (Bool,Bool)
measure_bell00 = do
  (bx,by) <- bell (False,False)
  mx <- measure_qubit bx
  --show_tableau
  my <- measure_qubit by
  --show_tableau
  return (mx,my)

-- | A single-qubit operation can be controlled by a classical boolean value.
controlled_if :: Bool -> (Qubit -> CliffordCirc ()) -> Qubit -> CliffordCirc ()
controlled_if b u q = if b then u q else return ()

-- | A simple, single qubit, teleportation circuit.
teleport :: Qubit -> CliffordCirc Qubit
teleport q1 = do
  (q2,q3) <- bell (False,False)
  controlled_X q1 q2
  gate_H q1
  [b1,b2] <- measure_qubits [q1,q2]
  controlled_if b2 gate_X q3
  controlled_if b1 gate_Z q3
  return q3

-- | A wrapper around the teleportation circuit that initializes a qubit
-- in the given boolean state, and measures the teleported qubit.
test_teleport :: Bool -> CliffordCirc Bool
test_teleport b = do
  q <- init_qubit b
  q' <- teleport q
  measure_qubit q'

-- | Measure an equal superposition.
random_bool :: CliffordCirc Bool
random_bool = do
  q <- init_qubit False
  gate_H q
  measure_qubit q
