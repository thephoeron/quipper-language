-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE IncoherentInstances #-}

-- | This module provides global definitions for the Triangle Finding Algorithm. 

module Algorithms.TF.Definitions where

import Prelude hiding (mapM, mapM_)
import qualified Data.Map as Map
import Data.IntMap (IntMap, Key)
import qualified Data.IntMap as IntMap
import Data.Traversable (mapM)
import Data.Foldable (mapM_)
import Data.Typeable (Typeable)

import Quipper
import Quipper.Internal
import QuipperLib.Arith

import Libraries.Auxiliary (mmap)

-- ======================================================================
-- * Qram abstraction

-- | A data structure to hold a Qram implementation. This provides
-- operations for fetching and storing quantum data from a quantum
-- array, addressed by a quantum integer. One implementation is given
-- by algorithms 'a8_FetchT', 'a9_StoreT' and 'a10_FetchStoreT'.

data Qram = Qram {
  qram_fetch :: (QData qa) => QDInt -> IntMap qa -> qa -> Circ (QDInt, IntMap qa, qa),
  qram_store :: (QData qa) => QDInt -> IntMap qa -> qa -> Circ (QDInt, IntMap qa, qa),
  qram_swap :: (QData qa) => QDInt -> IntMap qa -> qa -> Circ (QDInt, IntMap qa, qa)
}

-- ======================================================================
-- * Types for the Triangle Finding Algorithm

-- As synonyms, these first few types are all automatically instances of QCData.

-- | A node of the graph (classical circuit type). 
type CNode = [Bit]  

-- | A node of the graph (quantum circuit type). 
type QNode = [Qubit]  

-- | The type of problem specifications for the Triangle Finding Problem. A problem 
-- specification consists of: 
--
-- * an integer /n/ which determines the number /N=//2/[sup /n/] of nodes of the graph,
-- 
-- * an integer /r/ which determines the size /R=//2/[sup /r/] of tuples in the Hamming
-- graph, 
--
-- * a function /edge_oracle/ which inputs two graph nodes and a qubit and flips the qubit 
-- if the nodes are connected by an edge and
--
-- * additional options, for selecting, e.g., which qRAM implementation should be used.
type QWTFP_spec = (Int, Int, QNode -> QNode -> Qubit -> Circ Qubit, Qram)

-- ======================================================================
-- * TF integers

-- ----------------------------------------------------------------------
-- ** Types

-- $ We define a 'QData' family of integer datatypes ('QIntTF',
-- 'CIntTF', 'IntTF'). These are similar to ('QDInt', 'CInt', 'IntM'),
-- except that the integers are considered to be mod 2[sup /m/]-1 instead
-- of 2[sup /m/].
-- 
-- In general, functions on these types should be able to handle both 00…00 and 11…11, 
-- and should treat them equally, essentially regarding 'IntTF', 'CIntTF', and the 
-- computational basis of 'QIntTF' as formal quotients.
-- Some operations are not perfect. One should keep in mind, for example, that specifying 
-- a control on a 'QIntTF' of the form @/q/ .==. 0@ will compare the bitwise representation 
-- to 0, and not the logical quotient.

-- | All three types 'QIntTF', 'CIntTF', and 'IntTF' are special cases
-- of a more general type 'XIntTF' /x/, parameterized by a type /x/ of
-- bits. It is an abstract type, and details of its implementation is
-- not exposed to user-level code.
data XIntTF x = XIntTF (XInt x)
  deriving (Show, Typeable)
                
-- | The type of fixed-length /m/-qubit quantum integers, regarded
-- modulo 2[sup /m/]-1.
type QIntTF = XIntTF Qubit

-- | The type of fixed-length /m/-bit classical integers, regarded
-- modulo 2[sup /m/]-1.
type CIntTF = XIntTF Bit

-- | The type of fixed-length /m/-bit integer parameters, regarded
-- modulo 2[sup /m/]-1. A value of type 'IntTF' may have indeterminate
-- length, similarly to 'IntM'.
type IntTF = XIntTF Bool

-- ----------------------------------------------------------------------
-- ** Operations for IntTF

-- | Convert an 'IntTF' of length /m/ to an 'Integer' in the range {0,
-- …, 2[sup /m/]-2}. If the 'IntTF' has indeterminate length, return
-- the original 'Integer'.
integer_of_inttf :: IntTF -> Integer
integer_of_inttf (XIntTF x) = 
  case intm_length x of
    Just m -> (integer_of_intm_unsigned x) `mod` (2^m - 1)
    Nothing -> integer_of_intm_unsigned x

-- | Convert an 'Integer' to an 'IntTF' of indeterminate length.
inttf_of_integer :: Integer -> IntTF
inttf_of_integer n = XIntTF (intm_of_integer n)

-- | Convert an 'Integer' to an 'IntTF' of length /m/.
inttf :: Int -> Integer -> IntTF
inttf m n = XIntTF (intm m n') 
  where
    n' = n `mod` (2^m-1)

-- | Return the length of an 'IntTF', or 'Nothing' if indeterminate.
inttf_length :: IntTF -> Maybe Int
inttf_length = intm_length . xint_of_xinttf

instance Eq IntTF where
  x == y =
    case inttf_length x' of 
      Just m -> (integer_of_inttf x') `mod` (2^m - 1) == (integer_of_inttf y') `mod` (2^m - 1)
      Nothing -> x' == y'
      where
        x' = inttf_promote x y errstr 
        y' = inttf_promote y x errstr
        errstr = "Equality test on IntTF: operands must be of equal length"

-- | Set the length of an 'IntTF' to /m/ ≥ 0. This operation is only
-- legal if the input (a) has indeterminate length or (b) has
-- determinate length already equal to /m/. In particular, it cannot
-- be used to change the length from anything other than from
-- indeterminate to determinate. 
-- 
-- If both arguments already have determinate lengths, and they do not
-- coincide, throw an error. The 'String' argument is used as an error
-- message in that case.
inttf_set_length :: Int -> IntTF -> String -> IntTF
inttf_set_length m (XIntTF x) errmsg | m < 0 =
  error "inttf_set_length: negative length not permitted"
inttf_set_length m (XIntTF x) errmsg =
  case intm_length x of
    Just n | m==n -> (XIntTF x)
           | otherwise -> error errmsg
    Nothing -> XIntTF (intm m n)
      where
        -- Here "unsigned" or "signed" doesn't matter, since this is
        -- the indeterminate case, where the original integer is
        -- returned.
        n = integer_of_intm_unsigned x `mod` (2^m - 1)

-- | Try to set the length of an 'IntTF' to that of another 'XIntTF'
-- value (which could be a 'QIntTF', a 'CIntTF', or another 'IntTF'). This
-- will fail with an error if both numbers already have determinate
-- lengths that don't coincide. In this case, the string argument is
-- used as an error message. The promotion is done modulo 2[sup /m/]-1.
inttf_promote :: IntTF -> XIntTF x -> String -> IntTF
inttf_promote b (XIntTF x) errmsg =
  case xint_maybe_length x of
    Nothing -> b
    Just m -> inttf_set_length m b errmsg

-- | Convert an 'IntTF' to human readable form. We show the bit value,
-- i.e., 0 and 2[sup /m/]-1 are shown as different values. 
show_inttf :: IntTF -> String
show_inttf x = 
  case inttf_length x of
    Nothing -> "IntTF -- " ++ show (integer_of_inttf x)
    Just m -> "IntTF " ++ show m ++ " " ++ show (integer_of_intm_unsigned (xint_of_xinttf x))

-- make 'IntTF' an (overlapping) instance of 'Show':
instance Show IntTF where
  show = show_inttf

-- ----------------------------------------------------------------------
-- ** Operations for QIntTF
    
-- | Convert a 'QIntTF' to a list of qubits. The conversion is
-- little-headian, i.e., the head of the list holds the least
-- significant digit.
qulist_of_qinttf_lh :: QIntTF -> [Qubit]
qulist_of_qinttf_lh = reverse . qulist_of_qdint_bh . xint_of_xinttf

-- | Convert a list of qubits to a 'QIntTF'. The conversion is
-- little-headian, i.e., the head of the list holds the least
-- significant digit.
qinttf_of_qulist_lh :: [Qubit] -> QIntTF
qinttf_of_qulist_lh = xinttf_of_xint . qdint_of_qulist_bh . reverse

-- | Return a piece of shape data to represent an /m/-qubit
-- 'QIntTF'. Please note that the data can only be used as shape; it
-- will be undefined at the leaves.
qinttf_shape :: Int -> QIntTF
qinttf_shape = xinttf_of_xint . qdint_shape

-- ----------------------------------------------------------------------
-- ** Auxiliary functions

-- | The low-level isomorphism from 'XInt' /x/ to 'XIntTF' /x/. Note
-- that \"isomorphism\" is between the underlying raw types, and does not
-- respect the arithmetic operations.
xinttf_of_xint :: XInt x -> XIntTF x
xinttf_of_xint = XIntTF

-- | The low-level isomorphism from 'XIntTF' /x/ to 'XInt' /x/.  Note
-- that \"isomorphism\" is between the underlying raw types, and does not
-- respect the arithmetic operations.
xint_of_xinttf :: XIntTF x -> XInt x
xint_of_xinttf (XIntTF x) = x

-- | Like 'xint_of_xinttf', but first try to promote the length of the
-- 'IntTF' to that of the given 'XIntTF'.
xint_with_promote :: XIntTF y -> IntTF -> IntM
xint_with_promote x b = xint_of_xinttf b' where
  b' = inttf_promote b x "xint_with_promote: length change not permitted"

-- ----------------------------------------------------------------------
-- The QCData instance

type instance QCType x y (XIntTF z) = XIntTF (QCType x y z)
type instance QTypeB IntTF = QIntTF

instance QCLeaf x =>  QCData (XIntTF x) where
  qcdata_mapM shape f g xs = 
    mmap xinttf_of_xint $ qcdata_mapM (xint_of_xinttf shape) f g (xint_of_xinttf xs)
  qcdata_zip shape q c q' c' xs ys e = 
    xinttf_of_xint $ qcdata_zip (xint_of_xinttf shape) q c q' c' (xint_of_xinttf xs) (xint_of_xinttf ys) errmsg
    where
      errmsg x = e "QDInt length mismatch"
  qcdata_promote b q e = inttf_promote b q errmsg
    where
      errmsg = e "IntM length mismatch"
    
-- Labeling of QIntTF is s[m-1], ..., s[0], with the least significant
-- bit at index 0.
instance QCLeaf x => Labelable (XIntTF x) String where
  label_rec qa = label_rec (xint_of_xinttf qa)

-- ======================================================================
-- * Miscellaneous circuit-building functions
  

-- | Controlled phase flip of -1.
phaseFlipIf :: (ControlSource ctrl) => ctrl -> Circ ()
phaseFlipIf ctrl = do
  -- why would one do an uncontrolled phase flip? Because it could be
  -- part of a subroutine that will later get controlled.
  global_phase 1.0 `controlled` ctrl

-- | Variant of 'phaseFlip' that performs a phase flip /unless/ all
-- controls are in the given state.
phaseFlipUnless :: (ControlSource ctrl) => ctrl -> Circ ()
phaseFlipUnless ctrls = do
  global_phase 1.0
  global_phase 1.0 `controlled` ctrls

-- | @qor q c@: Applies \"not\" to /q/, if /any/ of the control qubits
-- in /c/ is in specified state.
qor :: Qubit -> [(Qubit,Bool)] -> Circ Qubit
qor q cs = do
  q <- qnot q
  q <- qnot q `controlled` (map (\(p,b) -> (p .==. not b)) cs)
  return q

-- ======================================================================
-- * Arithmetic functions

-- | Increment a standard 'QDInt' (i.e. big-endian, mod 2[sup ℓ]).
increment :: QDInt -> Circ QDInt
increment x = do
  comment_with_label "ENTER: increment" x "x"
  x <- mmap qdint_of_qulist_bh . increment_big . qulist_of_qdint_bh $ x
  comment_with_label "EXIT: increment" x "x"
  return x
 
-- | Decrement a standard 'QDInt' (i.e. big-endian, mod 2[sup ℓ]).
decrement :: QDInt -> Circ QDInt
decrement x = do
  comment_with_label "ENTER: decrement" x "x"
  x <- mmap qdint_of_qulist_bh . decrement_big . qulist_of_qdint_bh $ x
  comment_with_label "EXIT: decrement" x "x"
  return x

-- | Increment a bit-string, considered as a big-endian integer mod 2[sup ℓ].
increment_big :: [Qubit] -> Circ [Qubit]
increment_big [] = return []
increment_big (i_high:i_lower) = do
      i_high <- qnot i_high `controlled` i_lower
      i_lower <- increment_big i_lower
      return (i_high:i_lower)
 
-- | Decrement a bit-string, considered as a big-endian integer mod 2[sup ℓ].
decrement_big :: [Qubit] -> Circ [Qubit]
decrement_big [] = return []
decrement_big (i_high:i_lower) = do
      i_lower <- decrement_big i_lower
      i_high <- qnot i_high `controlled` i_lower
      return (i_high:i_lower)

-- | Increment a bit-string, considered as a little-endian integer mod 2[sup ℓ].
increment_little :: [Qubit] -> Circ [Qubit]
increment_little [] = return []
increment_little (i_low:i_higher) = do
  i_higher <- increment_little i_higher `controlled` i_low
  i_low <- qnot i_low
  return (i_low:i_higher)

-- | Decrement a bit-string, considered as a little-endian integer mod 2[sup ℓ].
decrement_little :: [Qubit] -> Circ [Qubit]
decrement_little [] = return []
decrement_little (i_low:i_higher) = do
  i_low <- qnot i_low
  i_higher <- decrement_little i_higher `controlled` i_low
  return (i_low:i_higher)

-- | The standard “combinations” function “/n/ choose /k/”.
choose :: (Integral a) => a -> a -> a
choose n 0 = 1
choose 0 k = 0
choose n k = ((choose (n-1) (k-1)) * n) `div` k

-- ======================================================================
-- * IntMaps as QData

-- | Replace an 'IntMap' /f/ with the 'IntMap' mapping each key /k/ to (/k/,/f(k)/).  An auxiliary function for defining 'mapWithKeyM', etc.
addKeys :: IntMap a -> IntMap (Key,a)
addKeys = IntMap.mapWithKey (\k x -> (k,x))

-- | Analogous to 'mapM', but allows the function to use the key.  Particularly useful for mapping in parallel over two (or more) 'IntMap's assumed to have the same domain. 
mapWithKeyM :: (Monad m) => (IntMap.Key -> a -> m b) -> IntMap a -> m (IntMap b) 
mapWithKeyM f as =  mapM (\(k,x) -> f k x) (addKeys as)

-- | Analogous to 'mapM_', but allows the function to use the key.
mapWithKeyM_ :: (Monad m) => (IntMap.Key -> a -> m b) -> IntMap a -> m () 
mapWithKeyM_ f as = mapM_ (\(k,x) -> f k x) (addKeys as)

-- | Analogous to 'replicate' on lists.
intMap_replicate :: Int -> a -> IntMap a
intMap_replicate n x = IntMap.fromList [(i,x) | i <- [0..n-1]]

infixl 9 !

-- | Convenient syntax for accessing elements of an 'IntMap'.  Left associative, and binds very strongly, like '(!!)'.
(!) :: IntMap a -> IntMap.Key -> a
xs ! k = let (Just x) = IntMap.lookup k xs in x
 
type instance QCType x y (IntMap a) = IntMap (QCType x y a)
type instance QTypeB (IntMap a) = IntMap (QTypeB a)

instance QCData a => QCData (IntMap a) where
  qcdata_mapM a f g xs =
    intmap_mapM (qcdata_mapM a' f g) xs
      where a' = shape $ a IntMap.! 0
  
  qcdata_zip a q c q' c' xs ys e =
    intmap_map (\(x,y) -> qcdata_zip a' q c q' c' x y e) (intmap_zip_errmsg xs ys errmsg)
      where 
        a' = shape $ a IntMap.! 0
        errmsg = e "IntMap domains do not agree"
  
  qcdata_promote as xs e
    | IntMap.keys as /= IntMap.keys xs = error errmsg
    | otherwise =
        intmap_map (\(a,x) -> qcdata_promote a x e) (intmap_zip_errmsg as xs errmsg)
    where
      errmsg = e "IntMap domains do not agree"
                
instance (Labelable a String) => Labelable (IntMap a) String where
  label_rec xs s = do
    sequence_ [ label_rec x s `indexed` show i | (i,x) <- IntMap.toList xs ]
    
instance (Labelable a s) => Labelable (IntMap a) (IntMap s) where
  label_rec xs ss = do
    sequence_ [ label_rec x s | (i,x) <- IntMap.toList xs, IntMap.member i ss, let s = ss IntMap.! i ]
