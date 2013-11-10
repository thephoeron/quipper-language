-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module provides miscellaneous general-purpose auxiliary
-- functions.

module Libraries.Auxiliary (
  -- * List operations
  applyAt,
  overwriteAt,
  has_duplicates,
  substitute,
  
  -- * Set and Map related operations
  map_provide,
  intset_inserts,
  intmap_zip,
  intmap_zip_errmsg,
  intmap_map,
  intmap_mapM,
  
  -- * XIntMaps
  XIntMap,
  xintmap_delete,
  xintmap_deletes,
  xintmap_insert,
  xintmap_inserts,
  xintmap_lookup,
  xintmap_member,
  xintmap_empty,
  xintmap_freshkey,
  xintmap_freshkeys,
  xintmap_to_intmap,
  xintmap_size,
  xintmap_dirty,
  xintmap_reserves,
  xintmap_unreserves,  
  xintmap_makeclean,
  
  -- * Various map- and fold-like list combinators
  loop,
  loop_with_index,
  fold_right_zip,
  zip_strict,
  zip_strict_errmsg,
  zip_rightstrict,
  zip_rightstrict_errmsg,
  zipWith_strict,
  zipWith_rightstrict,
  
  -- * Monadic versions of list combinators
  loopM,
  loop_with_indexM,
  zipRightWithRightStrictM,
  zipRightWithRightStrictM_,
  fold_right_zipM,
  foldRightPairM,
  foldRightPairM_,
  sequence_right,
  sequence_right_,
  
  -- * Loops
  -- $LOOPS
  for,
  endfor,
  foreach,
  
  -- * Operations for monads
  mmap,
  monad_join1,
  
  -- * Operations for disjoint unions
  map_either,
  map_eitherM,
  
  -- * Operations for tuples
  map_pair,
  map_pairM,
  
  -- * Arithmetic operations
  int_ceiling,
  
  -- * Bit vectors
  Boollist(..),
  boollist_of_int_bh,
  boollist_of_int_lh,
  int_of_boollist_unsigned_bh,
  int_of_boollist_signed_bh,
  bool_xor,
  boollist_xor,
  
  -- * Formatting of lists and strings
  string_of_list,
  optional,
  
  -- * Lists optimized for fast concatenation
  BList,
  blist_of_list,
  list_of_blist,
  (+++),
  blist_empty,
  blist_concat,
  
  -- * Strings optimized for fast concatenation
  Strbuf,
  strbuf_of_string,
  string_of_strbuf,
  strbuf_empty,
  strbuf_concat,
  
  -- * The identity monad
  Id(..),
  
  -- * Identity types
  Identity,
  reflexivity,
  symmetry,
  transitivity,
  identity,
  
  -- * Error messages
  ErrMsg,
  
  -- * The Curry type class
  Curry (..)
  ) where

-- import other stuff
import Data.List (foldl')

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import qualified Data.Traversable as Traversable

-- ----------------------------------------------------------------------
-- * List operations

-- | Apply a function to a specified position in a list.
applyAt :: Int -> (a -> a) -> [a] -> [a]
applyAt _ _ [] = []
applyAt 0 f (x:xs) = (f x):xs
applyAt n f (x:xs) = x:(applyAt (n-1) f xs)

-- | Overwrite an element at a specified position in a list.
overwriteAt :: Int -> a -> [a] -> [a]
overwriteAt n a = applyAt n (const a)

-- | Check whether a list has duplicates.
has_duplicates :: Ord a => [a] -> Bool
has_duplicates list = aux list (Set.empty) where
  aux [] _ = False
  aux (h:t) set = if Set.member h set then True else aux t (Set.insert h set)

-- | @'substitute' string character replacement@: 
-- Replace the first occurrence of /character/ in /string/ by /replacement/.
substitute :: (Eq a) => [a] -> a -> [a] -> [a]
substitute string character replacement =    
  case break (== character) string of
    (x, []) -> x
    (x, h:y) -> x ++ replacement ++ y

-- ----------------------------------------------------------------------
-- * Set related operations

-- | Insert the elements of a list in an 'IntSet' (cf. 'IntSet.insert').
intset_inserts :: [Int] -> IntSet -> IntSet
intset_inserts list set =
  foldl' (\t x -> IntSet.insert x t) set list


-- ----------------------------------------------------------------------
-- * Map related operations

-- | Insert the given key-value pair in a 'Map', but only if the given
-- key is not already present. If the key is present, keep the old
-- value.
map_provide :: Ord k => k -> a -> Map k a -> Map k a
map_provide = Map.insertWith (\x y -> y)

-- | Take two 'IntMap's /m/[sub 1] and /m/[sub 2], and form a new
-- 'IntMap' whose domain is that of /m/[sub 2], and whose value at /k/
-- is the pair (/m/[sub 1] ! /k/, /m/[sub 2] ! /k/). It is an error if
-- the domain of /m/[sub 2] is not a subset of the domain of /m/[sub 1].
intmap_zipright :: IntMap x -> IntMap y -> IntMap (x, y)
intmap_zipright m1 m2 = m where
  m = IntMap.mapWithKey f m2
  f k y = case IntMap.lookup k m1 of
    Just x -> (x, y)
    Nothing -> error "intmap_zipright: shape mismatch"
  
-- | Take two 'IntMap's with the same domain, and form a new 'IntMap'
-- whose values are pairs. It is an error if the two inputs don't have
-- identical domains.
intmap_zip :: IntMap x -> IntMap y -> IntMap (x, y)
intmap_zip m1 m2 = intmap_zip_errmsg m1 m2 "intmap_zip: shape mismatch"
  
-- | Like 'intmap_zip', but also takes an error message to use in case of
-- domain mismatch.
intmap_zip_errmsg :: IntMap x -> IntMap y -> String -> IntMap (x, y)
intmap_zip_errmsg m1 m2 errmsg = 
  if all (\k -> IntMap.member k m2) (IntMap.keys m1) 
    then intmap_zipright m1 m2
    else error errmsg
  
-- | Map a function over all values in an 'IntMap'.
intmap_map :: (x -> y) -> IntMap x -> IntMap y
intmap_map = IntMap.map

-- | Monadic version of 'intmap_map'. Map a function over all values
-- in an 'IntMap'.
intmap_mapM :: (Monad m) => (x -> m y) -> IntMap x -> m (IntMap y)
intmap_mapM = Traversable.mapM

-- ----------------------------------------------------------------------
-- * XIntMaps. 

-- | A 'XIntMap' is just like an 'IntMap', except that it supports
-- some additional efficient operations: to find the smallest unused
-- key, to find the set of all keys ever used in the past, and to
-- reserve a set of keys so that they will not be allocated. Moreover,
-- it keeps track of the highest key ever used (whether or not it is
-- still used in the current map).

-- This is implemented as a tuple (/m/, /n/, /free/, /h/), where /m/ is an
-- 'IntMap', /n/ is an integer such that dom /m/ ⊆ [0../n/-1], /free/
-- ⊆ [0../n/-1] \\ dom /m/ is a set of integers not currently reserved
-- or used, and /h/ is the set of all integers used in the past (the
-- set of /touched/ wires).

data XIntMap a = XIntMap !(IntMap a) !Int !IntSet !IntSet

instance (Show a) => Show (XIntMap a) where
  show = show . xintmap_to_intmap
    
-- | Delete a key from the 'XIntMap'.
xintmap_delete :: Int -> XIntMap a -> XIntMap a
xintmap_delete k (XIntMap m n free h) = (XIntMap m' n free' h) where
  m' = IntMap.delete k m
  free' = IntSet.insert k free
  
-- | Delete a list of keys from a 'XIntMap'.
xintmap_deletes :: [Int] -> XIntMap a -> XIntMap a
xintmap_deletes list map =
  foldl' (\map k -> xintmap_delete k map) map list

-- | Insert a new key-value pair in the 'XIntMap'. 
xintmap_insert :: Int -> a -> XIntMap a -> XIntMap a
xintmap_insert k v (XIntMap m n free h) = (XIntMap m' n' free' h') where
  m' = IntMap.insert k v m
  h' = IntSet.insert k h
  n' = max n (k+1)
  free' = IntSet.delete k (intset_inserts [n..n'-1] free)

-- | Insert a list of key-value pairs in the 'XIntMap'.
xintmap_inserts :: [(Int,a)] -> XIntMap a -> XIntMap a
xintmap_inserts list map =
  foldl' (\map (k,v) -> xintmap_insert k v map) map list

-- | Look up the value at a key in the 'XIntMap'. Return 'Nothing' if
-- not found.
xintmap_lookup :: Int -> XIntMap a -> Maybe a
xintmap_lookup k (XIntMap m n free h) =
  IntMap.lookup k m

-- | Check whether the given key is in the 'XIntMap'.
xintmap_member :: Int -> XIntMap a -> Bool
xintmap_member k (XIntMap m n free h) =
    IntMap.member k m

-- | The empty 'XIntMap'.
xintmap_empty :: XIntMap a
xintmap_empty = (XIntMap m n free h) where
  m = IntMap.empty
  n = 0
  free = IntSet.empty
  h = IntSet.empty

-- | Return the first free key in the 'XIntMap', but without actually
-- using it yet.
xintmap_freshkey :: XIntMap a -> Int
xintmap_freshkey (XIntMap m n free h) = 
  if IntSet.null free then n else IntSet.findMin free

-- | Return the next /k/ unused keys in the 'XIntMap', but without
-- actually using them yet.
xintmap_freshkeys :: Int -> XIntMap a -> [Int]
xintmap_freshkeys k (XIntMap m n free h) = ks1 ++ ks2 where
  ks1 = take k (IntSet.elems free)
  delta = k - (length ks1)
  ks2 = [n .. n+delta-1]

-- | Convert a 'XIntMap' to an 'IntMap'.
xintmap_to_intmap :: XIntMap a -> IntMap a
xintmap_to_intmap (XIntMap m n free h) = m

-- | Return the smallest key never used in the 'XIntMap'.
xintmap_size :: XIntMap a -> Int
xintmap_size (XIntMap m n free k) = n

-- | Return the set of all keys ever used in the 'XIntMap'.
xintmap_touched :: XIntMap a -> IntSet
xintmap_touched (XIntMap m n free h) = h 

-- | A wire is /dirty/ if it is touched but currently free. 
xintmap_dirty :: XIntMap a -> IntSet
xintmap_dirty (XIntMap m n free h) = h `IntSet.intersection` free

-- | Reserve a key in the 'XIntMap'. If the key is not free, do
-- nothing. The key must have been used before; for example, this is
-- the case if it was returned by 'xintmap_dirty'.
xintmap_reserve :: Int -> XIntMap a -> XIntMap a
xintmap_reserve k (XIntMap m n free h) = (XIntMap m n free' h) where
  free' = IntSet.delete k free
  
-- | Reserve a set of keys in the 'XIntMap'. For any keys that are not
-- free, do nothing. All keys must have been used before; for example,
-- this is the case if they were returned by 'xintmap_dirty'.
xintmap_reserves :: IntSet -> XIntMap a -> XIntMap a
xintmap_reserves ks (XIntMap m n free h) = (XIntMap m n free' h) where
  free' = free `IntSet.difference` ks

-- | Unreserve a key in the 'XIntMap'. If the key is currently used,
-- do nothing. The key must have been reserved before, and (therefore)
-- must have been used before.
xintmap_unreserve :: Int -> XIntMap a -> XIntMap a
xintmap_unreserve k (XIntMap m n free h) 
  | IntMap.member k m = (XIntMap m n free h)
  | otherwise = (XIntMap m n free' h)
    where
      free' = IntSet.insert k free

-- | Unreserve a list of keys in the 'XIntMap'. If any key is
-- currently used, do nothing. All keys must have been reserved
-- before, and (therefore) must have been used before.
xintmap_unreserves :: IntSet -> XIntMap a -> XIntMap a
xintmap_unreserves ks map = 
  IntSet.fold (\k map -> xintmap_unreserve k map) map ks

-- | Make an exact copy of the 'XIntMap', except that the set of
-- touched wires is initially set to the set of used wires. In other
-- words, we mark all free and reserved wires as untouched.
xintmap_makeclean :: XIntMap a -> XIntMap a
xintmap_makeclean (XIntMap m n free h) = (XIntMap m n free h') where
  h' = IntMap.keysSet m

-- ----------------------------------------------------------------------
-- * Map- and fold-like list combinators

-- ** Combinators for looping

-- | Like 'loop', but also pass a loop counter to the function being
-- iterated. Example:
-- 
-- > loop_with_index 3 x f = f 2 (f 1 (f 0 x))
loop_with_index :: (Eq int, Num int) => int -> t -> (int -> t -> t) -> t
loop_with_index n x f = aux 0 x
  where
    aux i x = if i == n then x else aux (i+1) (f i x)

-- | Monadic version of 'loop_with_index'. Thus, 
-- 
-- > loop_with_indexM 3 x0 f
-- 
-- will do the following:
-- 
-- > do
-- >   x1 <- f 0 x0
-- >   x2 <- f 1 x1
-- >   x3 <- f 2 x2    
-- >   return x3
loop_with_indexM :: (Eq int, Num int, Monad m) => int -> t -> (int -> t -> m t) -> m t
loop_with_indexM n x f = aux 0 x
  where
    aux i x =
      if i == n then return x else do
        x <- f i x
        aux (i+1) x

-- | Iterate a function /n/ times. Example: 
-- 
-- > loop 3 x f = f (f (f x))
loop :: (Eq int, Num int) => int -> t -> (t -> t) -> t
loop n x f = loop_with_index n x (\_ -> f)

-- | Monadic version of 'loop'.
loopM :: (Eq int, Num int, Monad m) => int -> t -> (t -> m t) -> m t
loopM n x f = loop_with_indexM n x (\_ -> f)

-- ** Combinators for sequencing

-- | A right-to-left version of 'sequence': Evaluate each action in the
-- sequence from right to left, and collect the results.
sequence_right :: Monad m => [m a] -> m [a]
sequence_right [] = return []
sequence_right (x:xs) = do
  ys <- sequence_right xs
  y <- x
  return (y:ys)

-- | Same as 'sequence_right', but ignore the result.
sequence_right_ :: Monad m => [m a] -> m ()
sequence_right_ [] = return ()
sequence_right_ (x:xs) = do
  ys <- sequence_right_ xs
  y <- x
  return ()

-- ** Combinators for zipping

-- | A \"strict\" version of 'zip', i.e., raises an error when the
-- lists are not of the same length.
zip_strict :: [a] -> [b] -> [(a, b)]
zip_strict a b = zip_strict_errmsg a b "zip_strict: lists are not of the same length"

-- | Like 'zip_strict', but also takes an explicit error message to
-- use in case of failure.
zip_strict_errmsg :: [a] -> [b] -> String -> [(a, b)]
zip_strict_errmsg [] [] e = []
zip_strict_errmsg (h:t) (h':t') e = (h,h') : zip_strict_errmsg t t' e
zip_strict_errmsg _ _ e = error e

-- | A \"right strict\" version of 'zip', i.e., raises an error when the
-- left list is shorter than the right one. 
zip_rightstrict :: [a] -> [b] -> [(a, b)]
zip_rightstrict a b = zip_rightstrict_errmsg a b "zip_rightstrict: list too short"

-- | A version of 'zip_rightstrict' that also takes an explicit error
-- message to use in case of failure.
zip_rightstrict_errmsg :: [a] -> [b] -> String -> [(a, b)]
zip_rightstrict_errmsg _ [] s = []
zip_rightstrict_errmsg (h:t) (h':t') s = (h,h') : zip_rightstrict_errmsg t t' s
zip_rightstrict_errmsg _ _ s = error s

-- | A \"strict\" version of 'zipWith', i.e., raises an error when the
-- lists are not of the same length.
zipWith_strict :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith_strict f [] [] = []
zipWith_strict f (h:t) (h':t') = f h h' : zipWith_strict f t t'
zipWith_strict f _ _ = error "zipWith_strict: lists are not of the same length"

-- | A \"right strict\" version of 'zipWith', i.e., raises an error when the
-- right list is shorter than the left one.
zipWith_rightstrict :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith_rightstrict f _ [] = []
zipWith_rightstrict f (h:t) (h':t') = f h h' : zipWith_rightstrict f t t'
zipWith_rightstrict f _ _ = error "zipWith_rightstrict: list too short"

-- | A right-to-left version of 'zipWithM', which is also \"right
-- strict\", i.e., raises an error when the right list is shorter than
-- the left one. Example:
-- 
-- > zipRightWithM f [a,b] [x,y] = [f a x, f b y],
-- 
-- computed right-to-left.
zipRightWithRightStrictM :: (Monad m) => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipRightWithRightStrictM f l1 l2 =
  sequence_right $ zipWith_rightstrict f l1 l2

-- | Same as 'zipRightWithM', but ignore the result.
zipRightWithRightStrictM_ :: (Monad m) => (a -> b -> m c) -> [a] -> [b] -> m ()
zipRightWithRightStrictM_ f l1 l2 =
  sequence_right_ $ zipWith_rightstrict f l1 l2

-- ** Combinators combining mapping with folding

-- | Fold over two lists with state, and do it right-to-left.  For example,
-- 
-- > foldRightPairM (w0, [1,2,3], [a,b,c]) f
-- 
-- will do the following:
-- 
-- > do
-- >   w1 <- f (w0, 3, c)
-- >   w2 <- f (w1, 2, b)
-- >   w3 <- f (w2, 1, a)
-- >   return w3
foldRightPairM :: (Monad m) => (w, [a], [b]) -> ((w, a, b) -> m w) -> m w
foldRightPairM (w, [], _) f = return w
foldRightPairM (w, _, []) f = return w
foldRightPairM (w, a:as, b:bs) f = do
  w <- foldRightPairM (w, as, bs) f
  w <- f (w, a, b)
  return w

-- | Like 'foldRightPairM', but ignore the final result.
foldRightPairM_ :: (Monad m) => (w, [a], [b]) -> ((w, a, b) -> m w) -> m ()
foldRightPairM_ x f = do
  foldRightPairM x f
  return ()

-- | Combine right-to-left zipping and folding. Example:
-- 
-- > fold_right_zip f (w0, [a,b,c], [x,y,z]) = (w3, [a',b',c'])
-- >  where f (w0,c,z) = (w1,c')
-- >        f (w1,b,y) = (w2,b')
-- >        f (w2,a,x) = (w3,a')
fold_right_zip :: ((w, a, b) -> (w, c)) -> (w, [a], [b]) -> (w, [c])
fold_right_zip f (w, [], []) = (w, [])
fold_right_zip f (w, a:bb, x:yy) = (w2, a':bb')
  where
    (w1, bb') = fold_right_zip f (w, bb, yy)
    (w2, a') = f (w1, a, x)
fold_right_zip f _ = error "fold_right_zip"

-- | Monadic version of 'fold_right_zip'.
fold_right_zipM ::
  (Monad m) => ((w, a, b) -> m(w, c)) -> (w, [a], [b]) -> m(w, [c])
fold_right_zipM f (w, [], []) = return (w, [])
fold_right_zipM f (w, a:bb, x:yy) = do
    (w1, bb') <- fold_right_zipM f (w, bb, yy)
    (w2, a') <- f (w1, a, x)
    return (w2, a':bb')
fold_right_zipM f _ = error "fold_right_zipM"

-- ----------------------------------------------------------------------
-- * Loops.

-- $LOOPS We provide a syntax for \"for\"-style loops.

-- | A \"for\" loop. Counts from /a/ to /b/ in increments of /s/.
-- 
-- Standard notation: 
-- 
-- > for i = a to b by s do
-- >   commands             
-- > end for
-- 
-- Our notation: 
-- 
-- > for a b s $ \i -> do
-- >   commands
-- > endfor

for :: Monad m => Int -> Int -> Int -> (Int -> m()) -> m()
for a b s f = if s > 0 then aux a (<= b) else aux a (>= b)
  where
    aux i cond = 
      if cond i then do
        f i
        aux (i+s) cond
      else
        return ()

-- | Mark the end of a \"for\"-loop. This command actually does
-- nothing, but can be used to make the loop look prettier.
endfor :: Monad m => m()
endfor = return ()

-- | Iterate a parameter over a list of values. It can be used as
-- follows:
-- 
-- > foreach [1,2,3,4] $ \n -> do
-- >   <<<loop body depending on the parameter n>>>
-- > endfor
-- 
-- The loop body will get executed once for each /n/ ∈ {1,2,3,4}.

foreach :: Monad m => [a] -> (a -> m b) -> m ()
foreach l f = mapM_ f l

-- ----------------------------------------------------------------------
-- * Operations for monads

-- | Every monad is a functor. Input a function /f/ : /a/ → /b/ and output
-- /m/ /f/ : /m/ /a/ → /m/ /b/.
mmap :: (Monad m) => (a -> b) -> m a -> m b
mmap f a = a >>= (return . f)

-- | Remove an outer application of a monad from a monadic function.
monad_join1 :: (Monad m) => m (a -> m b) -> a -> m b
monad_join1 mf a = do
  f <- mf
  f a

-- ----------------------------------------------------------------------
-- * Operations for disjoint unions

-- | Take two functions /f/ : /a/ → /b/ and /g/ : /c/ → /d/, and return
-- /f/ ⊕ /g/ : /a/ ⊕ /c/ → /c/ ⊕ /d/.
map_either :: (a -> b) -> (c -> d) -> Either a c -> Either b d
map_either f g (Left x) = Left (f x)
map_either f g (Right x) = Right (g x)

-- | Monadic version of 'map_either'.
map_eitherM :: (Monad m) => (a -> m b) -> (c -> m d) -> Either a c -> m (Either b d)
map_eitherM f g (Left x) = mmap Left (f x)
map_eitherM f g (Right x) = mmap Right (g x)

-- ----------------------------------------------------------------------
-- * Operations for tuples

-- | Take two functions /f/ : /a/ → /b/ and /g/ : /c/ → /d/, and return
-- /f/ × /g/ : /a/ × /c/ → /c/ × /d/.
map_pair :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
map_pair f g (x, y) = (f x, g y)

-- | Monadic version of 'mappair'.
map_pairM :: (Monad m) => (a -> m b) -> (c -> m d) -> (a, c) -> m (b, d)
map_pairM f g (a, c) = do
  b <- f a
  d <- g c
  return (b, d)

-- ----------------------------------------------------------------------
-- * Arithmetic operations
  
-- | A version of the 'ceiling' function that returns an 'Integer'.
int_ceiling :: RealFrac a => a -> Integer
int_ceiling = toInteger . ceiling

-- ----------------------------------------------------------------------
-- * Bit vectors

-- | The type of bit vectors. True = 1, False = 0.
type Boollist = [Bool]

-- | Convert an integer to a bit vector. The first argument is the
-- length in bits, and the second argument the integer to be
-- converted. The conversion is big-headian (or equivalently,
-- little-tailian), i.e., the head of the list holds the integer's most
-- significant digit.
boollist_of_int_bh :: Integral a => Int -> a -> Boollist
boollist_of_int_bh m = reverse . boollist_of_int_lh m

-- | Convert an integer to a bit vector. The first argument is the
-- length in bits, and the second argument the integer to be
-- converted. The conversion is little-headian (or equivalently,
-- big-tailian), i.e., the head of the list holds the integer's least
-- significant digit.
boollist_of_int_lh :: Integral a => Int -> a -> Boollist
boollist_of_int_lh m x | m <= 0 = []
boollist_of_int_lh m x = digit : boollist_of_int_lh (m-1) tail where
  digit = (x `mod` 2 == 1)
  tail = x `div` 2

-- | Convert a bit vector to an integer. The conversion is big-headian
-- (or equivalently, little-tailian), i.e., the head of the list holds
-- the integer's most significant digit. This function is unsigned,
-- i.e., the integer returned is ≥ 0.
int_of_boollist_unsigned_bh :: Integral a => Boollist -> a
int_of_boollist_unsigned_bh v = aux v 0
  where
    aux v acc =
      case v of
        [] -> acc
        digit : vs -> aux vs (2*acc+(if digit then 1 else 0))

-- | Convert a bit vector to an integer, signed.
int_of_boollist_signed_bh :: Integral a => Boollist -> a
int_of_boollist_signed_bh [] = 0
int_of_boollist_signed_bh (False:v) = int_of_boollist_unsigned_bh v
int_of_boollist_signed_bh (True:v) = -1 - int_of_boollist_unsigned_bh (map not v)

-- | Exclusive or operation on booleans.
bool_xor :: Bool -> Bool -> Bool
bool_xor a b = (a /= b)

-- | Exclusive or operation on bit vectors.
boollist_xor :: Boollist -> Boollist -> Boollist
boollist_xor = zipWith bool_xor

-- ----------------------------------------------------------------------
-- * Formatting of lists and strings

-- | A general list-to-string function. Example:
-- 
-- > string_of_list "{" ", " "}" "{}" show [1,2,3] = "{1, 2, 3}"
string_of_list :: String -> String -> String -> String -> (t -> String) -> [t] -> String
string_of_list lpar comma rpar nil string_of_elt lst =
  let string_of_tail lst =
        case lst of
          [] -> ""
          h:t -> comma ++ string_of_elt h ++ string_of_tail t
  in
  case lst of
    [] -> nil
    h:t -> lpar ++ string_of_elt h ++ string_of_tail t ++ rpar

-- | @'optional' b s@: if /b/ = 'True', return /s/, else the empty
-- string. This function is for convenience.
optional :: Bool -> String -> String
optional True s = s
optional False s = ""

-- ----------------------------------------------------------------------
-- * Lists optimized for fast concatenation

-- | The type of bidirectional lists. This is similar to [a], but
-- optimized for fast concatenation and appending on both sides.
newtype BList a = BList { getBList :: [a] -> [a] }

-- | Convert a List to a 'BList'.
blist_of_list :: [a] -> BList a
blist_of_list s = BList (\x -> s ++ x)

-- | Convert a 'BList' to a List.
list_of_blist :: BList a -> [a]
list_of_blist buf = getBList buf []

-- | Fast concatenation of 'BList's or string buffers.
(+++) :: BList a -> BList a -> BList a
(+++) buf1 buf2 = BList ((getBList buf1) . (getBList buf2))

-- | The empty 'BList'.
blist_empty :: BList a
blist_empty = BList id

-- | Concatenate a list of 'Blist's.
blist_concat :: [BList a] -> BList a
blist_concat l = foldr (+++) blist_empty l

instance (Show a) => Show (BList a) where
	show bl = show (list_of_blist bl) 

-- ----------------------------------------------------------------------
-- * Strings optimized for fast concatenation

-- | A string buffer holds a string that is optimized for fast
-- concatenation. Note that this is an instance of 'BList', and hence
-- 'BList' operations (in particular '+++') can be applied to string
-- buffers. The following functions are synonyms of the respective
-- 'BList' functions, and are provided for convenience.
type Strbuf = BList Char

-- | Convert a string to a string buffer.
strbuf_of_string :: String -> Strbuf
strbuf_of_string = blist_of_list

-- | Convert a string buffer to a string.
string_of_strbuf :: Strbuf -> String
string_of_strbuf = list_of_blist

-- | The empty string buffer.
strbuf_empty :: Strbuf
strbuf_empty = blist_empty

-- | Concatenate a list of string buffers.
strbuf_concat :: [Strbuf] -> Strbuf
strbuf_concat = blist_concat

-- ----------------------------------------------------------------------
-- * The identity monad
      
-- | The identity monad. Using /m/ = 'Id' gives useful special cases
-- of monadic functions.
newtype Id a = Id { getId :: a }

instance Monad Id where
  return a = Id a
  (Id a) >>= b = b a

-- ----------------------------------------------------------------------
-- * Identity types
  
-- | The type 'Identity' /a/ /b/ witnesses the fact that /a/ and /b/
-- are the same type. In other words, this type is non-empty if and
-- only if /a/ = /b/. This property is not guaranteed by the type
-- system, but by the API, via the fact that the operators
-- 'relexivity', 'symmetry', and 'transitivity' are the only exposed
-- constructors for this type. The implementation of this type is
-- deliberately hidden, as this is the only way to guarantee its
-- defining property.
-- 
-- Identity types are useful in certain situations. For example, they
-- can be used to define a data type which is polymorphic in some type
-- variable /x/, and which has certain constructors that are only
-- available when /x/ is a particular type. For example, in the
-- declaration
-- 
-- > data ExampleType x = Constructor1 x | Constructor2 x (Identity x Bool),
-- 
-- @Constructor1@ is available for all /x/, but @Constructor2@ is only
-- available when /x/ = 'Bool'.
newtype Identity a b = Identity (a -> b, b -> a)

-- | Witness the fact that /a/=/a/.
reflexivity :: Identity a a
reflexivity = Identity (id, id)

-- | Witness the fact that /a/=/b/ implies /b/=/a/.
symmetry :: Identity a b -> Identity b a
symmetry (Identity (f,g)) = Identity (g,f)

-- | Witness the fact that /a/=/b/ and /b/=/c/ implies /a/=/c/.
transitivity :: Identity a b -> Identity b c -> Identity a c
transitivity (Identity (f,g)) (Identity (f',g')) = Identity (f'',g'') where
  f'' = f' . f
  g'' = g . g'

-- | The identity function 'id' : /a/ → /b/, provided that /a/ and /b/
-- are the same type.
identity :: Identity a b -> a -> b
identity (Identity (f,g)) = f

instance Show (Identity a b) where
  show x = "id"

-- ----------------------------------------------------------------------
-- * Isomorphism types

-- | The type 'Isomorphism' /a/ /b/ consists of isomorphisms between
-- /a/ and /b/, i.e. pairs (/f/,/g/) such that /g/./f/ == id :: /a/ -> /a/,
-- /f/./g/ == id :: /b/ -> /b/. 
--
-- As with e.g. Haskell’s 'Monad' class, it is not possible in general
-- to guarantee that the intended laws hold; it is the programmer’s
-- responsibility to ensure this.
--
-- Under the hood, 'Isomorphism' and 'Identity' are in fact the same;
-- they differ just in the API exposed. 
newtype Isomorphism a b = Isomorphism (a -> b, b -> a)

-- | Map forwards along an isomorphism.
iso_forwards :: Isomorphism a b -> a -> b
iso_forwards (Isomorphism (f,g)) = f

-- | Map backwards along an isomorphism.
iso_backwards :: Isomorphism a b -> b -> a
iso_backwards (Isomorphism (f,g)) = g

-- ======================================================================
-- * Error messages

-- | Often a low-level function, such as 'qcdata_zip' and
-- 'qcdata_promote', throws an error because of a failure of some
-- low-level condition, such as \"list too short\". To produce error
-- messages that are meaningful to user-level code, these functions do
-- not have a hard-coded error message. Instead, they input a stub
-- error message.
-- 
-- A meaningful error message typically consists of at least three parts:
-- 
-- * the name of the user-level function where the error occurred, for
-- example: \"reverse_generic\";
-- 
-- * what the function was doing when the error occurred, for example:
-- \"operation not permitted in reversible circuit\";
-- 
-- * a specific low-level reason for the error, for example: \"dynamic
-- lifting\".
-- 
-- Thus, a meaningful error message may be: \"reverse_generic:
-- operation not permitted in reversible circuit: dynamic lifting\".
-- 
-- The problem is that the three pieces of information are not usually
-- present in the same place. The user-level function is often a
-- wrapper function that performs several different mid-level
-- operations (e.g., transforming, reversing). The mid-level function
-- knows what operation was being performed when the error occurred,
-- but often calls a lower-level function to do the actual work (e.g.,
-- encapsulating).
--   
-- Therefore, a stub error message is a function that inputs some
-- lower-level reason for a failure (example: \"list too short\") and
-- translates this into a higher-level error message (example:
-- \"qterm: shape of parameter does not data: list too short\").
-- 
-- Sometimes, the stub error message may also ignore the low-level
-- message and completely replace it by a higher-level one. For
-- example, a function that implements integers as bit lists may wish
-- to report a problem with integers, rather than a problem with the
-- underlying lists.
type ErrMsg = String -> String

-- ======================================================================
-- * The Curry type class

-- | The 'Curry' type class is used to implement functions that have a
-- variable number of arguments. It provides a family of type
-- isomorphisms
-- 
-- @fun  ≅  args -> res,@
-- 
-- where
-- 
-- > fun = a1 -> a2 -> ... -> an -> res,
-- > args = (a1, (a2, (..., (an, ())))).

class Curry fun args res | args res -> fun where
  -- | Multiple curry: map a function 
  -- (/a/[sub 1], (/a/[sub 2], (…, ())) → /b/ 
  -- to its curried form 
  -- /a/[sub 1] → /a/[sub 2] → … → /b/.
  mcurry :: (args -> res) -> fun
  -- | Multiple uncurry: map a function
  -- /a/[sub 1] → /a/[sub 2] → … → /b/
  -- to its uncurried form 
  -- (/a/[sub 1], (/a/[sub 2], (…, ())) → /b/.
  muncurry :: fun -> (args -> res)
               
instance Curry b () b where
  mcurry g = g ()
  muncurry x = const x

instance Curry fun args res => Curry (a -> fun) (a,args) res where
  mcurry g x = mcurry (\xs -> g (x,xs))
  muncurry f (x,xs) = muncurry (f x) xs
                
