-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- --------------------------------------------------------------------
-- | This module provides functions for generating lists of samples
-- from a range of input values. This is primarily useful for
-- generating test cases. Ranges can be specified for types that are
-- members of the 'Interval' class. Each sampling procedure generates
-- a (finite or infinite) list of values from the range. We provide
-- sampling procedures for
-- 
-- * generating the range in its entirety ('sample_all')
-- 
-- * sampling every /n/th element from a range ('sample_step')
-- 
-- * generating a random sample from the range ('sample_random')

module Libraries.Sampling (
  
  -- * Interval class
  Interval(..),
  
  -- * Zero class
  Zero(..),
  
  -- * Random class
  -- $Random
  Random,
  
  -- * Functions
  sample_all,
  sample_step,
  sample_random,
  sample_all0,
  sample_step0,
  sample_random0  
  ) where

import Libraries.Tuple

import System.Random
import Data.Tuple
import Data.List

-- --------------------------------------------------------------------
-- | The 'Interval' class contains types for which an interval of
-- values can be specified by giving a lower bound and an upper
-- bound. Intervals are specified as @'interval' min max@, for
-- example: 
-- 
-- > interval (0,0) (1,2) = [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)].

class Interval a where
  -- | Takes a range (/min/,/max/) and returns a list of all values with
  -- lower bound /min/ and upper bound /max/.
  interval :: a -> a -> [a]

instance Interval Int where
  interval x y = [x..y]
  
instance Interval Integer where
  interval x y = [x..y]

instance Interval Double where
  interval x y = [x..y]
  
instance Interval Bool where
  interval x y = [x..y]

instance Interval () where
  interval () () = [()]
  
instance (Interval a, Interval b) => Interval (a,b) where
  interval (x0,y0) (x1,y1) = [ (x,y) | x <- interval x0 x1, y <- interval y0 y1 ]

instance (Interval a, Interval b, Interval c) => Interval (a,b,c) where
  interval x y = map tuple (interval (untuple x) (untuple y))
  
instance (Interval a, Interval b, Interval c, Interval d) => Interval (a,b,c,d) where
  interval x y = map tuple (interval (untuple x) (untuple y))
  
instance (Interval a, Interval b, Interval c, Interval d, Interval e) => Interval (a,b,c,d,e) where
  interval x y = map tuple (interval (untuple x) (untuple y))
  
instance (Interval a, Interval b, Interval c, Interval d, Interval e, Interval f) => Interval (a,b,c,d,e,f) where
  interval x y = map tuple (interval (untuple x) (untuple y))
  
instance (Interval a, Interval b, Interval c, Interval d, Interval e, Interval f, Interval g) => Interval (a,b,c,d,e,f,g) where
  interval x y = map tuple (interval (untuple x) (untuple y))
  
instance Interval a => Interval [a] where
  interval x y = l where
    xy = safe_zip x y "interval: upper and lower bound contain lists of non-matching lengths"
    l = aux xy
    aux [] = [[]]
    aux ((x,y):t) = [ h:t' | h <- interval x y, t' <- aux t ]

-- --------------------------------------------------------------------
-- | Types in the 'Zero' class have an \"origin\", i.e., an element
-- that can conveniently serve as the starting point for intervals.

class Zero a where
  -- | Inputs any element of the type and outputs the corresponding
  -- \"zero\" element, for example:
  -- 
  -- > zero ([1,2],3,True) = ([0,0],0,False)
  zero :: a -> a
  
instance Zero Int where
  zero _ = 0
  
instance Zero Integer where
  zero _ = 0

instance Zero Double where
  zero _ = 0

instance Zero Bool where
  zero _ = False

instance Zero () where
  zero () = ()

instance (Zero a, Zero b) => Zero (a,b) where
  zero (a,b) = (zero a, zero b)
  
instance (Zero a, Zero b, Zero c) => Zero (a,b,c) where
  zero x = tuple (zero (untuple x))
  
instance (Zero a, Zero b, Zero c, Zero d) => Zero (a,b,c,d) where
  zero x = tuple (zero (untuple x))
  
instance (Zero a, Zero b, Zero c, Zero d, Zero e) => Zero (a,b,c,d,e) where
  zero x = tuple (zero (untuple x))
  
instance (Zero a, Zero b, Zero c, Zero d, Zero e, Zero f) => Zero (a,b,c,d,e,f) where
  zero x = tuple (zero (untuple x))
  
instance (Zero a, Zero b, Zero c, Zero d, Zero e, Zero f, Zero g) => Zero (a,b,c,d,e,f,g) where
  zero x = tuple (zero (untuple x))
  
instance Zero a => Zero [a] where
  zero l = map zero l
  
-- --------------------------------------------------------------------
-- $Random 
-- We extend the class 'System.Random' with tuples and lists.

-- | 0-tuples
instance Random () where
  randomR ((),()) g = ((), g)
  random g = ((), g)

-- | Pairs
instance (Random a, Random b) => Random (a,b) where
  randomR ((a0,b0),(a1,b1)) g = ((a,b), g'') where
    (a,g') = randomR (a0,a1) g
    (b,g'') = randomR (b0,b1) g'
  random g = ((a,b), g'') where
    (a,g') = random g
    (b,g'') = random g'

-- | Triples
instance (Random a, Random b, Random c) => Random (a,b,c) where
  randomR (a,b) g = (t, g') where
    a1 = untuple a
    b1 = untuple b
    (t1,g') = randomR (a1,b1) g
    t = tuple t1
  random g = (t, g') where
    (t1,g') = random g
    t = tuple t1

-- | 4-Tuples
instance (Random a, Random b, Random c, Random d) => Random (a,b,c,d) where
  randomR (a,b) g = (t, g') where
    a1 = untuple a
    b1 = untuple b
    (t1,g') = randomR (a1,b1) g
    t = tuple t1
  random g = (t, g') where
    (t1,g') = random g
    t = tuple t1

-- | 5-Tuples
instance (Random a, Random b, Random c, Random d, Random e) => Random (a,b,c,d,e) where
  randomR (a,b) g = (t, g') where
    a1 = untuple a
    b1 = untuple b
    (t1,g') = randomR (a1,b1) g
    t = tuple t1
  random g = (t, g') where
    (t1,g') = random g
    t = tuple t1

-- | 6-Tuples
instance (Random a, Random b, Random c, Random d, Random e, Random f) => Random (a,b,c,d,e,f) where
  randomR (a,b) g = (t, g') where
    a1 = untuple a
    b1 = untuple b
    (t1,g') = randomR (a1,b1) g
    t = tuple t1
  random g = (t, g') where
    (t1,g') = random g
    t = tuple t1

-- | 7-Tuples
instance (Random a, Random b, Random c, Random d, Random e, Random f, Random g) => Random (a,b,c,d,e,f,g) where
  randomR (a,b) g = (t, g') where
    a1 = untuple a
    b1 = untuple b
    (t1,g') = randomR (a1,b1) g
    t = tuple t1
  random g = (t, g') where
    (t1,g') = random g
    t = tuple t1

-- | Lists
instance Random a => Random [a] where
  randomR (a,b) g = (l, g') where
    ab = safe_zip a b "randomR: upper and lower bound contain lists of non-matching lengths"
    (g', l) = mapAccumL (\g r -> swap $ randomR r g) g ab
  random g = ([a], g') where
    (a, g') = random g

-- --------------------------------------------------------------------
-- Functions:

-- | @'sample_all' min max@: 
-- returns a list of all elements from the range (/min/,/max/). This
-- is actually just a synonym of 'interval'.
sample_all :: Interval a => a -> a -> [a]
sample_all = interval

-- | @'sample_step' n k min max@: 
-- returns every /n/th element from the range (/min/,/max/), starting
-- with the /k/th element.
sample_step :: (Integral a, Integral b, Interval c) => a -> b -> c -> c -> [c]
sample_step n k x y = list_step n k (interval x y)

-- | @'sample_random' g min max@: 
-- returns an infinite list of random samples from the range
-- (/min/,/max/), using the random number generator /g/.
sample_random :: (Random a, RandomGen g) => g -> a -> a -> [a]
sample_random g x y = randomRs (x,y) g

-- | A variant of 'sample_all' that omits the /min/ argument, and uses
-- the 'zero' element of the type instead.
sample_all0 :: (Zero a, Interval a) => a -> [a]
sample_all0 a = sample_all (zero a) a

-- | A variant of 'sample_step' that omits the /min/ argument, and uses
-- the 'zero' element of the type instead.
sample_step0 :: (Integral a, Integral b, Zero c, Interval c) => a -> b -> c -> [c]
sample_step0 n k a = sample_step n k (zero a) a

-- | A variant of 'sample_random' that omits the /min/ argument, and uses
-- the 'zero' element of the type instead.
sample_random0 :: (Random a, Zero a, RandomGen g) => g -> a -> [a]
sample_random0 g a = sample_random g (zero a) a

-- --------------------------------------------------------------------
-- Local functions:

-- | samples every /n/th element from the list, starting with element /k/
list_step :: (Integral a, Integral b) => a -> b -> [c] -> [c]
list_step n k [] = []
list_step n k (h:t) =
  if k==0 then 
    h:(list_step n (n-1) t) 
  else
    list_step n (k-1) t
    
-- | same as 'zip', but throw an error if length don't match
safe_zip :: [a] -> [b] -> String -> [(a,b)]
safe_zip l1 l2 msg = 
  if length l1 == length l2 
  then zip l1 l2
  else error msg
