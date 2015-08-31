-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper
import QuipperLib.Unboxing

main :: IO ()
main = do
  print_generic Preview boxed_unboxed (replicate 5 qubit) (replicate 5 qubit)
  --print_simple Preview boxed_unboxed2
  --print_simple Preview boxed_unboxed3
  --print_simple Preview boxed_unboxed4

sub_notboxed :: [Qubit] -> Circ [Qubit]
sub_notboxed [] = return []
sub_notboxed [a] = return [a]
sub_notboxed (a:(b:cs)) = do
  a' <- hadamard a `controlled` b
  bcs' <- sub_notboxed (b:cs)
  return (bcs' ++ [a'])

sub_boxed :: [Qubit] -> Circ [Qubit]
sub_boxed = box "sub" sub_notboxed

my_circuit :: ([Qubit] -> Circ [Qubit]) -> [Qubit] -> [Qubit] -> Circ ([Qubit],[Qubit])
my_circuit sub as bs = do
  comment_with_label "ENTER: my_circuit" (as,bs) ("a","b")
  as' <- sub (reverse as) `controlled` (head bs)
  label (as',bs) ("a","b")
  bs' <- sub bs 
  label (as',bs') ("a","b")
  as'' <- reverse_generic_endo sub (reverse as') `controlled` (head bs')
  comment_with_label "EXIT: my_circuit" (as'',bs') ("a","b")
  return (as'',bs')

boxed_unboxed :: [Qubit] -> [Qubit] -> Circ ([Qubit],[Qubit])
boxed_unboxed as bs = do
  label (as,bs) ("a","b")
  (as,bs) <- my_circuit sub_notboxed as bs
  label (as,bs) ("a","b")
  (as,bs) <- my_circuit sub_boxed as bs
  label (as,bs) ("a","b")
  (as,bs) <- unbox (my_circuit sub_boxed) as bs
  label (as,bs) ("a","b")
  return (as,bs)

my_subroutine2 :: (Qubit,Qubit,Qubit) -> Circ (Qubit,Qubit,Qubit)
my_subroutine2 (a,b,c) = do
   qnot_at c `controlled` [a,b]
   return (a,b,c)

sub2 :: (Qubit,Qubit,Qubit) -> Circ (Qubit,Qubit,Qubit)
sub2 = box "tof" my_subroutine2

my_subroutine2' :: (Qubit,Qubit,Qubit,Qubit) -> Circ (Qubit,Qubit,Qubit,Qubit)
my_subroutine2' (a,b,c,d) = do
     (b',c',d') <- sub2 (b,c,d) `controlled` a
     return (a,b',c',d')

sub2' :: (Qubit,Qubit,Qubit,Qubit) -> Circ (Qubit,Qubit,Qubit,Qubit)
sub2' = box "ss" my_subroutine2'

my_circuit2 :: (Qubit,Qubit,Qubit,Qubit) -> (Qubit,Qubit,Qubit,Qubit) -> Circ ((Qubit,Qubit,Qubit,Qubit),(Qubit,Qubit,Qubit,Qubit))
my_circuit2 as bs = do
  (a1,a2,a3,a4) <- sub2' as
  (b1,b2,b3,b4) <- sub2' bs 
  return ((a1,a2,a3,a4),(b1,b2,b3,b4))

boxed_unboxed2 :: (Qubit,Qubit,Qubit,Qubit) -> (Qubit,Qubit,Qubit,Qubit) -> Circ ((Qubit,Qubit,Qubit,Qubit),(Qubit,Qubit,Qubit,Qubit))
boxed_unboxed2 as bs = do
  (as',bs') <- my_circuit2 as bs
  (as'',bs'') <- (unbox my_circuit2) as' bs'
  (unbox (unbox my_circuit2)) as'' bs''

my_subroutine3 :: (Qubit,Qubit,Qubit) -> Circ Qubit
my_subroutine3 (a,b,c) = do
  qdiscard (c,a)
  return b

sub3 :: (Qubit,Qubit,Qubit) -> Circ Qubit
sub3 = box "term" my_subroutine3

my_circuit3 :: (Qubit,Qubit,Qubit,Qubit,Qubit,Qubit) -> Circ (Qubit,Qubit)
my_circuit3 (a,b,c,d,e,f) = do
  b' <- sub3 (a,b,c)
  e' <- sub3 (d,e,f)
  qnot_at e' `controlled` b' 
  return (b',e')

boxed_unboxed3 :: ((Qubit,Qubit,Qubit,Qubit,Qubit,Qubit),(Qubit,Qubit,Qubit,Qubit)) -> Circ (Qubit,Qubit)
boxed_unboxed3 ((a,b,c,d,e,f),(c',d',e',f')) = do
  (a',b') <-  my_circuit3 (a,b,c,d,e,f)
  (unbox my_circuit3) (a',b',c',d',e',f')

my_subroutine4 :: Qubit -> Circ (Qubit,Qubit,Qubit)
my_subroutine4 a = do
  (b,c) <- qinit (False,False)
  return (a,b,c)

sub4 :: Qubit -> Circ (Qubit,Qubit,Qubit)
sub4 = box "init" my_subroutine4

my_circuit4 :: (Qubit,Qubit) -> Circ (Qubit,Qubit,Qubit,Qubit,Qubit,Qubit)
my_circuit4 (a,b) = do
  (a',c,d) <- sub4 a 
  (b',e,f) <- sub4 b
  return (a',b',c,d,e,f)

boxed_unboxed4 :: (Qubit,Qubit) -> Circ ((Qubit,Qubit,Qubit,Qubit),(Qubit,Qubit,Qubit,Qubit,Qubit,Qubit))
boxed_unboxed4 (a,b) = do
  (a',b',c,d,e,f) <- my_circuit4 (a,b)
  (a'',b'',g,h,i,j) <- unbox my_circuit4 (a',b')
  return ((c,d,e,f),(a'',b'',g,h,i,j))


