-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | Alternative implementations for the binary welded tree algorithm.
-- The purpose of these is to experiment with and potentially
-- illustrate a more functional programming style.

module Algorithms.BWT.Alternative where

import Quipper

import QuipperLib.Qureg
import QuipperLib.Simulation

import Algorithms.BWT.Definitions

-- import other Quipper stuff
import qualified Algorithms.BWT.BWT as BWT

import Libraries.Sampling
import Libraries.Auxiliary

-- import other stuff
import Control.Monad
import Text.Printf
import Data.Bits (xor)
import Text.Printf

import Data.Map (Map)
import qualified Data.Map as Map


-- ======================================================================
-- * Oracle abstraction

-- | This is a version of 'BWT.Oracle' that uses 'Qulist' instead of
--   'Qureg'.  An oracle provides the following information: the tree
--   depth /n/, the label length /m/, the number of edge colors /k/,
--   the entrance label /ENTRANCE/, and for each color 0 ≤ /c/ < /k/,
--   a reversible circuit /ORACLE[sub c](a,b,r)/.

data Oracle = Oracle {
    n :: Int,
    m :: Int,
    k :: Int,
    entrance :: Boollist,
    oraclefun :: Int -> (Qulist, Qulist, Qubit) -> Circ ()
}

-- | Convert a "Alternative".'Oracle' into a "BWT".'BWT.Oracle'.
convert_oracle :: Oracle -> BWT.Oracle
convert_oracle Oracle { n=n, m=m, k=k, entrance=e, oraclefun=f1 } =
  BWT.Oracle { BWT.n=n, BWT.m=m, BWT.k=k, BWT.entrance=e, BWT.oraclefun=f2 } 
    where 
      f2 c (a, b, r) = f1 c (qulist_of_qureg_te a, qulist_of_qureg_te b, r)

-- ======================================================================
-- * Top-level algorithm

-- | Do a quantum random walk on the binary welded tree given by the
-- oracle, for /s/ times steps of length /dt/.  Return a bit list
-- corresponding to the probable exit label.  This is a more
-- functional implementation of 'BWT.qrwbwt' from the module "BWT".
-- 
-- Note: This implementation does not rely on the oracle being
-- self-inverse, and therefore only requires that
-- 
-- > ORACLE[sub c](a, 0, 0) = (a, v[sub c](a), f[sub c](a)), 
-- 
-- rather than the more general property 
-- 
-- > ORACLE[sub c](a, b, r) = (a, b ⊕ v[sub c](a), r ⊕ f[sub c](a)).  
-- 
-- This gives us the freedom to build more efficient oracles, where
-- appropriate.
qrwbwt :: Oracle -> Timestep -> Int -> Circ Bitlist
qrwbwt oracle dt s = do
  comment (printf "ENTER: qrwbwt (dt=%.3e, s=%d)" dt s)
  -- Initialize a to the entrance label.
  a <- qinit (entrance oracle)

  -- Run the Hamiltonian /s/ times for time step /dt/.
  replicateM s $ hamiltonian dt oracle a

  -- Measure /a/.
  exit <- measure a
  comment_with_label "EXIT: qrwbwt" exit "exit"
  return exit

-- | Apply one round of the Hamiltonian for time step /dt/ to /a/.
hamiltonian :: Timestep -> Oracle -> Qulist -> Circ ()
hamiltonian dt oracle a = do
  comment_with_label "ENTER: hamiltonian" a "a"
  for 0 ((k oracle)-1) 1 $ \c -> do
    -- for c from 0 to k-1

    -- create ancillas b and r
    with_ancilla_list (length a) $ \b -> do
      with_ancilla $ \r -> do

        -- perform computations
        (oraclefun oracle) c (a,b,r)
        time_step dt (a,b,r)
        reverse_generic_imp ((oraclefun oracle) c) (a,b,r)
        -- "reverse" here is not quite GFI
  comment_with_label "EXIT: hamiltonian" a "a"

-- | Apply the diffusion step to /(a,b,r)/. Here /a/ and /b/ must be
-- of equal length.
time_step :: Timestep -> (Qulist, Qulist, Qubit) -> Circ ()
time_step dt (a,b,r) = do
  comment_with_label "ENTER: time_step" (a,b,r) ("a","b","r")
  with_ancilla $ \h -> do
    basischange (a,b,h)
    controlledExpGate (dt,r,h)
    (reverse_generic_imp basischange) (a,b,h)
  comment_with_label "EXIT: time_step" (a,b,r) ("a","b","r")

-- | Apply the basis change from Figure 3 of \[Childs et al.\] to /a/,
-- /b/, and /h/. Here /a/ and /b/ must be of equal length.
basischange :: (Qulist, Qulist, Qubit) -> Circ ()
basischange (a,b,h) = do
  comment_with_label "ENTER: basischange" (a,b,h) ("a","b","h")
  -- apply W gates
  zipWithM_ gate_W a b
  -- apply doubly-controlled not-gates
  zipWithM_ (dc_not h) a b
  comment_with_label "EXIT: basischange" (a,b,h) ("a","b","h")
    where
      dc_not h x y = qnot_at h `controlled` (x .==. 1 .&&. y .==. 0)
  
-- | Compute the required number of iterations as a function of ε and
-- /dt/.
-- 
-- Inputs: /n/ is the tree depth, ε is the desired precision, /dt/ is
-- the simulation time step. Intermediate values: /t/ is the
-- simulation time. Output: /s/, the upper bound on the number of
-- simulation time steps.
-- 
-- Note: \[Childs et al\] specifies that /t/ should be chosen
-- uniformly at random within the interval 0 < /t/ ≤ /n/[sup 4]\/2ε.
-- Here, for simplicity, we just use /t/ = ⌊/n/[sup 4]\/2ε⌋. Also note
-- that this function is for information only, as it is not actually
-- used. Users should specify /s/ directly.
compute_steps :: Int -> Double -> Double -> Int
compute_steps n epsilon dt =
  floor (t / dt)
  where
    t = fromIntegral (n * n * n * n) / (2.0 * epsilon)

-- ======================================================================
-- * Oracle implementations

-- ** Blackbox oracle

-- | A blackbox oracle for testing. This just produces a labelled box
-- in place of the actual oracle circuit. The argument is the tree
-- height.
oracle_blackbox :: Int -> Oracle
oracle_blackbox n = 
  let m = n+2 in
  Oracle {
    n = n,
    m = m,
    k = 4,
    entrance = boollist_of_int_bh (n+2) 1,
    oraclefun = \c (a, b, r) ->
    do
      named_gate_at ("O(" ++ show c ++ ")") (a ++ b ++ [r])
      return ()
  }

-- ----------------------------------------------------------------------
-- ** A simple \"exponential\" oracle.

-- | This oracle, which works only for the fixed tree height 3, works
-- by explicitly listing all the edges. It serves only to illustrate
-- how the edge information is encoded. Listing all edges explicitly
-- obviously would not scale well to larger graphs.
oracle_simple :: Oracle
oracle_simple =
  let n = 3
      m = 5
      k = 4

      invalid = 0    -- also works correctly for invalid = 31
      invalid_vec = boollist_of_int_bh m invalid

      green = 0
      blue = 1
      red = 2
      black = 3

      edges :: Int -> [(Int, Int)]
      edges 0 = [(1,3), (2,5), (4,8), (6,12), (7,15), (9,17), (10,18),
                 (13,21), (19,25), (22,27), (24,28), (26,29)]
      edges 1 = [(2,4), (3,6), (5,10), (7,14), (8,16), (11,19), (12,20),
                 (17,24), (21,26), (23,27), (25,28), (29,30)]
      edges 2 = [(1,2), (3,7), (4,9), (5,11), (6,13), (14,22), (15,23),
                 (16,24), (18,25), (20,26), (27,29), (28,30)]
      edges 3 = [(8,17), (9,18), (10,19), (11,20), (12,21), (13,22),
                 (14,23), (15,16)]
      edges n = error ("oracle_simple: illegal color: " ++ show n)

      -- apply an (a,n1)-controlled not operation to (v,n2)
      multi_controlled_multi_not :: Int -> (Qulist, Qulist) -> (Int, Int) -> Circ ()
      multi_controlled_multi_not m (a,v) (n1, n2) = do
        let vec1 = boollist_of_int_bh m n1
        let vec2 = boollist_of_int_bh m n2
        bool_controlled_not v vec2 `controlled` a .==. vec1
        return ()

      -- the O_c circuit
      oracle_O :: Int -> (Qulist, Qulist) -> Circ ()
      oracle_O c (a,v) = do
        let e = edges c
        foreach e $ \(n1, n2) -> do
	  multi_controlled_multi_not m (a,v) (n1, invalid `xor` n2)
	  multi_controlled_multi_not m (a,v) (n2, invalid `xor` n1)

      -- the B_c circuit
      oracle_B :: (Qulist, Qulist) -> Circ ()
      oracle_B (v,b) =
        for 0 (m-1) 1 $ \i -> do
          qnot_at (b !! i) `controlled` (v !! i) .==. 1

      -- the R_c circuit
      oracle_R :: (Qulist, Qubit) -> Circ ()
      oracle_R (v,r) = do
        qnot_at r `controlled` v .==. invalid_vec

      -- the oracle circuit
      oraclefun :: Int -> (Qulist, Qulist, Qubit) -> Circ ()
      oraclefun c (a,b,r) = do
        comment_with_label "ENTER: oracle_simple" (a,b,r) ("a","b","r")
        with_ancilla_init invalid_vec $ \v -> do
          oracle_O c (a,v)
          oracle_B (v,b)
          oracle_R (v,r)
          oracle_O c (a,v)
        comment_with_label "EXIT: oracle_simple" (a,b,r) ("a","b","r")

  in

   -- return the oracle object
   Oracle { n = n,
            m = m,
            k = k,
            entrance = boollist_of_int_bh m 1,
            oraclefun = oraclefun
          }

-- ======================================================================
-- ** Alternate implementations of the \"orthodox\" oracle

-- ----------------------------------------------------------------------
-- *** Classical implementation

-- $ In this section, we first implement the oracle function 
-- /v[sub c](a)/ as a classical boolean function. This implementation
-- is just for reference, and attempts to be neither efficient nor
-- quantum. It can, however, be used as a specification to test the 
-- actual quantum oracles against. 
-- 
-- Both the classical circuit implementation (below) and the Template
-- Haskell implementation (in the module "BWT.Template") were derived
-- from this.
-- 
-- We start with several auxiliary functions.

-- | The type of nodes: a pair of a tree bit and a node address.
type Node = (Bool, [Bool])

-- | Convert integers to nodes, mainly for testing.
node_of_int :: Int -> Int -> Node
node_of_int m a = node_of_boollist (boollist_of_int_bh m a)

-- | Convert nodes to integers, mainly for testing.
int_of_node :: Node -> Int
int_of_node n = int_of_boollist_unsigned_bh (boollist_of_node n)

-- | Convert a bit vector to a node.
node_of_boollist :: [Bool] -> Node
node_of_boollist (t:a) = (t,a)
node_of_boollist [] = error "node_of_boollist: empty boollist"

-- | Convert a node to a bit vector.
boollist_of_node :: Node -> [Bool]
boollist_of_node (t,a) = t:a

-- | Input a node /a/ and return the parent of /a/. We assume that /a/
-- is not a root or invalid.
parent :: Node -> Node
parent (t, aa) = (t, False : init aa)

-- | Input a node /a/ and return the left or right child of /a/
-- (depending on whether the /childbit/ is 'False' or 'True',
-- respectively). Assumes that /a/ is not a leaf.
childintree :: Node -> Bool -> Node
childintree (t, h:aa) childbit = (t, aa ++ [childbit])
childintree _ _ = error "childintree: invalid node"

-- | @'bit_adder' 'False'@ is a one-bit adder, and @'bit_adder' 'True'@ is
-- a one-bit subtracter (i.e., add the 2's complement of /y/).
bit_adder :: Bool -> (Bool, Bool, Bool) -> (Bool, Bool)
bit_adder sign (carry, x, y) = (carry', z)
  where
    y' = y `bool_xor` sign
    z = carry `bool_xor` x `bool_xor` y'
    carry' = majority carry x y'
    majority a b c = if a==b then a else c

-- | Input an /n/+1-bit leaf node /a/:/aa/ (without the tree bit; /a/
-- is the highest bit and /aa/ is the remaining /n/ bits) and a sign
-- /s/ (where 'True' = negative, 'False' = positive).  Return
-- /a/:(/aa/ + /s/ * /f/). The first input is the /n/-bit welding
-- vector /f/ (a parameter to the oracle). Note that /f/ is a
-- parameter and /s/, /aa/ are inputs.
doweld1 :: Boollist -> Bool -> [Bool] -> [Bool]
doweld1 f s (a:aa) = a : aa' where
  aa' = snd $ fold_right_zip (bit_adder s) (s, aa, f)
doweld1 f s [] = error "doweld1: invalid node"

-- | Input an /n/+1-bit leaf node /a/:/aa/ (without the tree bit), and
-- return /a/:(/aa/ ⊕ /g/). The first input is the /n/-bit welding
-- vector /g/ (a parameter to the oracle).
doweld0 :: Boollist -> [Bool] -> [Bool]
doweld0 g (a:aa) = a : aa' where
  aa' = g `boollist_xor` aa
doweld0 g [] = error "doweld0: invalid node"

-- | Input a leaf node /a/ and return the left or right weld of /a/ in
-- the other tree (depending on whether the /weldbit/ is 'False' or
-- 'True').  Assumes that /a/ is a leaf.
weld :: Boollist -> Boollist -> Node -> Bool -> Node
weld f g (t, aa) weldbit = (not t, bb)
  where
    bb = if weldbit
         then doweld1 g t aa
         else doweld0 f aa

-- | Input a node /a/ and return the left or right child of /a/
-- (depending on whether the /childbit/ is 'False' or 'True'. This
-- works for leaf and non-leaf nodes.
child :: Boollist -> Boollist -> Node -> Bool -> Node
child f g (t, aa) childbit =
  case aa of
    True : _ ->  -- This is a leaf
      weld f g (t, aa) childbit
    False : _ -> -- This is not a leaf
      childintree (t, aa) childbit
    _ -> error "child: invalid node"

-- | Input a node address (without the tree bit) and return the parity
-- of the node level expressed as a boolean either 'False' or
-- 'True'. Leaves have parity 'False', and other levels have
-- alternating parities. In other words: count the number of leading
-- zeros modulo 2.
level_parity :: [Bool] -> Bool
level_parity [] = False
level_parity (h:t) = if h then False else not (level_parity t)

-- | Input a node address (without the tree bit) and return 'True' iff
-- the node address is invalid. In other words, return 'True' iff the
-- list consists of all 0's.
is_zero :: [Bool] -> Bool
is_zero [] = True
is_zero (h:t) = if h then False else is_zero t

-- | Input a node address (without the tree bit) and return 'True' iff
-- the node is a root or invalid. In other words, check whether all
-- digits but the last are 0's.
is_root :: [Bool] -> Bool
is_root [] = True
is_root (h:[]) = True
is_root (h:t) = if h then False else is_root t

-- | @'v_function' f g c a@: returns /v/[sub /c/](/a/), the label of the
-- node connected to /a/ by an edge of color /c/, or 'Nothing' if
-- there is no such node. The parameters /f/ and /g/ encode the
-- welding functions, and are lists of length /n/. /c/ is a color in
-- the range 0..3, and /a/ is an (/n/+2)-bit node label.
v_function :: Boollist -> Boollist -> Int -> Node -> Maybe Node
v_function f g c a =
  let (t,aa) = a
      bc_hi = level_parity aa
      z = is_zero aa
      e = is_root aa
      a1 = if last aa then True else False
      [c_hi, c_lo] = boollist_of_int_bh 2 c
      [cbc_hi, cbc_lo] = [c_hi `bool_xor` bc_hi, c_lo]
  in
   if not e && [cbc_hi, cbc_lo] == [True, a1] then Just(parent a) else
   if not z && cbc_hi == False then Just(child f g a cbc_lo) else
   Nothing

-- ----------------------------------------------------------------------
-- *** Auxiliary functions

-- | The type of nodes: a pair of a tree bit and a node address.
type CNode = (Bit, Bitlist)

-- | Like 'CNode', but uses qubits instead of classical bits.
type QNode = (Qubit, [Qubit])

-- | Convert a 'Qulist' to a 'QNode'.
qnode_of_qulist :: Qulist -> QNode
qnode_of_qulist (t:a) = (t,a)
qnode_of_qulist [] = error "qnode_of_qulist: empty list"

-- | Convert a 'Bitlist' to a 'CNode'.
cnode_of_bitlist :: Bitlist -> CNode
cnode_of_bitlist (t:a) = (t,a)
cnode_of_bitlist [] = error "cnode_of_bitlist: empty list"

-- | Exclusive or operation on bit vectors.
cboollist_xor :: Bitlist -> Bitlist -> Circ Bitlist
cboollist_xor = zipWithM (\x y -> cgate_xor [x,y])

-- ----------------------------------------------------------------------
-- *** Classical circuit implementation

-- $ We now implement the oracle function v[sub c](a) as a classical
-- circuit, with /c/ as a parameter. We don't try to be clever or
-- efficient yet.  The implementation follows the \"classical
-- implementation\" above, but must be reformulated due to the need to
-- work within the 'Circ' monad.

-- | Input a node /a/ and return the parent of /a/. We assume that /a/
-- is not a root or invalid.
cparent :: CNode -> Circ CNode
cparent (t, aa_in) = do
  comment_with_label "ENTER: cparent" (t, aa_in) ("t", "aa_in")
  false <- cinit False
  let aa_out = false : init aa_in
  comment_with_label "EXIT: cparent" (t, aa_out) ("t", "aa_out")
  return (t, aa_out)

-- | Input a node /a/ and return the left or right child of /a/
-- (depending on whether the /childbit/ is 'False' or 'True',
-- respectively). Assumes that /a/ is not a leaf.
cchildintree :: CNode -> Bit -> Circ CNode
cchildintree (t, node_in@(h:aa)) childbit = do
  comment_with_label "ENTER: cchildintree" (t, node_in) ("t", "node_in")
  let node_out = aa ++ [childbit]
  comment_with_label "EXIT: cchildintree" (t, node_out) ("t", "node_out")
  return (t, node_out)
cchildintree _ _ = error "cchildintree: invalid node"

-- | @'bit_adder' 'False'@ is a one-bit adder, and @'bit_adder' 'True'@ is
-- a one-bit subtracter (i.e., add the 2's complement of /y/).
cbit_adder :: Bit -> (Bit, Bit, Bit) -> Circ (Bit, Bit)
cbit_adder sign (carry_in, x, y) = do
    comment_with_label "ENTER: cbit_adder" (sign, carry_in, x, y) ("sign", "carry_in", "x", "y")
    y' <- cgate_xor [y, sign]
    z <- cgate_xor [carry_in, x, y']
    carry_out <- cmajority carry_in x y'
    comment_with_label "EXIT: cbit_adder" (carry_out, z) ("carry_out", "z")
    return (carry_out, z)
  where
    cmajority a b c = do
      cond <- cgate_eq a b
      cgate_if cond a c

-- | Input an /n/+1-bit leaf node /a/:/aa/ (without the tree bit; /a/
-- is the highest bit and /aa/ is the remaining /n/ bits) and a sign
-- /s/ (where 'True' = negative, 'False' = positive).  Return
-- /a/:(/aa/ + /s/ * /f/). The first input is the /n/-bit welding
-- vector /f/ (a parameter to the oracle). Note that /f/ is a
-- parameter and /s/, /aa/ are inputs.
cdoweld1 :: Boollist -> Bit -> Bitlist -> Circ Bitlist
cdoweld1 f s node_in@(a:aa) = do
  comment_with_label "ENTER: cdoweld1" (s, node_in) ("s", "node_in")
  f' <- cinit f
  (_,aa') <- fold_right_zipM (cbit_adder s) (s, aa, f')
  let node_out = a : aa'
  comment_with_label "EXIT: cdoweld1" node_out "node_out"
  return node_out
cdoweld1 f s [] = error "cdoweld1: invalid node"

-- | Input an /n/+1-bit leaf node /a/:/aa/ (without the tree bit), and
-- return /a/:(/aa/ ⊕ /g/). The first input is the /n/-bit welding
-- vector /g/ (a parameter to the oracle).
cdoweld0 :: Boollist -> Bitlist -> Circ Bitlist
cdoweld0 g node_in@(a:aa) = do
  comment_with_label "ENTER: cdoweld0" node_in "node_in"
  g' <- cinit g
  aa' <- g' `cboollist_xor` aa
  let node_out = a:aa'
  comment_with_label "EXIT: cdoweld0" node_out "node_out"
  return node_out
cdoweld0 g [] = error "cdoweld0: invalid node"

-- | Input a leaf node /a/ and return the left or right weld of /a/ in
-- the other tree (depending on whether the /weldbit/ is 'False' or
-- 'True').  Assumes that /a/ is a leaf.
cweld :: Boollist -> Boollist -> CNode -> Bit -> Circ CNode
cweld f g node_in@(t, aa) weldbit = do
  comment_with_label "ENTER: cweld" (node_in, weldbit) ("node_in", "weldbit")
  bb <- circ_if weldbit (
    cdoweld1 g t aa
    )(
    cdoweld0 f aa
    )
  t' <- cgate_not t
  let node_out = (t', bb)
  comment_with_label "EXIT: cweld" node_out "node_out"
  return node_out

-- | Input a node /a/ and return the left or right child of /a/
-- (depending on whether the /childbit/ is 'False' or 'True'. This
-- works for leaf and non-leaf nodes.
cchild :: Boollist -> Boollist -> CNode -> Bit -> Circ CNode
cchild f g node_in@(t, a:aa) childbit = do
  comment_with_label "ENTER: cchild" (node_in, childbit) ("node_in", "childbit")
  node_out <- circ_if a (
    -- This is a leaf
    cweld f g (t, a:aa) childbit
    )(            
    -- This is not a leaf
    cchildintree (t, a:aa) childbit
    )
  comment_with_label "EXIT: cchild" node_out "node_out"
  return node_out

cchild f g (t, _) childbit = 
  error "cchild: invalid node"

-- | Input a node address (without the tree bit) and return the parity
-- of the node level expressed as a boolean either 'False' or
-- 'True'. Leaves have parity 'False', and other levels have
-- alternating parities. In other words: count the number of leading
-- zeros modulo 2.
clevel_parity :: Bitlist -> Circ Bit
clevel_parity node = do
  comment_with_label "ENTER: clevel_parity" node "node"
  parity <- clevel_parity_rec node
  comment_with_label "EXIT: clevel_parity" parity "parity"
  return parity

  where
    clevel_parity_rec :: Bitlist -> Circ Bit
    clevel_parity_rec [] = cinit False
    clevel_parity_rec (h:t) = do
      r <- clevel_parity_rec t
      circ_if h (
        cinit False
        )(
        cgate_not r
        )

-- | Input a node address (without the tree bit) and return 'True' iff
-- the node address is invalid. In other words, return 'True' iff the
-- list consists of all 0's.
cis_zero :: Bitlist -> Circ Bit
cis_zero node = do
  comment_with_label "ENTER: cis_zero" node "node"
  is_zero <- cis_zero_rec node
  comment_with_label "EXIT: cis_zero" is_zero "is_zero"
  return is_zero
  
  where
    cis_zero_rec :: Bitlist -> Circ Bit
    cis_zero_rec [] = cinit True
    cis_zero_rec (h:t) = do
      circ_if h (
        cinit False
        )(
        cis_zero_rec t
        )

-- | Input a node address (without the tree bit) and return 'True' iff
-- the node is a root or invalid. In other words, check whether all
-- digits but the last are 0's.
cis_root :: Bitlist -> Circ Bit
cis_root node = do
  comment_with_label "ENTER: cis_root" node "node"
  is_root <- cis_root_rec node
  comment_with_label "EXIT: cis_root" is_root "is_root"
  return is_root

  where
    cis_root_rec :: Bitlist -> Circ Bit
    cis_root_rec [] = cinit True
    cis_root_rec (h:[]) = cinit True
    cis_root_rec (h:t) = do
      circ_if h (
        cinit False
        )(
        cis_root_rec t
        )

-- | @'cv_function' f g c a@: returns /v/[sub /c/](/a/), the label of the
-- node connected to /a/ by an edge of color /c/, or 'Nothing' if
-- there is no such node. The parameters /f/ and /g/ encode the
-- welding functions, and are lists of length /n/. /c/ is a color in
-- the range 0..3, and /a/ is an (/n/+2)-bit node label.
-- 
-- We currently implement @'Maybe' 'CNode'@ as an indexed union, and
-- specifically as @('CNode','Bit')@. When /Bit/='True', the value of
-- 'CNode' is undefined (doesn't matter); in particular, this value
-- may contain garbage.
cv_function :: Boollist -> Boollist -> Int -> CNode -> Circ (CNode,Bit)
cv_function f g color a = do
  comment_with_label (printf "ENTER: cv_function (color=%d)" color) a "a"
  let (t,aa) = a
  bc_hi <- clevel_parity aa
  z <- cis_zero aa
  e <- cis_root aa
  let a1 = last aa
  let [c_hi', c_lo'] = boollist_of_int_bh 2 color
  c_hi <- cinit c_hi'
  c_lo <- cinit c_lo'
  cbc_hi <- cgate_xor [c_hi, bc_hi]
  let cbc_lo = c_lo
  not_e <- cgate_not e
  cbc_lo_eq_a1 <- cgate_eq cbc_lo a1
  cond1 <- cgate_and [not_e, cbc_hi, cbc_lo_eq_a1]
  (b, invalid) <- circ_if cond1 (
    do 
      cparent_a <- cparent a
      false <- cinit False
      return (cparent_a, false)
    )(
    do
      cchild_a_cbc_lo <- cchild f g a cbc_lo
      not_z <- cgate_not z
      cbc_hi_eq_false <- cgate_not cbc_hi
      valid <- cgate_and [not_z, cbc_hi_eq_false]
      not_valid <- cgate_not valid
      -- a slight optimization here: we return garbage in the
      -- first register if not_valid == True
      return (cchild_a_cbc_lo, not_valid)
    )
  comment_with_label (printf "EXIT: cv_function (color=%d)" color) (b, invalid) ("b", "invalid")
  return (b, invalid)

-- ======================================================================
-- *** Oracle abstraction

-- | The classical oracle implementation, packaged into the 'Oracle'
-- abstraction. This oracle has two parameters, namely the welding
-- vectors /f/ and /g/. Note: this oracle has not been optimized
-- whatsoever.
oracle_classical :: Boollist -> Boollist -> Oracle
oracle_classical f g =
  Oracle { n = n,
           m = m,
           k = k,
           entrance = entrance,
           oraclefun = oraclefun
         } where
    n = length f
    m = n+2
    k = 4
    entrance = boollist_of_int_bh m 1
      
    oraclefun :: Int -> (Qulist, Qulist, Qubit) -> Circ ()
    oraclefun color (a,b,r) = do
      let an = qnode_of_qulist a
      let bn = qnode_of_qulist b
      (classical_to_quantum . classical_to_reversible) (cv_function f g color) (an, (bn, r))
      return ()
      
-- ======================================================================
-- * Testing functions

-- | Output the list of colored edges as computed by the classical
-- 'v_function', for some arbitrary choice of /f/ and /g/ and /n/=3.
main_edges1 :: IO()
main_edges1 = mapM_ output (sample_all0 (127,3))
  where
    f = take 5 (True : False : f)    
    g = take 5 (False : True : g)
    
    output :: (Int,Int) -> IO()
    output (a,c) =
      case v_function f g c (node_of_int 7 a) of
        Nothing -> printf "%d ---%d---> None\n" a c
        Just b -> printf "%d ---%d---> %d\n" a c (int_of_node b)

-- | For debugging: 'circfun' is similar to 'v_function', except it
-- works by calling 'cv_function' to assemble the circuit, then
-- simulates it. This is for testing whether the assembled circuit is
-- correct. Returns @('Bool', 'Node')@ instead of @'Maybe' 'Node'@, so
-- that we can see any garbage that is output in case of an invalid
-- node.
circfun :: Boollist -> Boollist -> Int -> Node -> (Node, Bool)
circfun f g color nd = 
  run_classical_generic (cv_function f g color) nd

-- | Output the list of colored edges as computed by simulating the
-- circuit 'cv_function', for some arbitrary choice of /f/ and /g/ and
-- /n/=3. This is like 'main_edges1', except it actually assembles and
-- simulates the classical circuit.
main_edges2 :: IO()
main_edges2 = mapM_ output (sample_all0 (127,3))
  where
    f = take 5 (True : False : f)    
    g = take 5 (False : True : g)
    output :: (Int,Int) -> IO()
    output (a,c) =
      case circfun f g c (node_of_int 7 a) of
        (node, False) -> printf "%d ---%d---> %d\n" a c (int_of_node node)
        (garbage, True) -> printf "%d ---%d---> None (%d)\n" a c (int_of_node garbage)
    
-- | Graphically output the classical oracle circuit for color /c/,
-- using /n/ from the oracle data structure, and for some arbitrary
-- /f/ and /g/.
main_oraclec :: Format -> BWT.Oracle -> Int -> IO()
main_oraclec format oracle color =
  print_generic format circuit cnode_shape
    where
      m' = BWT.m oracle
      n' = BWT.n oracle
      f = take n' (True : False : f)
      g = take n' (False : True : g)
      cnode_shape = cnode_of_bitlist (replicate m' bit)
      circuit n = cv_function f g color n

-- | Like 'main_oraclec', except it rewrites the classical circuit in
-- terms of Toffoli gates.
main_oracle2 :: Format -> BWT.Oracle -> Int -> IO()
main_oracle2 format oracle color =
  print_generic format circuit cnode_shape
    where
      m' = BWT.m oracle
      n' = BWT.n oracle
      f = take n' (True : False : f)
      g = take n' (False : True : g)
      cnode_shape = cnode_of_bitlist (replicate m' bit)
      circuit n = classical_to_cnot (cv_function f g color n)

-- | Like 'main_oraclec', except it makes the classical circuit
-- reversible first.
main_oracle3 :: Format -> BWT.Oracle -> Int -> IO()
main_oracle3 format oracle color =
  print_generic format circuit (cnode_shape, (cnode_shape, qubit))
    where
      m' = BWT.m oracle
      n' = BWT.n oracle
      f = take n' (True : False : f)
      g = take n' (False : True : g)
      cnode_shape = qnode_of_qulist (replicate m' qubit)
      circuit = (classical_to_quantum . classical_to_reversible) (cv_function f g color)

-- | Output the top-level circuit for the binary welded tree algorithm
-- with the classical oracle, using some arbitrary welding vectors /f/
-- and /g/, and /s/=1.
main_qrwbwt :: IO()
main_qrwbwt =
   print_simple EPS (qrwbwt (oracle_classical f g) dt 1)
     where 
       f = [False, False, True]
       g = [True, False, True]
       dt = pi/180
