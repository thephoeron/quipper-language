-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides an implementation of the main binary welded
-- tree algorithm and oracle, using a more-or-less imperative
-- programming style. We abstract the oracle into a data type, so that
-- different oracles can be plugged into the main algorithm.

module Algorithms.BWT.BWT where

-- import other Quipper stuff
import Quipper
import Algorithms.BWT.Definitions

import QuipperLib.Qureg
import QuipperLib.Decompose

import Libraries.Auxiliary

import Text.Printf

-- ======================================================================
-- * Oracle abstraction

-- | A data structure to hold an oracle. The binary welded tree
-- algorithm is parametric on an oracle. An oracle encodes a graph,
-- and provides the following information: the tree depth /n/ (in the
-- above example: 3), the label length /m/ (in bits; 5 in the above
-- example), the number of edge colors /k/, the entrance label
-- /ENTRANCE/, and for each color 0 ≤ /c/ < /k/, a reversible circuit
-- /ORACLE/[sub /c/](/a/,/b/,/r/). On basis vectors, this circuit
-- encodes the edge information in the following sense:
-- 
-- > ORACLE[sub c](a, b, r) = (a, b ⊕ v[sub c](a), r ⊕ f[sub c](a)),
-- 
-- where /f/[sub /c/](/a/) is 1 if the node /a/ is connected to an
-- edge of color /c/, and 0 otherwise; and /v/[sub /c/](a) is the
-- node label connected to node /a/ along an edge of color /c/ (if
-- any), and arbitrary otherwise. 
-- 
-- Not all available node labels need to be used (for example, 0 and
-- 16 are unused in the graph in the above illustration).

data Oracle = Oracle {
    n :: Int,
    m :: Int,
    k :: Int,
    entrance :: Boollist,
    oraclefun :: Int -> (Qureg, Qureg, Qubit) -> Circ ()
}

-- ======================================================================
-- * Top-level algorithm

-- | The main loop of the binary welded tree algorithm. 
-- 
-- @qrwbwt oracle s dt@: Do a quantum random walk on the binary welded
-- tree given by the oracle /oracle/, for /s/ times steps of length
-- /dt/. Returns a bit list corresponding to the computed exit node
-- label.

qrwbwt :: Oracle -> Int -> Timestep -> Circ [Bit]
qrwbwt oracle s dt = do
  comment (printf "ENTER: qrwbwt (s=%d, dt=%.3e)" s dt)
  -- initialize a to the entrance label
  a <- qinit_register (entrance oracle)
  with_ancilla_reg (m oracle) $ \b -> do
    with_ancilla $ \r -> do
      loopM_boxed_if (s > 1) "qrwbwt_loop" s (a,b,r) $ \(a,b,r) -> do
        for 0 (k oracle-1) 1 $ \c -> do
          (oraclefun oracle) c (a, b, r)
          timestep (a, b, r, dt, m oracle)
          (oraclefun oracle) c (a, b, r)
        endfor
        return (a,b,r)
      endfor
  exit <- qmeasure_register a
  comment_with_label "EXIT: qrwbwt" exit "exit"
  return exit

-- | @timestep (a, b, r, dt, m)@: Perform a single time step /dt/ of
-- the quantum walk. This is done by iterating through each of the
-- available edge colors, and performing a diffusion step for each
-- color. Here, /a/ is an /m/-qubit registers holding (a superposition
-- of) the current node label. /b/ is an /m/-qubit ancilla register,
-- and /r/ is an ancilla qubit. Both /b/ and /r/ are expected to be
-- initialized to |0〉 by the caller, and will be returned in state
-- |0〉.
timestep :: (Qureg, Qureg, Qubit, Timestep, Int) -> Circ ()
timestep (a, b, r, dt, m) = do
  comment_with_label "ENTER: timestep" (a,b,r) ("a","b","r")
  with_ancilla $ \h -> do
    for 0 (m-1) 1 $ \i -> do
      wGate (a.!(i), b.!(i))
    endfor
    for 0 (m-1) 1 $ \i -> do
      toffoliGate (a.!(i), b.!(i), h)
    endfor
    controlledExpGate (dt, r, h)
    for (m-1) 0 (-1) $ \i -> do
      toffoliGate (a.!(i), b.!(i), h)
    endfor
    for (m-1) 0 (-1) $ \i -> do
      wGateInverse (a.!(i), b.!(i))
    endfor
  comment_with_label "EXIT: timestep" (a,b,r) ("a","b","r")
  return ()

-- ======================================================================
-- * Oracle implementation

-- $ The functions in this section implement a particular oracle for a
-- binary welded tree. The oracle is parametric on:
-- 
-- * the tree depth /n/;
-- 
-- * two \"welding vectors\" /f/ and /g/, specifying how the leaves of
-- the two binary trees are connected to each other. Specifically, /f/
-- and /g/ encode the permutations of leaves given by a ↦ a ⊕ f and 
-- a ↦ a + g, respectively, where \"⊕\" denotes bitwise exclusive or,
-- and \"+\" denotes binary addition.

-- ----------------------------------------------------------------------
-- ** Oracle subroutines

-- | The top-level oracle circuit. The arguments are of the form (/a/,
-- /b/, /r/, /color/, /f/, /g/, /n/), where /a/, /b/ are quantum
-- registers of length /n/+2, /color/ is a boolean register of length
-- 2, and /f/ and /g/ are boolean registers of length /n/.
oracle :: (Qureg, Qureg, Qubit, Boolreg, Boolreg, Boolreg, Int) -> Circ ()
oracle (a, b, r, color, f, g, n) = do
  let c = int_of_boolreg_unsigned_le color :: Int
  comment_with_label (printf "ENTER: oracle (color=%d)" c) (a,b,r) ("a","b","r")
  with_ancilla $ \root -> do
    with_ancilla $ \even -> do
      with_ancilla $ \isparent -> do
        with_ancilla $ \ischild -> do
          with_ancilla $ \direction -> do
            with_ancilla $ \ismatch -> do
              parseNodeRoot (a, root, even, n)
              parseNodeEven (a, even, n)
              testIsParent (a, root, even, isparent, color, n, 1, ismatch)
              testIsChild (even, ischild, direction, color, n)
              setParent (a, b, isparent, n)
              setChild (a, b, ischild, direction, f, g, n)
              with_controls (isparent .==. 0 .&&. ischild .==. 0) $ do {
                qnot_at r
              }
              testIsChild (even, ischild, direction, color, n)
              testIsParent (a, root, even, isparent, color, n, 0, ismatch)
              parseNodeEven (a, even, n)
              parseNodeRoot (a, root, even, n)
  comment_with_label (printf "EXIT: oracle (color=%d)" c) (a,b,r) ("a","b","r")
  return ()

-- | Input a node label /a/ of length at least /n/+1. Negate both
-- /root/ and /even/ if /a/ is a root node.
parseNodeRoot :: (Qureg, Qubit, Qubit, Int) -> Circ ()
parseNodeRoot (a, root, even, n) = do
  comment_with_label "ENTER: parseNodeRoot" (a, root, even) ("a", "root", "even")
  with_ancilla_reg (n+1) $ \scratch -> do
    for n 1 (-1) $ \index -> do 
      with_controls (scratch.!(index) .==. 0 .&&. a.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index - 1))
      }
      with_controls (scratch.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index - 1))
      }
    endfor
    with_controls (scratch.!(0) .==. 0) $ do {
      qnot_at root;
      qnot_at even
    }
    for 1 n 1 $ \index -> do    
      with_controls (scratch.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index - 1))
      }
      with_controls (scratch.!(index) .==. 0 .&&. a.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index-1))
      }
    endfor
  comment_with_label "EXIT: parseNodeRoot" (a, root, even) ("a", "root", "even")
  return ()
      
-- | Input a node label /a/ of length at least /n/+1. Negate /even/
-- if the node /a/ occurs at an even height in the tree.
parseNodeEven :: (Qureg, Qubit, Int) -> Circ ()
parseNodeEven (a, even, n) = do
  comment_with_label "ENTER: parseNodeEven" (a, even) ("a", "even")
  with_ancilla_reg (n+1) $ \scratch -> do
    for n 1 (-1) $ \index -> do
      with_controls (scratch.!(n) .==. 0 .&&. a.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index-1));
        with_controls (Prelude.even index) $ do {
          qnot_at even
        }
      }
      with_controls (scratch.!(index-1) .==. 1) $ do {
        qnot_at (scratch.!(n))
      }
    endfor
    for 1 n 1 $ \index -> do
      with_controls (scratch.!(index-1) .==. 1) $ do {
        qnot_at (scratch.!(n))
      }            
      with_controls (scratch.!(n) .==. 0 .&&. a.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index-1))
      }
    endfor
  comment_with_label "EXIT: parseNodeEven" (a, even) ("a", "even")
  return ()

-- | Input a node label /a/ of length at least 1, and flags /root/
-- and /even/ describing whether /a/ is a root and at an even level,
-- respectively. Negate /isparent/ if /a/ has a parent of color
-- /color/ in the tree. 
-- 
-- The qubit /ismatch/ is an ancilla, and /really/ is either 0 or
-- 1. They are jointly used to control uncomputation, so that the
-- following sequence will compute and then uncompute 'testIsParent':
-- 
-- > ismatch <- qinit 0
-- > testIsParent (a, root, even, isparent, color, n, 1, ismatch)
-- > testIsParent (a, root, even, isparent, color, n, 0, ismatch)
-- > qterm 0 ismatch
testIsParent :: (Qureg, Qubit, Qubit, Qubit, Boolreg, Int, Int, Qubit) -> Circ ()
testIsParent (a, root, even, isparent, color, n, really, ismatch) = do
    let c = int_of_boolreg_unsigned_le color :: Int
    comment_with_label (printf "ENTER: testIsParent (color=%d really=%d)" c really) (a, root, even, isparent, ismatch) ("a", "root", "even", "isparent", "ismatch")
    with_controls (really == 0) $ do {
      with_controls (root .==. 0 .&&. ismatch .==. 1) $ do {
        qnot_at isparent
      }
    }
    if color.!(1) == 1 then
      if color.!(0) == 1 then
        with_controls (even .==. 1 .&&. a.!(0) .==. 1) $ do {
          qnot_at ismatch
        }
      else
        with_controls (even .==. 1 .&&. a.!(0) .==. 0) $ do {
          qnot_at ismatch
        }
    else
      if color.!(0) == 1 then
        with_controls (even .==. 0 .&&. a.!(0) .==. 1) $ do {
          qnot_at isparent
        }
      else
        with_controls (even .==. 0 .&&. a.!(0) .==. 0) $ do {
          qnot_at isparent
        }
    with_controls (root .==. 0 .&&. ismatch .==. 1) $ do {
      qnot_at isparent
    }
    comment_with_label (printf "EXIT: testIsParent (color=%d really=%d)" c really) (a, root, even, isparent, ismatch) ("a", "root", "even", "isparent", "ismatch")
    return ()

-- | Consider a node /a/, and negate /ischild/ if /a/ has a child
-- node of color /color/. Also set /direction/ to indicate whether
-- it is a \"left\" or \"right\" child. Here, /color/ is a boolean
-- register of length 2, representing a color. This function is
-- self-inverse.
testIsChild :: (Qubit, Qubit, Qubit, Boolreg, Int) -> Circ ()
testIsChild (even, ischild, direction, color, n) = do
  comment_with_label "ENTER: testIsChild" (even, ischild, direction) ("even", "ischild", "direction")
  if color.!(1) == 1 then
    with_controls (even .==. 0) $ do {
      qnot_at ischild
    }
  else
    with_controls (even .==. 1) $ do {
      qnot_at ischild
    }
  with_controls (color.!(0) == 1) $ do {
    qnot_at direction
  }
  comment_with_label "EXIT: testIsChild" (even, ischild, direction) ("even", "ischild", "direction")
  return ()

-- | Input a node label /a/ of length at least /n/+2, and a flag
-- /isparent/ that has been initialized accordingly. Also input a
-- register /b/ of length at least /n/+2, initialized to |0〉.  If
-- /isparent/ is set, set /b/ to the node label of the parent of
-- /a/. This is self-inverse.
setParent :: (Qureg, Qureg, Qubit, Int) -> Circ ()
setParent (a, b, isparent, n) = do
  comment_with_label "ENTER: setParent" (a, b, isparent) ("a", "b", "isparent")
  for 0 (n-1) 1 $ \index -> do
    with_controls (isparent .==. 1 .&&. a.!(index+1) .==. 1) $ do {
      qnot_at (b.!(index))
    }
  endfor
  with_controls (isparent .==. 1 .&&. a.!(n+1) .==. 1) $ do {
    qnot_at (b.!(n+1))
  }
  comment_with_label "EXIT: setParent" (a, b, isparent) ("a", "b", "isparent")
  return ()

-- | Similar to 'setParent', but set /b/ to the node label of the
-- indicated child of /a/. Here /a/ and /b/ are quantum registers of
-- length at least /n/+2, and /f/ and /g/ are boolean registers of
-- length /n/.
setChild :: (Qureg, Qureg, Qubit, Qubit, Boolreg, Boolreg, Int) -> Circ ()
setChild (a, b, ischild, direction, f, g, n) = do
  comment_with_label "ENTER: setChild" (a, b, ischild, direction) ("a", "b", "ischild", "direction")
  with_ancilla $ \childctrl -> do
    with_controls (ischild .==. 1 .&&. a.!(n) .==. 1) $ do {
      qnot_at childctrl
    }
    setWeld (a, b, childctrl, direction, f, g, n)
    with_controls (ischild .==. 1) $ do {
      qnot_at childctrl
    }
    setChildInTree (a, b, childctrl, direction, n)
    with_controls (ischild .==. 1 .&&. a.!(n) .==. 0) $ do {
      qnot_at childctrl
    }
  comment_with_label "EXIT: setChild" (a, b, ischild, direction) ("a", "b", "ischild", "direction")
  return ()
      
-- | A special case of 'setChild', where the child is inside the same
-- binary tree (i.e., not via the welding). 
setChildInTree :: (Qureg, Qureg, Qubit, Qubit, Int) -> Circ ()
setChildInTree (a, b, childctrl, direction, n) = do
  comment_with_label "ENTER: setChildInTree" (a, b, childctrl, direction) ("a", "b", "childctrl", "direction")
  with_controls (childctrl .==. 1 .&&. direction .==. 1) $ do {
    qnot_at (b.!(0))
  }
  for 1 n 1 $ \index -> do
    with_controls (childctrl .==. 1 .&&. a.!(index-1) .==. 1) $ do {
      qnot_at (b.!(index))
    }
  endfor
  with_controls (childctrl .==. 1 .&&. a.!(n+1) .==. 1) $ do {
    qnot_at (b.!(n+1))
  }
  comment_with_label "EXIT: setChildInTree" (a, b, childctrl, direction) ("a", "b", "childctrl", "direction")
  return ()

-- | A special case of 'setChild', where the child is in the opposite
-- binary tree, i.e., we follow one of the welding edges.
setWeld :: (Qureg, Qureg, Qubit, Qubit, Boolreg, Boolreg, Int) -> Circ ()
setWeld (a, b, childctrl, direction, f, g, n) = do
  comment_with_label "ENTER: setWeld" (a, b, childctrl, direction) ("a", "b", "childctrl", "direction")
  with_ancilla $ \weldctrl -> do
    with_controls (childctrl .==. 1 .&&. direction .==. 0) $ do {
      qnot_at weldctrl
    }
    doWeld0 (a, b, weldctrl, f, n)
    with_controls (childctrl .==. 1) $ do {
      qnot_at weldctrl
    }
    doWeld1 (a, b, weldctrl, g, n)
    with_controls (childctrl .==. 1 .&&. direction .==. 1) $ do {
      qnot_at weldctrl
    }
    with_controls (childctrl .==. 1 .&&. a.!(n+1) .==. 1) $ do {
      qnot_at (b.!(n+1))
    }
    with_controls (childctrl .==. 1) $ do {
      qnot_at (b.!(n));
      qnot_at (b.!(n+1))
    }
  comment_with_label "EXIT: setWeld" (a, b, childctrl, direction) ("a", "b", "childctrl", "direction")
  return ()

-- | Input a node label /a/, and a register /b/ initialized to
-- |0〉. If /weldctrl/ is set, set /b/ to the node connected to /a/
-- by the welding function /f/. This is self-inverse. Here, /a/ and
-- /b/ are quantum registers of length at least /n/+2, and /f/ is a
-- boolean register of length /n/.
doWeld1 :: (Qureg, Qureg, Qubit, Boolreg, Int) -> Circ ()
doWeld1 (a, b, weldctrl, f, n) = do
  comment_with_label "ENTER: doWeld1" (a, b, weldctrl) ("a", "b", "weldctrl")
  with_ancilla $ \addsub -> do
    with_controls (weldctrl .==. 1 .&&. a.!(n+1) .==. 0) $ do {
      qnot_at addsub
    }
    cAddNum (addsub, b, a, f, n)
    with_controls (weldctrl .==. 1) $ do {
      qnot_at addsub
    }
    cSubNum (addsub, b, a, f, n)
    with_controls (weldctrl .==. 1 .&&. a.!(n+1) .==. 1) $ do {
      qnot_at addsub
    }
  comment_with_label "EXIT: doWeld1" (a, b, weldctrl) ("a", "b", "weldctrl")
  return ()

-- | Input a node label /a/, and a register /b/ initialized to
-- |0〉. If /weldctrl/ is set, set /b/ to the node connected to /a/
-- by the welding function /g/. This is self-inverse. Here, /a/ and
-- /b/ are quantum registers of length at least /n/+2, and /g/ is a
-- boolean register of length /n/.
doWeld0 :: (Qureg, Qureg, Qubit, Boolreg, Int) -> Circ ()
doWeld0 (a, b, weldctrl, g, n) = do
  comment_with_label "ENTER: doWeld0" (a, b, weldctrl) ("a", "b", "weldctrl")
  for 0 (n-1) 1 $ \index -> do
    with_controls (weldctrl .==. 1) $ do {
      qnot_at (b.!(index)) `controlled` a.!(index) ./=. g.!(index)
    }
  endfor
  comment_with_label "EXIT: doWeld0" (a, b, weldctrl) ("a", "b", "weldctrl")
  return ()

-- | This function implements integer addition. Input a quantum
-- register /input/ and a boolean register /num/, representing
-- integers, and a quantum register /out/ initialized to |0〉. If
-- /control/ is set, set /out/ to /input/ + /num/, otherwise do
-- nothing.  Here /input/ and /out/ are quantum registers of length at
-- least /n/, /num/ is a boolean register of length /n/.
cAddNum :: (Qubit, Qureg, Qureg, Boolreg, Int) -> Circ ()
cAddNum (control, out, input, num, n) = do
  comment_with_label "ENTER: cAddNum" (control, out, input) ("control", "out", "input")
  -- we represent mask as 1 << maskbit
  with_ancilla_reg n $ \scratch -> do
    let maskbit = 0  -- invariant: mask = 1 << maskbit
    with_controls (control .==. 1 .&&. input.!(0) .==. 1) $ do {
      qnot_at (out.!(0))
    }
    with_controls (num.!(maskbit) /= 0) $ do {
      with_controls (control .==. 1) $ do {
        qnot_at (out.!(0))
      };
      with_controls (input.!(0) .==. 1) $ do {
        qnot_at (scratch.!(0))
      }
    }
    for 1 (n-1) 1 $ \index -> do
      let maskbit = index   -- invariant: mask = 1 << maskbit
      with_controls (control .==. 1 .&&. input.!(index) .==. 1) $ do {
        qnot_at (out.!(index))
      }
      with_controls (num.!(maskbit) /= 0 .&&. control .==. 1) $ do {
        qnot_at (out.!(index))
      }
      with_controls (control .==. 1 .&&. scratch.!(index-1) .==. 1) $ do {
        qnot_at (out.!(index))
      }
      with_controls (num.!(maskbit) /= 0 .&&. input.!(index) .==. 1) $ do {
        qnot_at (scratch.!(index))
      }
      with_controls (input.!(index) .==. 1 .&&. scratch.!(index-1) .==. 1) $ do {
        qnot_at (scratch.!(index))
      }
      with_controls (num.!(maskbit) /= 0 .&&. scratch.!(index-1) .==. 1) $ do {
        qnot_at (scratch.!(index))
      }
    endfor
    cAddNumClear (control, scratch, input, num, n)
  comment_with_label "EXIT: cAddNum" (control, out, input) ("control", "out", "input")
  return ()

-- | A helper function for clearing the scratch space used by 'cAddNum'.
cAddNumClear :: (Qubit, Qureg, Qureg, Boolreg, Int) -> Circ ()
cAddNumClear (control, scratch, input, num, n) = do
  comment_with_label "ENTER: cAddNumClear" (control, scratch, input) ("control", "scratch", "input")
  -- we represent mask as 1 << maskbit
  for (n-1) 1 (-1) $ \index -> do
    let maskbit = index   -- invariant: mask = 1 << maskbit
    with_controls (num.!(maskbit) /= 0 .&&. scratch.!(index-1) .==. 1) $ do {
      qnot_at (scratch.!(index))
    }
    with_controls (input.!(index) .==. 1 .&&. scratch.!(index-1) .==. 1) $ do {
      qnot_at (scratch.!(index))
    }
    with_controls (num.!(maskbit) /= 0 .&&. input.!(index) .==. 1) $ do {
      qnot_at (scratch.!(index))
    }
  endfor
  let maskbit = 0  -- invariant: mask = 1 << maskbit
  with_controls (num.!(maskbit) /= 0 .&&. input.!(0) .==. 1) $ do {
    qnot_at (scratch.!(0))
  }
  comment_with_label "EXIT: cAddNumClear" (control, scratch, input) ("control", "scratch", "input")
  return ()

-- | Like 'cAddNum', except subtract instead of adding. 
cSubNum :: (Qubit, Qureg, Qureg, Boolreg, Int) -> Circ ()
cSubNum (control, out, input, num, n) = do
  comment_with_label "ENTER: cSubNum" (control, out, input) ("control", "out", "input")
  -- we represent mask as 1 << maskbit
  with_ancilla_reg n $ \scratch -> do
    let maskbit = 0  -- invariant: mask = 1 << maskbit
    with_controls (control .==. 1 .&&. input.!(0) .==. 1) $ do {
      qnot_at (out.!(0))
    }
    with_controls (num.!(maskbit) /= 0) $ do {
      with_controls (control .==. 1) $ do {
        qnot_at (out.!(0))
      };
      with_controls (input.!(0) .==. 0) $ do {
        qnot_at (scratch.!(0))
      }
    }
    for 1 (n-1) 1 $ \index -> do
      let maskbit = index    -- invariant: mask = 1 << maskbit
      with_controls (control .==. 1 .&&. input.!(index) .==. 1) $ do {
        qnot_at (out.!(index))
      }
      with_controls (num.!(maskbit) /= 0 .&&. control .==. 1) $ do {
        qnot_at (out.!(index))
      }
      with_controls (control .==. 1 .&&. scratch.!(index-1) .==. 1) $ do {
        qnot_at (out.!(index))
      }
      with_controls (num.!(maskbit) /= 0 .&&. input.!(index) .==. 0) $ do {
        qnot_at (scratch.!(index))
      }
      with_controls (input.!(index) .==. 0 .&&. scratch.!(index-1) .==. 1) $ do {
        qnot_at (scratch.!(index))
      }
      with_controls (num.!(maskbit) /= 0 .&&. scratch.!(index-1) .==. 1) $ do {
        qnot_at (scratch.!(index))
      }
    endfor
    cSubNumClear (control, scratch, input, num, n)
  comment_with_label "EXIT: cSubNum" (control, out, input) ("control", "out", "input")
  return ()

-- | A helper function for clearing the scratch space used by 'cSubNum'.
cSubNumClear :: (Qubit, Qureg, Qureg, Boolreg, Int) -> Circ ()
cSubNumClear (control, scratch, input, num, n) = do
  comment_with_label "ENTER: cSubNumClear" (control, scratch, input) ("control", "scratch", "input")
  -- we represent mask as 1 << maskbit
  for (n-1) 1 (-1) $ \index -> do
    let maskbit = index  -- invariant: mask = 1 << maskbit
    with_controls (num.!(maskbit) /= 0 .&&. scratch.!(index-1) .==. 1) $ do {
      qnot_at (scratch.!(index))
    }
    with_controls (input.!(index) .==. 0 .&&. scratch.!(index-1) .==. 1) $ do {
      qnot_at (scratch.!(index))
    }
    with_controls (num.!(maskbit) /= 0 .&&. input.!(index) .==. 0) $ do {
      qnot_at (scratch.!(index))
    }
  endfor
  let maskbit = 0  -- invariant: mask = 1 << maskbit
  with_controls (num.!(maskbit) /= 0 .&&. input.!(0) .==. 0) $ do {
    qnot_at (scratch.!(0))
  }
  comment_with_label "EXIT: cSubNumClear" (control, scratch, input) ("control", "scratch", "input")
  return ()

-- ----------------------------------------------------------------------
-- ** The oracle data structure

-- | This function inputs two welding functions /f/ and /g/, and
-- returns the oracle defined by the preceding functions. 
-- 
-- We call this the \"orthodox\" oracle, because the implementation
-- follows its specification very closely. For example, it uses a very
-- \"imperative\" programming style. For alternative implementations
-- of this and other oracles, see the modules
-- "Algorithms.BWT.Alternative" and "Algorithms.BWT.Template".
oracle_orthodox :: Boollist -> Boollist -> Oracle
oracle_orthodox f g =
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
    f_reg = boolreg_of_boollist_te f
    g_reg = boolreg_of_boollist_te g
    
    oraclefun :: Int -> (Qureg, Qureg, Qubit) -> Circ ()
    oraclefun c (a,b,r) = do
      let color = boolreg_of_int_le 2 c
      oracle (a, b, r, color, f_reg, g_reg, n)
      return ()

-- ======================================================================
-- * Main functions

-- These functions are so that the user can output something.

-- | Output the circuit for the quantum walk and a binary welded tree,
-- for the given 'Oracle' in the specified 'Format' and using the
-- specified 'GateBase'. Use /s/ time steps of length /dt/.
main_circuit :: Format -> GateBase -> Oracle -> Int -> Timestep -> IO()
main_circuit format base oracle s dt =
  print_generic format (decompose_generic base circuit)
  where
    circuit = qrwbwt oracle s dt

-- | Output the circuit for the given 'Oracle' and the given color
-- (specified as an 'Int'). Use the specified output 'Format' and
-- 'GateBase'.
main_oracle :: Format -> GateBase -> Oracle -> Int -> IO()
main_oracle format base oracle c =
  let m' = m oracle 
      ofun = oraclefun oracle
      circuit = (\(a,b,r) -> ofun c (qureg_of_qulist_te a, qureg_of_qulist_te b, r))
  in
   print_generic format (decompose_generic base circuit) (replicate m' qubit, replicate m' qubit, qubit)
