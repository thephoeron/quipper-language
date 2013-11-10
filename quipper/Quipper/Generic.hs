-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-} 

-- | This module provides functions and operators that are \"generic\"
-- on quantum data. We say that a function is generic if it works at
-- any quantum data type, rather than just a specific type such as
-- 'Qubit'. For example, the generic function 'qinit' can be used to
-- initialize a qubit from a boolean, or a pair of qubits from a pair
-- of booleans, or a list of qubits from a list of booleans, and so
-- forth.
-- 
-- Some functions are also generic in the /number/ of arguments they
-- take, in addition to the type of the arguments. 

module Quipper.Generic (
  -- * Generic gates
  -- ** Initialization and termination
  qinit,
  qterm,
  qdiscard,
  cinit,
  cterm,
  cdiscard,
  qc_init,
  qc_init_with_shape,
  qc_term,
  qc_discard,
  -- ** Measurement and preparation
  measure,
  prepare,
  qc_measure,
  qc_prepare,
  -- ** Global phase gate
  global_phase_anchored,
  -- ** Mapped gates
  map_hadamard,
  map_hadamard_at,
  swap,
  swap_at,
  controlled_not,  
  controlled_not_at,
  bool_controlled_not,
  bool_controlled_not_at,
  qmultinot,
  qmultinot_at,
  -- ** Copying and uncopying
  qc_copy_fun,
  qc_uncopy_fun,
  qc_copy,
  qc_uncopy,
  -- ** Classical gates
  cgate_if,
  circ_if,
  -- ** Named gates
  named_gate,
  named_gate_at,
  named_rotation,
  named_rotation_at,
  extended_named_gate,
  extended_named_gate_at,
  -- ** Dynamic lifting
  dynamic_lift,
  
  -- * Mapping
  mapUnary,
  mapBinary,
  mapBinary_c,
  map2Q,
  qc_mapBinary,

  -- * Conversion to lists
  -- $CONVERSION
  qubits_of_qdata,
  qdata_of_qubits,
  endpoints_of_qcdata,
  qcdata_of_endpoints,
  
  -- * Shape related operations
  qc_false,
  qshape,
  
  -- * Bindings
  qc_bind,
  qc_unbind,
  
  -- * Generic controls
  -- $CONTROL
  (.&&.),
  (.==.),
  (./=.),
  -- * Generic encapsulation
  -- $encapsulate
  encapsulate_generic,
  encapsulate_generic_in_namespace,
  unencapsulate_generic,
  -- $dynamic_encapsulate
  encapsulate_dynamic,
  unencapsulate_dynamic,
  -- * Generic reversing
  reverse_generic,
  reverse_generic_curried,
  reverse_simple,
  reverse_simple_curried,
  reverse_generic_endo,
  reverse_generic_imp,
  reverse_endo_if,
  reverse_imp_if,
  -- * The QCurry type class
  QCurry (..),
  -- * Generic circuit transformations
  transform_unary_dynamic_shape,
  transform_unary_dynamic,
  transform_unary,
  transform_generic,
  transform_unary_shape,
  transform_generic_shape,
  -- * Generic block structure
  with_ancilla_init,
  with_ancilla_list,
  with_computed_fun,
  with_computed,
  with_basis_change,
  with_classical_control,
  -- * Boxed subcircuits
  provide_subroutine_generic,
  box,
  nbox,
  box_loopM,
  loopM_boxed_if,
  inline_subroutine
  ) where

-- import other Quipper stuff
import Quipper.Circuit
import Quipper.Monad
import Libraries.Auxiliary
import Libraries.Tuple
import Quipper.Transformer
import Quipper.Control
import Quipper.QData

-- import other stuff
import Control.Monad
import Prelude
import Data.Typeable
import qualified Control.Monad.State as State

import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

-- ======================================================================
-- * Generic gates

-- ** Initialization and termination

-- | Initialize a qubit from a boolean parameter. More generally,
-- initialize a data structure of qubits from a corresponding data
-- structure of boolean parameters. Examples:
-- 
-- > q <- qinit False
-- > (q0, q1) <- qinit (True, False)
-- > [q0, q1, q2] <- qinit [True, False, True]
qinit :: (QShape ba qa ca) => ba -> Circ qa
qinit ba = qdata_mapM (shapetype_b ba) qinit_qubit ba

-- | Terminate a qubit, asserting its state to equal the boolean
-- parameter. More generally, terminate a data structure of qubits,
-- asserting that their state is as given by a data structure of
-- booleans parameters. Examples:
-- 
-- > qterm False q
-- > qterm (False, False) (q0, q1)
-- > qterm [False, False, False] [q0, q1, q2]
-- 
-- In some cases, it is permissible for some aspect of the parameter's
-- shape to be underspecified, e.g., a longer than necessary list, or
-- an integer of indeterminate length. It is therefore possible, for
-- example, to write:
-- 
-- > qterm 17 qa          -- when qa :: QDInt,
-- > qterm [False..] qa   -- when qa :: [Qubit].
-- 
-- The rules for when a boolean argument can be \"promoted\" in this
-- way are specific to each individual data type.
qterm :: (QShape ba qa ca) => ba -> qa -> Circ ()
qterm ba qa = do
  let shape = shapetype_b ba                  -- shape type  
  let ba' = qdata_promote ba qa errmsg  -- shape data
  let z = qdata_zip shape bool qubit ba' qa errmsg
  qdata_mapM_op shape (\(x,y) -> qterm_qubit x y) z
  return ()
  where
    errmsg s = "qterm: shape of parameter does not match data: " ++ s

-- | Discard a qubit, ignoring its state. This can leave the quantum
-- system in a mixed state, so is not a reversible operation. More
-- generally, discard all the qubits in a quantum data
-- structure. Examples:
-- 
-- > qdiscard q
-- > qdiscard (q0, q1)
-- > qdiscard [q0, q1, q2]
qdiscard :: (QData qa) => qa -> Circ ()
qdiscard qa = do
  qdata_mapM_op (shapetype_q qa) qdiscard_qubit qa
  return ()
  
-- | Initialize a 'Bit' (boolean input) from a 'Bool' (boolean
-- parameter). More generally, initialize the a data structure of Bits
-- from a corresponding data structure of Bools. Examples:
-- 
-- > b <- cinit False
-- > (b0, b1) <- cinit (True, False)
-- > [b0, b1, b2] <- cinit [True, False, True]
cinit :: (QShape ba qa ca) => ba -> Circ ca
cinit ba = qdata_mapM (shapetype_b ba) cinit_bit ba

-- | Terminate a 'Bit', asserting its state to equal the given
-- 'Bool'. More generally, terminate a data structure of Bits,
-- asserting that their state is as given by a data structure of
-- Bools. Examples:
-- 
-- > cterm False b
-- > cterm (False, False) (b0, b1)
-- > cterm [False, False, False] [b0, b1, b2]
-- 
-- In some cases, it is permissible for some aspect of the parameter's
-- shape to be underspecified, e.g., a longer than necessary list, or
-- an integer of indeterminate length. It is therefore possible, for
-- example, to write:
-- 
-- > cterm 17 ca          -- when ca :: CInt,
-- > cterm [False..] ca   -- when ca :: [Bit].
-- 
-- The rules for when a boolean argument can be \"promoted\" in this
-- way are specific to each individual data type.
cterm :: (QShape ba qa ca) => ba -> ca -> Circ ()
cterm ba ca = do
  -- shape type
  let shape = shapetype_b ba
  -- shape data
  let ba' = qdata_promote_c ba ca errmsg
  let z = qdata_zip shape bool bit ba' ca errmsg
  qdata_mapM_op shape (\(x,y) -> cterm_bit x y) z
  return ()
  where
    errmsg s = "cterm: shape of parameter does not match data: " ++ s

-- | Discard a 'Bit', ignoring its state. This can leave the system in
-- a mixed state, so is not a reversible operation. More generally,
-- discard all the Bits in a data structure. Examples:
-- 
-- > cdiscard b
-- > cdiscard (b0, b1)
-- > cdiscard [b0, b1, b2]
cdiscard :: (CData ca) => ca -> Circ ()
cdiscard ca = do
  qdata_mapM_op (shapetype_c ca) cdiscard_bit ca
  return ()

-- | Heterogeneous version of 'qinit'. Please note that the type of
-- the result of this function cannot be inferred from the type of the
-- argument. For example, 
-- 
-- > x <- qc_init False
-- 
-- is ambiguous, unless it can be inferred from the context whether
-- /x/ is a 'Bit' or a 'Qubit'. If the type cannot be inferred from
-- the context, it needs to be stated explicitly, like this:
-- 
-- > x <- qc_init False :: Circ Qubit
--    
-- Alternatively, 'qc_init_with_shape' can be used to fix a specific
-- type.
qc_init :: (QCData qc) => BType qc -> Circ qc
qc_init bs = qc_init_with_shape (undefined :: qc) bs

-- | A version of 'qc_init' that uses a shape type parameter. The
-- first argument is the shape type parameter, and the second argument
-- is a data structure containing boolean initializers. The shape type
-- argument determines which booleans are used to initialize qubits,
-- and which ones are used to initialize classical bits.
-- 
-- Example:
-- 
-- > (x,y) <- qc_init_with_shape (bit,[qubit]) (True, [False,True])
-- 
-- This will assign to /x/ a classical bit initialized to 1, and to
-- /y/ a list of two qubits initialized to |0〉 and |1〉, respectively.
qc_init_with_shape :: (QCData qc) => qc -> BType qc -> Circ qc
qc_init_with_shape shape bs = qcdata_mapM shape qinit_qubit cinit_bit bs

-- | Heterogeneous version of 'qterm'. 
qc_term :: (QCData qc) => BType qc -> qc -> Circ ()
qc_term bs qc = do
  let bs' = qcdata_promote bs qc errmsg
  let z = qcdata_zip qc bool bool qubit bit bs' qc errmsg
  qcdata_mapM_op qc map_qubit map_bit z 
  return ()
  where    
    
    map_qubit :: (Bool, Qubit) -> Circ ()
    map_qubit (b,q) = qterm_qubit b q

    map_bit :: (Bool, Bit) -> Circ ()
    map_bit (b,q) = cterm_bit b q

    errmsg s = "qc_term: shape of parameter does not match data: " ++ s

-- | Heterogeneous version of 'qdiscard'.
qc_discard :: (QCData qc) => qc -> Circ ()
qc_discard qc = do
  qcdata_mapM_op qc qdiscard_qubit cdiscard_bit qc
  return ()

-- ----------------------------------------------------------------------
-- ** Measurement and preparation

-- | Measure a 'Qubit', resulting in a 'Bit'. More generally, measure
-- all the Qubits in a quantum data structure, resulting in a
-- corresponding data structure of Bits. This is not a reversible
-- operation. Examples:
-- 
-- > b <- measure q
-- > (b0, b1) <- measure (q0, q1)
-- > [b0, b1, b2] <- measure [q0, q1, q2]
measure :: (QShape ba qa ca) => qa -> Circ ca
measure qa = qdata_mapM_op (shapetype_q qa) measure_qubit qa

-- | Prepare a 'Qubit' initialized from a 'Bit'. More generally,
-- prepare a data structure of Qubits, initialized from a corresponding
-- data structure of Bits. Examples:
-- 
-- > q <- prepare b
-- > (q0, q1) <- prepare (b0, b1)
-- > [q0, q1, q2] <- prepare [b0, b1, b2]
prepare :: (QShape ba qa ca) => ca -> Circ qa
prepare ca = qdata_mapM (shapetype_c ca) prepare_qubit ca

-- | Heterogeneous version of 'measure'. Given a heterogeneous data
-- structure, measure all of its qubits, and leave any classical bits
-- unchanged.
qc_measure :: (QCData qc) => qc -> Circ (QCType Bit Bit qc)
qc_measure qc = qcdata_mapM_op qc measure_qubit do_bit qc 
  where 
    do_bit :: Bit -> Circ Bit
    do_bit = return                                                         

-- | Heterogeneous version of 'measure'. Given a heterogeneous data
-- structure, prepare qubits from all classical bits, and leave any
-- qubits unchanged.
qc_prepare :: (QCData qc) => qc -> Circ (QCType Qubit Qubit qc)
qc_prepare qc = qcdata_mapM qc do_qubit prepare_qubit qc 
  where
    do_qubit :: Qubit -> Circ Qubit
    do_qubit = return

-- ----------------------------------------------------------------------
-- * Global phase gate
  
-- | Like 'global_phase', except the gate is also \"anchored\" at a
-- qubit, a bit, or more generally at some quantum data. The anchor
-- is only used as a hint for graphical display. The gate, which is a
-- zero-qubit gate, will potentially be displayed near the anchor(s).
global_phase_anchored :: (QCData qc) => Double -> qc -> Circ ()
global_phase_anchored t qc = global_phase_anchored_list t qs where
  qs = endpoints_of_qcdata qc

-- ----------------------------------------------------------------------
-- * Mapped gates

-- | Apply a Hadamard gate to every qubit in a quantum data structure.
map_hadamard :: (QData qa) => qa -> Circ qa
map_hadamard = mapUnary hadamard

-- | Imperative version of 'map_hadamard'.
map_hadamard_at :: (QData qa) => qa -> Circ ()
map_hadamard_at qa = do
  map_hadamard qa
  return ()

-- | Apply a swap gate to two qubits. More generally, apply swap gates
-- to every corresponding pair of qubits in two pieces of quantum
-- data.
swap :: (QCData qc) => qc -> qc -> Circ (qc,qc)
swap a b = qc_mapBinary swap_qubit swap_bit a b

-- | Apply a swap gate to two qubits. More generally, apply swap gates
-- to every corresponding pair of qubits in two pieces of quantum
-- data.
swap_at :: (QCData qc) => qc -> qc -> Circ ()
swap_at a b = do
  swap a b
  return ()

-- | Apply a controlled-not gate to every corresponding pair of
-- quantum or classical bits in two pieces of QCData. The first
-- argument is the target and the second the (positive) control.  
-- 
-- For now, we require both pieces of QCData to have the same type,
-- i.e., classical bits can be controlled only by classical bits and
-- quantum bits can be controlled only by quantum bits.
-- 
-- Example:
-- 
-- > ((a',b'), (x,y)) <- controlled_not (a,b) (x,y)
-- 
-- is equivalent to
-- 
-- > a' <- qnot a `controlled` x
-- > b' <- qnot b `controlled` y
controlled_not :: (QCData qc) => qc -> qc -> Circ (qc, qc)
controlled_not qc ctrl = do
  let z = qcdata_zip qc qubit bit qubit bit qc ctrl errmsg
  z' <- qcdata_mapM qc map_qubit map_bit z
  let (qc', ctrl') = qcdata_unzip qc qubit bit qubit bit z'
  return (qc', ctrl')
  where
    
    map_qubit :: (Qubit, Qubit) -> Circ (Qubit, Qubit)
    map_qubit (q,c) = do
      qnot_at q `controlled` c
      return (q,c)

    map_bit :: (Bit, Bit) -> Circ (Bit, Bit)
    map_bit (b,c) = do
      cnot_at b `controlled` c
      return (b,c)

    errmsg s = "controlled_not: shapes of control and controlee do not match: " ++ s

-- | Imperative version of 'controlled_not'. Apply a controlled-not
-- gate to every corresponding pair of quantum or classical bits in
-- two pieces of QCData. The first argument is the target and the
-- second the (positive) control.
controlled_not_at :: (QCData qc) => qc -> qc -> Circ ()
controlled_not_at a b = do
  controlled_not a b
  return ()

-- | A version of 'controlled_not' where the control consists of
-- boolean data. Example:
-- 
-- > bool_controlled_not (q, r, s) (True, True, False)
-- 
-- negates /q/ and /r/, but not /s/.
bool_controlled_not :: (QCData qc) => qc -> BType qc -> Circ qc
bool_controlled_not qc a = do
  bool_controlled_not_at qc a
  return qc

-- | A version of 'controlled_not_at' where the control consists of
-- boolean data. Example:
-- 
-- > bool_controlled_not_at (q, r, s) (True, True, False)
-- 
-- negates /q/ and /r/, but not /s/.
bool_controlled_not_at :: (QCData qc) => qc -> BType qc -> Circ ()
bool_controlled_not_at qc a = do
  qmultinot_list_at vq 
  cmultinot_list_at vc 
  where
    v = Map.toList $ qc_bind qc a
    vq = [ (qubit_of_wire q, b) | (q, Endpoint_Qubit b) <- v ]
    vc = [ (bit_of_wire c, b) | (c, Endpoint_Bit b) <- v ]

-- | Negate all qubits in a quantum data structure.
qmultinot :: (QData qa) => qa -> Circ qa
qmultinot qa = do
  qmultinot_at qa
  return qa

-- | Negate all qubits in a quantum data structure.
qmultinot_at :: (QData qa) => qa -> Circ ()
qmultinot_at qa =
  qmultinot_list_at [ (q,True) | q <- qubits_of_qdata qa ]

-- ----------------------------------------------------------------------
-- ** Copying and uncopying

-- | Initialize a new piece of quantum data, as a copy of a given
-- piece.  Returns both the original and the copy.
qc_copy_fun :: (QCData qc) => qc -> Circ (qc,qc)
qc_copy_fun orig = do
  copy <- qc_init (qc_false orig)
  (copy, orig) <- controlled_not copy orig
  return (orig, copy)
    
-- | Given two pieces of quantum data, assumed equal (w.r.t. the
-- computational basis), terminate the second piece (and return the
-- first, unmodified). This is the inverse of 'qc_copy_fun', in the sense
-- that the following sequence of instructions behaves like the
-- identity function:
-- 
-- > (orig, copy) <- qc_copy_fun orig
-- > orig <- qc_uncopy_fun orig copy
qc_uncopy_fun :: (QCData qc) => qc -> qc -> Circ qc
qc_uncopy_fun orig copy = reverse_generic qc_copy_fun orig (orig,copy) 

-- | Create a fresh copy of a piece of quantum data. Note: copying is
-- performed via a controlled-not operation, and is not cloning. This
-- is similar to 'qc_copy_fun', except it returns only the copy, and not
-- the original.
qc_copy :: (QCData qc) => qc -> Circ qc
qc_copy qc = do
  (qc, qc1) <- qc_copy_fun qc
  return qc1

-- | \"Uncopy\" a piece of quantum data; i.e. terminate /copy/,
-- assuming it's a copy of /orig/. This is the inverse of
-- 'qc_copy', in the sense that the following sequence of
-- instructions behaves like the identity function:
-- 
-- > b <- qc_copy a
-- > qc_uncopy a b
qc_uncopy :: (QCData qc) => qc -> qc -> Circ ()
qc_uncopy orig copy = do
  qc_uncopy_fun orig copy
  return ()

-- ----------------------------------------------------------------------
-- ** Classical gates

-- | If /a/ is 'True', return a copy of /b/, else return a copy of
-- /c/. Here /b/ and /c/ can be any data structures consisting of
-- Bits, but /b/ and /c/ must be of the same type and shape (for
-- example, if they are lists, they must be of equal
-- length). Examples:
-- 
-- > output <- cgate_if a b c
-- > (out0, out1) <- cgate_if a (b0, b1) (c0, c1)
-- > [out0, out1, out2] <- cgate_if a [b0, b1, b2] [c0, c1, c2]
cgate_if :: (CData ca) => Bit -> ca -> ca -> Circ ca
cgate_if a b c = do
  let shape = shapetype_c b
  let z = qdata_zip shape bit bit b c errmsg
  d <- qdata_mapM shape (\(x,y) -> cgate_if_bit a x y) z
  return d
  where
    errmsg s = "cgate_if: shapes of 'then' and 'else' part do not match: " ++ s

-- | 'circ_if' is an if-then-else function for classical circuits. 
-- It is a wrapper around 'cgate_if', intended to be used like this:
-- 
-- > result <- circ_if <<<condition>>> (
-- >   <<then-part>>>
-- >   )(
-- >   <<<else-part>>>
-- >   )
-- 
-- Unlike 'cgate_if', this is a meta-operation, i.e., the bodies of
-- the \"then\" and \"else\" parts can be circuit building
-- operations. 
-- 
-- What makes this different from the usual boolean \"if-then-else\"
-- is that the condition is of type 'Bit', i.e., it is only known at
-- circuit execution time. Therefore the generated circuit contains
-- /both/ the \"then\" and \"else\" parts, suitably
-- controlled. Precondition: the \"then\" and \"else\" parts must be
-- of the same type and shape.
circ_if :: (CData ca) => Bit -> Circ ca -> Circ ca -> Circ ca
circ_if a b c = do
  b' <- b
  c' <- c
  cgate_if a b' c'

-- ----------------------------------------------------------------------
-- ** Named gates

-- | Define a new functional-style gate of the given name. Like
-- 'named_gate', except that the generated gate is extended with
-- \"generalized controls\". The generalized controls are additional
-- inputs to the gate that are guaranteed not to be modified if they
-- are in a computational basis state. They are rendered in a special
-- way in circuit diagrams. Usage:
-- 
-- > my_new_gate :: (Qubit,Qubit) -> Qubit -> Circ (Qubit,Qubit)
-- > my_new_gate = extended_named_gate "Q"
-- 
-- This defines a new gate with name "Q", two inputs, and one
-- generalized input.
extended_named_gate :: (QData qa, QData qb) => String -> qa -> qb -> Circ qa
extended_named_gate name operands gencontrols = do
  named_gate_qulist_at name False (qubits_of_qdata operands) (qubits_of_qdata gencontrols)
  return operands

-- | Like 'extended_named_gate', except defines an imperative style gate.
-- Usage:
-- 
-- > my_new_gate_at :: (Qubit,Qubit) -> Qubit -> Circ ()
-- > my_new_gate_at = extended_named_gate_at "Q"
-- 
-- This defines a new gate with name "Q", two inputs, and one
-- generalized input.
extended_named_gate_at :: (QData qa, QData qb) => String -> qa -> qb -> Circ ()
extended_named_gate_at name operands gencontrols = do
  extended_named_gate name operands gencontrols
  return ()

-- | Define a new functional-style gate of the given name. Usage:
-- 
-- > my_unary_gate :: Qubit -> Circ Qubit
-- > my_unary_gate = named_gate "Q"
-- 
-- > my_binary_gate :: (Qubit, Qubit) -> Circ (Qubit, Qubit)
-- > my_binary_gate = named_gate "R"
--   
-- This defines a new unary gate and a new binary gate, which will be
-- rendered as "Q" and "R", respectively, in circuit diagrams. 

-- Implementation note: contrary to our usual convention, the binary
-- gate defined above is not in curried form. It would be nice to have
-- a version of this operator that curries the gate.
named_gate :: (QData qa) => String -> qa -> Circ qa
named_gate name operands = do
  extended_named_gate name operands ()

-- | Define a new imperative-style gate of the given name. Usage:
-- 
-- > my_unary_gate_at :: Qubit -> Circ ()
-- > my_unary_gate_at = named_gate_at "Q"
-- 
-- > my_binary_gate_at :: (Qubit, Qubit) -> Circ ()
-- > my_binary_gate_at = named_gate_at "R"
--   
-- This defines a new unary gate and a new binary gate, which will be
-- rendered as "Q" and "R", respectively, in circuit diagrams. 

named_gate_at :: (QData qa) => String -> qa -> Circ ()
named_gate_at name operands = do
  named_gate name operands
  return ()

-- | Define a new functional-style gate of the given name, and
-- parameterized by a real-valued parameter. This is typically used
-- for rotations or phase gates that are parameterized by an angle.
-- The name can contain \'%\' as a place holder for the parameter.
-- Usage:
-- 
-- > my_unary_gate :: Qubit -> Circ Qubit
-- > my_unary_gate = named_rotation "exp(-i%Z)" 0.123
-- 
-- > my_binary_gate :: TimeStep -> (Qubit, Qubit) -> Circ (Qubit, Qubit)
-- > my_binary_gate t = named_rotation "Q(%)" t
named_rotation :: (QData qa) => String -> Timestep -> qa -> Circ qa
named_rotation name theta operands = do
  named_rotation_qulist_at name False theta (qubits_of_qdata operands) []
  return operands

-- | Define a new imperative-style gate of the given name, and
-- parameterized by a real-valued parameter. This is typically used
-- for rotations or phase gates that are parameterized by an angle.
-- The name can contain \'%\' as a place holder for the parameter.
-- Usage:
-- 
-- > my_unary_gate_at :: Qubit -> Circ ()
-- > my_unary_gate_at = named_rotation "exp(-i%Z)" 0.123
-- 
-- > my_binary_gate_at :: TimeStep -> (Qubit, Qubit) -> Circ ()
-- > my_binary_gate_at t = named_rotation "Q(%)" t
named_rotation_at :: (QData qa) => String -> Timestep -> qa -> Circ ()
named_rotation_at name theta operands = do
  named_rotation name theta operands
  return ()

----------------------------------------------------------------------
-- ** Dynamic lifting

-- | Convert a 'Bit' (boolean circuit output) to a 'Bool' (boolean
-- parameter). More generally, convert a data structure of Bits to a
-- corresponding data structure of Bools.
-- 
-- For use in algorithms that require the output of a measurement to
-- be used as a circuit-generation parameter. This is the case, for
-- example, for sieving methods, and also for some iterative
-- algorithms.
-- 
-- Note that this is not a gate, but a meta-operation. The input
-- consists of classical circuit endpoints (whose values are known at
-- circuit execution time), and the output is a boolean parameter
-- (whose value is known at circuit generation time). 
-- 
-- The use of this operation implies an interleaving between circuit
-- execution and circuit generation. It is therefore a (physically)
-- expensive operation and should be used sparingly. Using the
-- 'dynamic_lift' operation interrupts the batch mode operation of the
-- quantum device (where circuits are generated ahead of time), and
-- forces interactive operation (the quantum device must wait for the
-- next portion of the circuit to be generated). This operation is
-- especially expensive if the current circuit contains unmeasured
-- qubits; in this case, the qubits must be preserved while the
-- quantum device remains on standby.
-- 
-- Also note that this operation is not supported in all contexts. It
-- is an error, for example, to use this operation in a circuit that
-- is going to be reversed, or in the body of a boxed subroutine.
-- Also, not all output devices (such as circuit viewers) support this
-- operation.
dynamic_lift :: (QShape ba qa ca) => ca -> Circ ba
dynamic_lift ca = qdata_mapM (shapetype_c ca) dynamic_lift_bit ca

-- ----------------------------------------------------------------------
-- * Mapping

-- | Map a single qubit gate across every qubit in the data structure.
mapUnary :: (QData qa) => (Qubit -> Circ Qubit) -> qa -> Circ qa
mapUnary f qa = qdata_mapM (shapetype_q qa) f qa

-- | Map a binary gate across every corresponding pair of qubits in
-- two quantum data structures of equal shape.
mapBinary :: (QData qa) => (Qubit -> Qubit -> Circ (Qubit, Qubit)) -> qa -> qa -> Circ (qa, qa)
mapBinary f q1 q2 = do
  let shape = shapetype_q q1
  let z = qdata_zip shape qubit qubit q1 q2 errmsg
  z' <- qdata_mapM shape (\(x,y) -> f x y) z
  let (q1', q2') = qdata_unzip shape qubit qubit z'
  return (q1', q2')
  where
    errmsg s = "mapBinary: shapes of arguments do not match: " ++ s
  
-- | Like 'mapBinary', except the second data structure is classical.
mapBinary_c :: (QShape ba qa ca) => (Qubit -> Bit -> Circ (Qubit, Bit)) -> qa -> ca -> Circ (qa, ca)
mapBinary_c f q1 c2 = do
  let shape = shapetype_q q1
  let z = qdata_zip shape qubit bit q1 c2 errmsg
  z' <- qdata_mapM shape (\(x,y) -> f x y) z
  let (q1', c2') = qdata_unzip shape qubit bit z'
  return (q1', c2')
  where
    errmsg s = "mapBinary_c: shapes of arguments do not match: " ++ s

-- | Map a binary qubit circuit to every pair of qubits in the quantum
-- data-type. It is a run-time error if the two structures do not have
-- the same size.
map2Q :: (QData qa) => ((Qubit, Qubit) -> Circ Qubit) -> (qa, qa) -> Circ qa
map2Q f (q,p) = do
  let shape = shapetype_q q
  let z = qdata_zip shape qubit qubit q p errmsg
  d <- qdata_mapM shape f z
  return d
  where
    errmsg s = "map2Q: shapes of arguments do not match: " ++ s
  
-- | Heterogeneous version of 'mapBinary'. Map a binary gate /f/
-- across every corresponding pair of qubits, and a binary gate /g/
-- across every corresponding pair of bits, in two quantum data
-- structures of equal shape.
qc_mapBinary :: (QCData qc) => (Qubit -> Qubit -> Circ (Qubit, Qubit)) -> (Bit -> Bit -> Circ (Bit, Bit)) -> qc -> qc -> Circ (qc, qc)
qc_mapBinary f g x y = do
  let z = qcdata_zip x qubit bit qubit bit x y errmsg
  z' <- qcdata_mapM x map_qubit map_bit z
  let (x', y') = qcdata_unzip x qubit bit qubit bit z'
  return (x', y')
  where
    
    map_qubit :: (Qubit, Qubit) -> Circ (Qubit, Qubit)
    map_qubit (x,y) = f x y

    map_bit :: (Bit, Bit) -> Circ (Bit, Bit)
    map_bit (x,y) = g x y

    errmsg s = "qc_mapBinary: shapes of arguments do not match: " ++ s

-- ----------------------------------------------------------------------
-- * Conversion to lists

-- $CONVERSION The functions in this section can be used to convert
-- quantum data structures to and from lists. Do not use them! The
-- conversion is unsafe in the same way pointers to void are unsafe in
-- the C programming language. There is almost always a better and
-- more natural way to accomplish what you need to do.

-- | Return the list of qubits representing the given quantum data.
-- The qubits are ordered in some fixed, but arbitrary way. It is
-- guaranteed that two pieces of qdata of the same given shape will be
-- ordered in the same way. No other property of the order is
-- guaranteed, In particular, the order may change without notice from
-- one version of Quipper to the next.
qubits_of_qdata :: (QData qa) => qa -> [Qubit]
qubits_of_qdata qa = qdata_sequentialize (shapetype_q qa) qa

-- | Take a specimen piece of quantum data to specify the \"shape\"
-- desired (length of lists, etc); then reads the given list of qubits
-- in as a piece of quantum data of the same shape. The ordering of
-- the input qubits is the same as 'qubits_of_qdata' produces for the
-- given shape.
-- 
-- A \"length mismatch\" error occurs if the list does not have
-- exactly the required length.
qdata_of_qubits :: (QData qa) => qa -> [Qubit] -> qa
qdata_of_qubits qa list = qdata_unsequentialize qa list

-- | Return the list of endpoints that form the leaves of the given
-- 'QCData'. The leaves are ordered in some fixed, but arbitrary
-- way. It is guaranteed that two pieces of data of the same given
-- shape will be ordered in the same way. No other property of the
-- order is guaranteed. In particular, the order may change without notice from
-- one version of Quipper to the next.
endpoints_of_qcdata :: (QCData qc) => qc -> [Endpoint]
endpoints_of_qcdata qc = qcdata_sequentialize qc qc

-- | Take a specimen piece of 'QCData' to specify the \"shape\"
-- desired (length of lists, etc); then reads the given list of
-- endpoints in as a piece of quantum data of the same shape. The
-- ordering of the input endpoints equals that produced by
-- 'endpoints_of_qcdata' for the given shape.
-- 
-- A \"length mismatch\" error occurs if the list does not have
-- exactly the required length. A \"shape mismatch\" error occurs if
-- the list contains a 'Qubit' when a 'Bit' was expected, or vice versa. 
qcdata_of_endpoints :: (QCData qc) => qc -> [Endpoint] -> qc
qcdata_of_endpoints qc list = qcdata_unsequentialize qc list where

-- | Take a specimen piece of 'QCData' to specify a shape;
-- return a 'CircuitTypeStructure' that structures appropriate
-- lists of wires with arities into data of this shape, and conversely
-- destructures data of this shape into wires and an arity.
--
-- The caveats mentioned in 'endpoints_of_qcdata' apply equally for
-- this function.
circuit_type_structure_of_qcdata :: (QCData qc) => qc -> CircuitTypeStructure qc
circuit_type_structure_of_qcdata qc = CircuitTypeStructure
  (wires_with_arity_of_endpoints . endpoints_of_qcdata)
  (\(ws,a) -> qcdata_of_endpoints qc $ endpoints_of_wires_in_arity a ws)

-- ----------------------------------------------------------------------
-- * Shape related operations

-- | Return a boolean data structure of the given shape, with every
-- leaf initialized to 'False'.
qc_false :: (QCData qc) => qc -> BType qc
qc_false qc = qcdata_map qc map_qubit map_bit qc 
  where
    map_qubit = const False :: Qubit -> Bool
    map_bit = const False :: Bit -> Bool

-- | Return a quantum data structure of the given boolean shape, with
-- every leaf initialized to the undefined dummy value 'qubit'.
qshape :: (QData qa) => BType qa -> qa
qshape ba = qdata_map (shapetype_b ba) map_qubit ba
  where
    map_qubit = const qubit :: Bool -> Qubit

-- ----------------------------------------------------------------------
-- * Bindings

-- | Take two pieces of quantum data of the same shape (the first of
-- which consists of wires of a low-level circuit) and create
-- bindings.
qc_bind :: (QCData qc) => qc -> QCType a b qc -> Bindings a b
qc_bind qc as = qc_bind_aux qc as bindings_empty
  where
    -- This can't be inlined without upsetting the type checker.
    qc_bind_aux :: (QCData qc) => qc -> QCType a b qc -> Bindings a b -> Bindings a b
    qc_bind_aux qc as (bind_in :: Bindings a b) = bindings where
      a = (dummy :: a) -- shape type
      b = (dummy :: b) -- shape type
      z = qcdata_zip qc qubit bit a b qc as errmsg
      bindings = qcdata_fold qc do_qubit do_bit z bind_in
  
    do_qubit :: (Qubit, a) -> Bindings a b -> Bindings a b
    do_qubit (q, binding) = bind_qubit q binding
  
    do_bit :: (Bit, b) -> Bindings a b -> Bindings a b
    do_bit (c, binding) = bind_bit c binding

    errmsg s = "qc_bind: shapes of arguments do not match: " ++ s

-- | Apply bindings to a piece of quantum and/or classical data
-- holding low-level wires, to get data of the same shape.
qc_unbind :: (QCData qc) => Bindings a b -> qc -> QCType a b qc
qc_unbind (bindings :: Bindings a b) qc =
  qcdata_map qc map_qubit map_bit qc
  where
    map_qubit :: Qubit -> a
    map_qubit q = unbind_qubit bindings q
    
    map_bit :: Bit -> b
    map_bit b = unbind_bit bindings b

-- ======================================================================
-- * Generic controls

-- $CONTROL The following functions define a convenient syntax for
-- controls. With this, we can write controls in much the same way as
-- one would write (a restricted class of) boolean
-- expressions. Examples:
-- 
-- > q1 .==. 0 .&&. q2 .==. 1         for Qubits q1, q2
-- 
-- > q .&&. p                         means  q .==. 1  .&&.  p .==. 1
-- 
-- > qx .==. 5                        for a QDInt qx
-- 
-- > q1 .==. 0 .&&. z <= 7            we can combine quantum and classical controls
-- 
-- > q ./=. b                         the negation of q .==. b;
-- >                                  here b is a boolean.
-- 
-- > [p,q,r,s]                        a list of positive controls
-- 
-- > [(p, True), (q, False), (r, False), (s, True)]
-- >                                  a list of positive and negative controls
--
-- Among these infix operators, @(.&&.)@ binds more weakly than
-- @(.==.)@, @(./=.)@.

-- | Given a piece of quantum data and a possible value for it, return
-- a 'ControlList' representing the condition that the quantum data
-- has that value.
-- 
-- If some aspect of the value's shape is indeterminate, it is
-- promoted to the same shape as the quantum data; therefore, it is
-- possible, for example, to write:
-- 
-- > qc_control qa 17          -- when qa :: QDInt
-- > qc_control qa [False..]   -- when qa :: [Qubit]
qc_control :: (QCData qc) => qc -> BType qc -> ControlList
qc_control qc b = clist where
  b' = qcdata_promote b qc errmsg
  z = qcdata_zip qc qubit bit bool bool qc b' errmsg
  clist = qcdata_fold qc do_qubit do_bit z clist_empty
  
  do_qubit :: (Qubit, Bool) -> ControlList -> ControlList
  do_qubit (q, b) = clist_add_qubit q b
  
  do_bit :: (Bit, Bool) -> ControlList -> ControlList
  do_bit (c, b) = clist_add_bit c b

  errmsg s = "qc_control: shape of control value does not match data: " ++ s

-- | This is an infix operator to concatenate two controls, forming
-- their logical conjunction.
(.&&.) :: (ControlSource a, ControlSource b) => a -> b -> ControlList
exp1 .&&. exp2 = combine (to_control exp1) (to_control exp2)

-- | @(qx .==. x)@: a control which is true just if quantum data /qx/ is in the specified state /x/. 
(.==.) :: (QCData qc) => qc -> BType qc -> ControlList
qx .==. x = qc_control qx x

-- | The notation @(q ./=. x)@ is shorthand for @(q .==. not x)@, when
-- /x/ is a boolean parameter. 
-- 
-- Unlike '.==.', which is defined for any shape of quantum data,
-- './=.' is only defined for a single control bit or qubit.
(./=.) :: (QCLeaf q) => q -> Bool -> ControlList
q ./=. b = to_control [Signed q (not b)]

-- Set the precedence for infix operators '.&&.', '.==.', and './=.'.
infixr 3 .&&. -- same precedence as (&&)
infix 4 .==. -- same precedence as (==)
infix 4 ./=. -- same precedence as (/=)

-- The following allows us to write 0 and 1 instead of 'False' and
-- 'True' everywhere.
instance Num Bool where
  (+) = (/=) 
  (*) = (&&)
  (-) = (/=)
  negate = id
  signum = id
  abs = id
  fromInteger n = (n `mod` 2 == 1)

-- ======================================================================
-- * Generic encapsulation

-- $encapsulate
-- 
-- An encapsulated circuit is a low-level circuit together with data
-- structures holding the input endpoints and output endpoints. A
-- circuit-generating function, with fully specified parameters, can
-- be turned into an encapsulated circuit; conversely, an encapsulated
-- circuit can be turned into a circuit-generating function. Thus,
-- encapsulation and unencapsulation are the main interface for
-- passing between high- and low-level data structures.

-- | Allocate new quantum data of the given shape, in the given
-- arity. Returns the quantum data and the updated arity.
qc_alloc :: (QCData qc) => qc -> ExtArity -> (qc, ExtArity)
qc_alloc qc arity = qcdata_fold_map qc do_qubit do_bit qc arity where
  
  do_qubit :: Qubit -> ExtArity -> (Qubit, ExtArity)
  do_qubit q arity = (qubit_of_wire w, a) 
    where
      (w, a) = arity_alloc Qbit arity
  
  do_bit :: Bit -> ExtArity -> (Bit, ExtArity)
  do_bit c arity = (bit_of_wire w, a)
    where
      (w, a) = arity_alloc Cbit arity

-- | Extract an encapsulated circuit from a circuit-generating
-- function. This requires a shape parameter.
encapsulate_generic :: (QCData x) => ErrMsg -> (x -> Circ y) -> x -> (x, BCircuit, y)
encapsulate_generic e f shape = (x, circ, y) where
  (x, arity) = qc_alloc shape arity_empty
  (circ, y) = extract_simple e arity (f x)

-- | As 'encapsulate_generic', but passes the current namespace
-- into the circuit-generating function, to save recomputing
-- shared subroutines
encapsulate_generic_in_namespace :: (QCData x) => ErrMsg -> (x -> Circ y) -> x -> Circ (x, BCircuit, y)
encapsulate_generic_in_namespace e f shape = do
  let (x, arity) = qc_alloc shape arity_empty
  (circ, y) <- extract_in_current_namespace e arity (f x)
  return (x, circ, y)

-- | Turn an encapsulated circuit back into a circuit-generating
-- function.
unencapsulate_generic :: (QCData x, QCData y) => (x, BCircuit, y) -> (x -> Circ y)
unencapsulate_generic (c_in, c, c_out) input = do
  let in_bindings = qc_bind c_in input
  out_bindings <- apply_bcircuit_with_bindings c in_bindings
  let output = qc_unbind out_bindings c_out
  return output

-- $dynamic_encapsulate
-- 
-- A dynamic encapsulated circuit is to an encapsulated circuit like a
-- 'DBCircuit' to a 'BCircuit'. The output is not a static circuit,
-- but an interactive computation expressed through the 'ReadWrite'
-- monad, which can be run on a quantum device to get a static circuit
-- out.

-- | Extract an encapsulated dynamic circuit from a circuit-generating
-- function. This requires a shape parameter.
encapsulate_dynamic :: (QCData x) => (x -> Circ y) -> x -> (x, DBCircuit y)
encapsulate_dynamic f shape = (x, comp) where
  (x, arity) = qc_alloc shape arity_empty
  comp = extract_general arity (f x)

-- | Turn an encapsulated dynamic circuit back into a
-- circuit-generating function.
-- 
-- This currently fails if the dynamic circuit contains output
-- liftings, because the transformer interface has not yet been
-- updated to work with dynamic circuits.
unencapsulate_dynamic :: (QCData x, QCData y) => (x, DBCircuit y) -> (x -> Circ y)
unencapsulate_dynamic (c_in, comp) input = do
  let in_bindings = qc_bind c_in input
  (out_bindings, c_out) <- apply_dbcircuit_with_bindings comp in_bindings
  let output = qc_unbind out_bindings c_out
  return output

-- ======================================================================
-- * Generic reversing

-- | Like 'reverse_unary', but also takes a stub error message. 
reverse_errmsg :: (QCData x, QCData y) => ErrMsg -> (x -> Circ y) -> x -> (y -> Circ x)
reverse_errmsg e f shape y = do
  circuit <- encapsulate_generic_in_namespace errmsg f shape
  let circuit_inv = reverse_encapsulated circuit
      f_inv = unencapsulate_generic circuit_inv
  f_inv y
  where
    errmsg x = e ("operation not permitted in reversible circuit: " ++ x)

-- | Reverse a non-curried circuit-generating function. The second
-- parameter is a shape parameter.
reverse_unary :: (QCData x, QCData y) => (x -> Circ y) -> x -> (y -> Circ x)
reverse_unary = reverse_errmsg errmsg 
  where
    errmsg x = "reverse_unary: " ++ x

-- | Reverse a circuit-generating function. The reversed function
-- requires a shape parameter, given as the input type of the original
-- function.
-- 
-- The type of this highly overloaded function is quite difficult to
-- read.  It can have for example the following types:
-- 
-- > reverse_generic :: (QCData x, QCData y) => (x -> Circ y) -> x -> (y -> Circ x) 
-- > reverse_generic :: (QCData x, QCData y, QCData z) => (x -> y -> Circ z) -> x -> y -> (z -> Circ (x,y)) 
reverse_generic :: (QCData x, QCData y, TupleOrUnary xt x, QCurry x_y x y, Curry x_y_xt x (y -> Circ xt)) => x_y -> x_y_xt
reverse_generic f = 
  mcurry $ aux f
  where
    -- An auxiliary function for defining 'reverse_generic'.  (Inlining
    -- this causes difficulty with the type inference for 'mcurry'.)
    --aux :: (QCData x, QCData y, TupleOrUnary xt x, QCurry x_y x y) => x_y -> x -> (y -> Circ xt)
    aux f shape =
      (fmap weak_tuple) . (reverse_errmsg errmsg (quncurry f) shape)

    errmsg x = "reverse_generic: " ++ x

-- | Like 'reverse_generic', but takes functions whose output is a
-- tuple, and curries the reversed function.  Differs from
-- 'reverse_generic' in an example such as:
-- 
-- > f                         :: (x -> y -> Circ (z,w))
-- > reverse_generic f         :: x -> y -> ((z,w) -> Circ (x,y))
-- > reverse_generic_curried f :: x -> y -> (z -> w -> Circ (x,y))
-- 
-- Note: the output /must/ be a /n/-tuple, where /n/ = 0 or /n/ ≥
-- 2. Applying this to a circuit whose output is a non-tuple type is a
-- type error; in this case, 'reverse_generic' should be used.
reverse_generic_curried :: (QCData x, QCData y, TupleOrUnary xt x, Tuple yt y, QCurry x_yt x yt, QCurry y_xt y xt, Curry x_y_xt x y_xt) => x_yt -> x_y_xt
reverse_generic_curried f = 
  mcurry $ aux f
  where
    -- An auxiliary function for 'reverse_generic_curried'.  (Inlining
    -- this causes difficulty with the type inference for 'mcurry'.)
    aux :: (QCData x, QCData y, TupleOrUnary xt x, Tuple yt y, QCurry x_yt x yt, QCurry y_xt y xt) => x_yt -> x -> y_xt
    aux f = 
      (qcurry .) $ \x y -> (fmap weak_tuple) $ (reverse_errmsg errmsg $ (fmap untuple) . (quncurry f)) x y

    errmsg x = "reverse_generic_curried: " ++ x

-- | Like 'reverse_generic', but only works at simple types, and
-- therefore requires no shape parameters.  Typical type instances:
-- 
-- > reverse_simple :: (QCData_Simple x, QCData y) => (x -> Circ y) -> (y -> Circ x)
-- > reverse_simple :: (QCData_Simple x, QCData_Simple y, QCData z) => (x -> y -> Circ z) -> (z -> Circ (x,y))
reverse_simple :: (QCData_Simple x, QCData y, TupleOrUnary xt x, QCurry x_y x y) => x_y -> y -> Circ xt
reverse_simple f = (fmap weak_tuple) . (reverse_errmsg errmsg (quncurry f) fs_shape)
  where
    errmsg x = "reverse_simple: " ++ x

-- | Like 'reverse_simple', but takes functions whose output is a
-- tuple, and curries the reversed function. Typical type instance:
-- 
-- > reverse_simple_curried :: (QCData_Simple x, QCData y, QCData z) => (x -> Circ (y,z)) -> (y -> z -> Circ x)
-- 
-- Note: the output /must/ be a /n/-tuple, where /n/ = 0 or /n/ ≥
-- 2. Applying this to a circuit whose output is a non-tuple type is a
-- type error; in this case, 'reverse_generic' should be used.
reverse_simple_curried :: (QCData_Simple x, QCData y, TupleOrUnary xt x, Tuple yt y, QCurry x_yt x yt, QCurry y_xt y xt)
  => x_yt -> y_xt
reverse_simple_curried f = qcurry $ 
  (fmap weak_tuple) . (reverse_errmsg errmsg ((fmap untuple) . (quncurry f)) fs_shape)
  where
    errmsg x = "reverse_simple_curried: " ++ x

-- | Like 'reverse_generic', but specialized to endomorphic circuits,
-- i.e., circuits where the input and output have the same type (modulo
-- possibly currying) and shape. In this case, unlike 'reverse_generic',
-- no additional shape parameter is required, and the reversed function
-- is curried if the original function was.  Typical type instances:
-- 
-- > reverse_generic_endo :: (QCData x) => (x -> Circ x) -> (x -> Circ x)
-- > reverse_generic_endo :: (QCData x, QCData y) => (x -> y -> Circ (x,y)) -> (x -> y -> Circ (x,y))
reverse_generic_endo :: (QCData x, TupleOrUnary xt x, QCurry x_xt x xt) => x_xt -> x_xt
reverse_generic_endo = qcurry . ((fmap weak_tuple) .) . 
                         (\f x -> reverse_errmsg errmsg f x x)
                                       . ((fmap weak_untuple) .) . quncurry
  where
    errmsg x = "reverse_generic_endo: " ++ x

-- | Like 'reverse_generic_endo', but applies to endomorphic circuits
-- expressed in \"imperative\" style. Typical type instances:
-- 
-- > reverse_generic_endo :: (QCData x) => (x -> Circ ()) -> (x -> Circ ())
-- > reverse_generic_endo :: (QCData x, QCData y) => (x -> y -> Circ ()) -> (x -> y -> Circ ())
reverse_generic_imp :: (QCData x, QCurry x__ x ()) => x__ -> x__
reverse_generic_imp f = qcurry $ \input -> do
  reverse_generic_endo f' input
  return ()
  where
    f' x = do
      (quncurry f) x
      return x
    
-- | Conditional version of 'reverse_generic_endo'. Invert the
-- endomorphic quantum circuit if the boolean is true; otherwise,
-- insert the non-inverted circuit.
reverse_endo_if :: (QCData x, TupleOrUnary xt x, QCurry x_xt x xt) => Bool -> x_xt -> x_xt
reverse_endo_if False f = f
reverse_endo_if True f = reverse_generic_endo f

-- | Conditional version of 'reverse_generic_imp'. Invert the
-- imperative style quantum circuit if the boolean is true; otherwise,
-- insert the non-inverted circuit.
reverse_imp_if :: (QCData qa, QCurry fun qa ()) => Bool -> fun -> fun
reverse_imp_if False f = f
reverse_imp_if True f = reverse_generic_imp f

-- ======================================================================
-- * The QCurry type class

-- | The 'QCurry' type class is similar to the 'Curry' type class,
-- except that the result type is guarded by the 'Circ' monad. It
-- provides a family of type isomorphisms
-- 
-- @fun  ≅  args -> Circ res,@
-- 
-- where
-- 
-- > fun = a1 -> a2 -> ... -> an -> Circ res,
-- > args = (a1, (a2, (..., (an, ())))).
-- 
-- The benefit of having @Circ@ in the result type is that it ensures
-- that the result type is not itself a function type, and therefore
-- /fun/ has a /unique/ arity /n/. Then /args/ and /res/ are uniquely
-- determined by /fun/, which can be used to write higher-order
-- operators that consume /fun/ of any arity and \"do the right
-- thing\".
  
class QCurry fun args res | fun -> args res, args res -> fun where
  qcurry :: (args -> Circ res) -> fun
  quncurry :: fun -> (args -> Circ res)
  
instance QCurry (Circ b) () b where
  qcurry g = g ()
  quncurry x = const x

instance QCurry fun args res => QCurry (a -> fun) (a,args) res where
  qcurry g x = qcurry (\xs -> g (x,xs))
  quncurry f (x,xs) = quncurry (f x) xs

-- ======================================================================
-- * Generic circuit transformations

-- | Like 'transform_unary_shape', but also takes a stub error message.
transform_errmsg :: (QCData x, QCData y, x' ~ QCType a b x, y' ~ QCType a b y, Monad m) => ErrMsg -> Transformer m a b -> (x -> Circ y) -> x -> (x' -> m y')
transform_errmsg e transformer f shape input = do
  let (x, circuit, y) = encapsulate_generic errmsg f shape
  let in_bind = qc_bind x input
  out_bind <- transform_bcircuit_rec transformer circuit in_bind
  let output = qc_unbind out_bind y
  return output
  where
    errmsg x = e ("operation not currently permitted in transformed circuit: " ++ x)

-- | Like 'transform_generic', but applies to arbitrary transformers
-- of type
-- 
-- > Transformer m a b
-- 
-- instead of the special case
-- 
-- > Transformer Circ Qubit Bit.
-- 
-- This requires an additional shape argument. 
transform_unary_shape :: (QCData x, QCData y, x' ~ QCType a b x, y' ~ QCType a b y, Monad m) => Transformer m a b -> (x -> Circ y) -> x -> (x' -> m y')
transform_unary_shape = transform_errmsg errmsg 
  where
    errmsg x = "transform_unary_shape: " ++ x

-- | Apply the given transformer to a circuit.
transform_unary :: (QCData x, QCData y) => Transformer Circ Qubit Bit -> (x -> Circ y) -> (x -> Circ y)
transform_unary transformer f x = transform_errmsg errmsg transformer f x x
  where
    errmsg x = "transform_unary: " ++ x


-- | Like transform_unary_shape but for a dynamic transformer
transform_unary_dynamic_shape :: (QCData x, QCData y, x' ~ QCType a b x, y' ~ QCType a b y, Monad m) => DynamicTransformer m a b -> (x -> Circ y) -> x -> (x' -> m y')
transform_unary_dynamic_shape dtransformer f shape input = do
  let (x, dbcircuit) = encapsulate_dynamic f shape
  let in_bind = qc_bind x input
  (y,out_bind) <- transform_dbcircuit dtransformer dbcircuit in_bind
  let output = qc_unbind out_bind y
  return output

-- | Like transform_unary but for a dynamic transformer
transform_unary_dynamic :: (QCData x, QCData y) => DynamicTransformer Circ Qubit Bit -> (x -> Circ y) -> (x -> Circ y)
transform_unary_dynamic dtransformer f x = transform_unary_dynamic_shape dtransformer f x x


-- | Like 'transform_generic', but applies to arbitrary transformers
-- of type
-- 
-- > Transformer m a b
-- 
-- instead of the special case
-- 
-- > Transformer Circ Qubit Bit.
-- 
-- This requires an additional shape argument. 
-- 
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types:
-- 
-- > transform_generic :: (QCData x) => Transformer m a b -> Circ x -> m (QCData a b x)
-- > transform_generic :: (QCData x, QCData y) => Transformer m a b -> (x -> Circ y) -> x -> (QCData a b x -> m (QCData a b y))
-- > transform_generic :: (QCData x, QCData y, QCData z) => Transformer m a b -> (x -> y -> Circ z) -> x -> y -> (QCData a b x -> QCData a b y -> m (QCData a b z))
-- 
-- and so forth.

transform_generic_shape :: (QCData x, QCData y, QCurry qfun x y, Curry qfun' x' (m y'), Curry qfun'' x qfun', x' ~ QCType a b x, y' ~ QCType a b y, Monad m) => Transformer m a b -> qfun -> qfun''
transform_generic_shape transformer f = g where
  f1 = quncurry f
  g1 = transform_errmsg errmsg transformer f1
  g2 = \x -> mcurry (g1 x)
  g = mcurry g2
  errmsg x = "transform_generic: " ++ x

-- | Apply the given transformer to a circuit.  Unlike
-- 'transform_unary', this function can be applied to a
-- circuit-generating function in curried form with /n/ arguments, for
-- any /n/ ≥ 0.
-- 
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types:
-- 
-- > transform_generic :: (QCData x) => Transformer Circ Qubit Bit -> Circ x -> Circ x
-- > transform_generic :: (QCData x, QCData y) => Transformer Circ Qubit Bit -> (x -> Circ y) -> (x -> Circ y)
-- > transform_generic :: (QCData x, QCData y, QCData z) => Transformer Circ Qubit Bit -> (x -> y -> Circ z) -> (x -> y -> Circ z)
-- 
-- and so forth.

transform_generic :: (QCData x, QCData y, QCurry qfun x y) => Transformer Circ Qubit Bit -> qfun -> qfun
transform_generic transformer f = g where
  f1 = quncurry f
  g1 = \x -> transform_errmsg errmsg transformer f1 x x
  g = qcurry g1
  errmsg x = "transform_generic: " ++ x


-- ======================================================================
-- * Generic block structure

-- | Execute a block with local ancillas. Opens a block, initializing an ancilla with a specified classical value, and terminates it with the same value when the block closes. Note: it is the programmer's responsibility to return the ancilla to its original state at the end of the enclosed block. Usage:
-- 
-- > with_ancilla_init True $ \a -> do {
-- >   <<<code block using ancilla a initialized to True>>>
-- > }
-- 
-- > with_ancilla_init [True,False,True] $ \a -> do {
-- >   <<<code block using list of ancillas a initialized to [True,False,True]>>>
-- > }
with_ancilla_init :: (QShape a qa ca) => a -> (qa -> Circ b) -> Circ b
with_ancilla_init x f = do
  qx <- without_controls (qinit x)
  qy <- f qx
  without_controls (qterm x qx)
  return qy

-- | Like 'with_ancilla', but creates a list of /n/ ancillas, all
-- initialized to |0〉. Usage:
-- 
-- > with_ancilla_list n $ \a -> do {
-- >   <<<code block using list of ancillas a>>>
-- > }
with_ancilla_list :: Int -> (Qulist -> Circ a) -> Circ a
with_ancilla_list n f = 
  with_ancilla_init (replicate n False) f

-- | @'with_computed_fun' /x/ /f/ /g/@: computes /x' := f(x)/; then computes /g(x')/, which should be organized as a pair /(x',y)/; then uncomputes /x'/ back to /x/, and returns /(x,y)/.
-- 
-- Important subtlety in usage: all quantum data referenced in /f/, even as controls, must be explicitly bound and returned by /f/, or the reversing may rebind it incorrectly.  /g/, on the other hand, can safely refer to anything that is in scope outside the 'with_computed_fun'.
 
with_computed_fun :: (QCData x, QCData y) => x -> (x -> Circ y) -> (y -> Circ (y,b)) -> Circ (x,b)
with_computed_fun x f g = do
  y <- without_controls (f x)  
  (y,b) <- g y
  x <- without_controls (reverse_generic f x y)
  return (x,b)

-- | @'with_computed' /computation/ /code/@: performs /computation/
-- (with result /x/), then performs /code/ /x/, and finally performs
-- the reverse of /computation/, for example like this:
-- 
-- \[image with_computed.png]
-- 
-- Both /computation/ and /code/ may refer to any qubits that exist in
-- the current environment, and they may also create new
-- qubits. /computation/ may produce arbitrary garbage in addition to
-- its output. 
-- 
-- This is a very general but relatively unsafe operation. It is the
-- user's responsibility to ensure that the computation can indeed be
-- undone. In particular, if /computation/ contains any
-- initializations, then /code/ must ensure that the corresponding
-- assertions will be satisfied in /computation/[sup −1].
-- 
-- Related more specialized, but potentially safer, operations are: 
-- 
-- * 'with_basis_change', which is like 'with_computed', but assumes
-- that /computation/ is unitary, and
-- 
-- * 'classical_to_reversible', which assumes that /computation/ is
-- classical (or pseudo-classical), and /code/ is a simple
-- copy-by-controlled-not operation.

with_computed :: (QCData x) => Circ x -> (x -> Circ b) -> Circ b
with_computed computation code = do
  (bcirc, dirty, x) <- extract_in_context errmsg computation
  without_controls $ do
    unextract_in_context bcirc
  y <- with_reserve dirty $ do
    code x
  without_controls $ do
    unextract_in_context (reverse_bcircuit bcirc)
  return y
  where
    errmsg x = "with_computed: operation not permitted in pre-computation: " ++ x

-- | @'with_basis_change' /basischange/ /code/@: performs a basis change,
-- then the /code/, then the inverse of the basis change. Both
-- /basischange/ and /code/ are in imperative style. It is the user's
-- responsibility to ensure that the image of /code/ is contained in
-- the image of /basischange/, or else there will be unmet assertions
-- or runtime errors. Usage:
-- 
-- > with_basis_change basischange $ do
-- >   <<<code>>>
-- >
-- > where
-- >   basischange = do
-- >     <<<gates>>>

with_basis_change :: Circ () -> Circ b -> Circ b
with_basis_change basischange code = do
  with_computed basischange (\x -> code)

-- ======================================================================
-- * Boxed subcircuits


-- | Bind a name to a function as a subroutine in the current
-- namespace. This requires a shape argument, as well as complete
-- parameters, so that it is uniquely determined which actual circuit
-- will be the subroutine. It is an error to call that subroutine
-- later with a different shape argument. It is therefore the user's
-- responsibility to ensure that the name is unique to the subroutine,
-- parameters, and shape. 
--
-- This function does nothing if the name
-- already exists in the namespace; in particular, it does /not/ check
-- whether the given function is equal to the stored subroutine. 
provide_subroutine_generic :: (QCData x, QCData y) => ErrMsg -> BoxId -> Bool -> (x -> Circ y) -> x -> Circ ()
provide_subroutine_generic e name is_classically_controllable f shape = do
  main_state <- get_namespace
  if (Map.member name main_state)
  then return ()
  else do
    (x, bcircuit, y) <- encapsulate_generic_in_namespace errmsg f shape

    -- The 'y' element only corresponds to the output type of the box,
    -- not the complete list of wires outputted by the circuit. This
    -- information is gathered and stored in forgotten_output_qcdata
    -- as ([Qubit],[Bit]).
    let ((_,_,aout,_),_) = bcircuit
        forgotten_output_arity  = strip_qcdata_from_arity y aout
        forgotten_output_qcdata = extract_from_arity forgotten_output_arity

    let ein = endpoints_of_qcdata x
        eout = endpoints_of_qcdata (y,forgotten_output_qcdata)
        win = map wire_of_endpoint ein
        wout = map wire_of_endpoint eout

        input_destructure = wires_with_arity_of_endpoints . endpoints_of_qcdata
        input_structure = (\(ws,a) -> qcdata_of_endpoints x $ endpoints_of_wires_in_arity a ws)

        input_CircTypeStructure = CircuitTypeStructure input_destructure input_structure 

        output_destructure = wires_with_arity_of_endpoints . endpoints_of_qcdata
        output_structure = (\(ws,a) -> qcdata_of_endpoints (y,forgotten_output_qcdata) $ endpoints_of_wires_in_arity a ws)

        output_CircTypeStructure = CircuitTypeStructure output_destructure output_structure 

    provide_subroutine name (ob_circuit win bcircuit wout) input_CircTypeStructure output_CircTypeStructure is_classically_controllable
    where
      errmsg x = e ("operation not permitted in boxed subroutine: " ++ x)

      -- Make a 'QCData' out of an arity.
      extract_from_arity :: Arity -> ([Qubit],[Bit])
      extract_from_arity x =
        fst $ IntMap.mapAccumWithKey record_wire ([],[]) x
        where
          record_wire :: ([Qubit],[Bit]) -> Int -> Wiretype -> (([Qubit],[Bit]),Wiretype)
          record_wire (qs,bs) wire Qbit = (((qubit_of_wire wire):qs,bs), Qbit)
          record_wire (qs,bs) wire Cbit = ((qs,(bit_of_wire wire):bs), Cbit)

      -- Take a 'QCData' /x/ and an 'Arity' /a/ and remove all the wires
      -- of /a/ that are already existing in /x/.
      strip_qcdata_from_arity :: (QCData x) => x -> Arity -> Arity
      strip_qcdata_from_arity x a =
        snd $ State.runState (qcdata_mapM x delete_qubit delete_bit x) a
        where
          
          delete_qubit :: Qubit -> State.State Arity ()
          delete_qubit q = do
            s <- State.get
            State.put $ flip IntMap.delete s $ wire_of_qubit q
          
          delete_bit :: Bit -> State.State Arity ()
          delete_bit b = do
            s <- State.get
            State.put $ flip IntMap.delete s $ wire_of_bit b






-- | A generic interface for wrapping a circuit-generating function
-- into a boxed and named subroutine. This takes a name and a
-- circuit-generating function, and returns a new circuit-generating
-- function of the same type, but which inserts a boxed subroutine
-- instead of the actual body of the subroutine.
-- 
-- It is intended to be used like this:
-- 
-- > somefunc :: Qubit -> Circ Qubit
-- > somefunc a = do ...
-- > 
-- > somefunc_boxed :: Qubit -> Circ Qubit
-- > somefunc_boxed = box "somefunc" somefunc
-- 
-- Here, the type of @somefunc@ is just an example; this could indeed
-- be a function with any number and type of arguments, as long as the
-- arguments and return type are quantum data.
-- 
-- It is also possible to inline the 'box' operator directly, in which
-- case it should be done like this:
-- 
-- > somefunc :: Qubit -> Circ Qubit
-- > somefunc = box "somefunc" $ \a -> do ...
-- 
-- Note: The 'box' operator wraps around a complete function,
-- including all of its arguments. It would be incorrect to apply the
-- 'box' operator after some quantum variables have already been
-- defined. Thus, the following is incorrect:
-- 
-- > incorrect_somefunc :: Qubit -> Circ Qubit
-- > incorrect_somefunc a = box "somefunc" $ do ...
-- 
-- It is the user's responsibility not to use the same name for
-- different subroutines. If 'box' is called more than once with the
-- same name and shape of input, Quipper assumes, without checking,
-- that they are subsequent calls to the same subroutine. 
-- 
-- The type of the 'box' operator is overloaded and quite difficult to
-- read.  It can have for example the following types:
-- 
-- > box :: String -> (Qubit -> Circ Qubit) -> (Qubit -> Circ Qubit)
-- > box :: String -> (QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt)) -> (QDInt -> QDInt -> Circ (QDInt,QDInt,QDInt))
box :: (QCData qa, QCData qb, QCurry qa_qb qa qb)
    => String -> qa_qb -> qa_qb
box n = qcurry . (box_internal err n $ RepeatFlag 1) . quncurry
  where
    err e = "box: " ++ e

-- | A version of 'box' with iteration. The second argument is an
-- iteration count.
-- 
-- This can only be applied to functions of a single argument, where
-- the input and output types are the same.
nbox :: (QCData qa) => String -> Integer -> (qa -> Circ qa) -> qa -> Circ qa
nbox n rep = qcurry . (box_internal err n (RepeatFlag rep)) . quncurry
  where
    err e = "nbox: " ++ e

-- | A version of 'nbox' with same type as 'loopM'.
box_loopM :: (Integral int, QCData qa)
    => String -> int -> qa -> (qa -> Circ qa) -> Circ qa
box_loopM n rep = flip (nbox  n $ fromIntegral rep)

-- | A version of 'loopM' that will be boxed conditionally on a
-- boolean condition. Typical usage:
-- 
-- > loopM_boxed_if (s > 1) "name" s x $ \x -> do
-- >   <<<body>>>
-- >   return x
loopM_boxed_if :: (Integral int, QCData qa) => Bool -> String -> int -> qa -> (qa -> Circ qa) -> Circ qa
loopM_boxed_if True name = box_loopM name
loopM_boxed_if False name = loopM

-- | The underlying implementation of 'box' and 'nbox'. It behaves
-- like 'box', but is restricted to unary functions, and takes an
-- 'ErrMsg' argument.
box_internal :: (QCData qa, QCData qb)
             => ErrMsg -> String -> RepeatFlag -> (qa -> Circ qb) -> (qa -> Circ qb)
box_internal e n r f x = do
  let boxid = BoxId n (canonical_shape x)
  provide_subroutine_generic e boxid False f x -- By default, fall back on the general controlling scheme: 
                                               -- set the classical-control flag to False.
  call_subroutine boxid r x


-- | Classical control on a function with same shape of input and
-- output: if the control bit is true the function is fired, otherwise
-- the identity map is used.
-- Note: the constraint on the types is dynamically checked.
with_classical_control :: QCData qa => Bit -> String -> qa -> (qa -> Circ qa) -> Circ qa
with_classical_control c n x f = do
  let boxid = BoxId n (canonical_shape x)
  provide_subroutine_generic err boxid True f x
  call_subroutine boxid (RepeatFlag 1) x `controlled` c
 where
  err e = "with_classical_control: " ++ e

-- | Like 'call_subroutine', except inline the subroutine body from
-- the given namespace, instead of inserting a subroutine call.
-- 
-- Implementation note: this currently copies /all/ subroutine
-- definitions from the given namespace into the current namespace,
-- and not just the ones used by the current subroutine.
-- 
-- Implementation note: this currently only works on lists of endpoints.
inline_subroutine :: BoxId -> Namespace -> [Endpoint] -> Circ [Endpoint]
inline_subroutine name ns inputs = do
  let mc = Map.lookup name ns
  case mc of 
    Nothing -> 
      error ("inline_subroutine: subroutine " ++ show name ++ " does not exist in the given namespace: " ++ showNames ns)
    Just (TypedSubroutine ocircuit _ _ scf) -> do
      let OCircuit (win, circuit, wout) = ocircuit
      provide_subroutines ns
      when (length win /= length inputs) $ do
        error ("inline_subroutine: subroutine " ++ show name ++ " has been applied to incorrect size of QCData")
      let in_bind = bind_list win inputs bindings_empty
      out_bind <- apply_circuit_with_bindings circuit in_bind
      let outputs = unbind_list out_bind wout
      return outputs
