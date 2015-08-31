-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This is the main export module for Quipper, collecting everything
-- that Quipper applications need. This is Quipper's \"public\"
-- interface.

module Quipper (
  -- * The Circ monad  
  Circ(..),
  
  -- * Basic types
  Qubit,
  Bit,
  Qulist,
  Bitlist,
  
  -- * Basic gates
  -- $BASIC
  Timestep,
  
  -- $FUNCTIONAL_ANCHOR
  
  -- ** Reversible gates in functional style
  -- $FUNCTIONAL
  qnot,
  hadamard,
  gate_H,
  gate_X,
  gate_Y,
  gate_Z,
  gate_S,
  gate_S_inv,
  gate_T,
  gate_T_inv,
  gate_E,
  gate_E_inv,
  gate_omega,
  gate_V,
  gate_V_inv,
  expZt,
  rGate,
  gate_W,
  gate_iX,
  gate_iX_inv,
  global_phase,
  global_phase_anchored,
  qmultinot,
  cnot,
  swap,
  
  -- $IMPERATIVE_ANCHOR
  
  -- ** Reversible gates in imperative style 
  -- $IMPERATIVE 
  qnot_at,
  hadamard_at,
  gate_H_at,
  gate_X_at,
  gate_Y_at,
  gate_Z_at,
  gate_S_at,
  gate_S_inv_at,
  gate_T_at,
  gate_T_inv_at,
  gate_E_at,
  gate_E_inv_at,
  gate_omega_at,
  gate_V_at,
  gate_V_inv_at,
  expZt_at,
  rGate_at,
  gate_W_at,
  gate_iX_at,
  gate_iX_inv_at,
  qmultinot_at,
  cnot_at,
  swap_at,
  
  -- ** Gates for state preparation and termination
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
  measure,
  prepare,
  qc_measure,
  qc_prepare,
  
  -- ** Gates for classical circuits
  -- $CLASSICAL
  cgate_xor,  
  cgate_eq,
  cgate_not,
  cgate_and,
  cgate_or,
  cgate_if,
  circ_if,
  
  -- ** User-defined gates
  named_gate,
  named_gate_at,
  named_rotation,
  named_rotation_at,
  extended_named_gate,
  extended_named_gate_at,
  
  -- ** Dynamic lifting
  dynamic_lift,
  
  -- * Other circuit-building functions
  qinit_plusminus,
  qinit_of_char,
  qinit_of_string,
  map_hadamard,
  map_hadamard_at,
  controlled_not,
  controlled_not_at,
  bool_controlled_not,
  bool_controlled_not_at,
  qc_copy,
  qc_uncopy,
  qc_copy_fun,
  qc_uncopy_fun,
  mapUnary,
  mapBinary,
  mapBinary_c,
  qc_mapBinary,
  
  -- * Notation for controls
  -- $CONTROLS
  ControlSource(..),
  ControlList,
  (.&&.), 
  (.==.), 
  (./=.),
  controlled,
  
  -- * Signed items
  Signed(..),
  from_signed,
  get_sign,
  
  -- * Comments and labelling
  comment,
  label,
  comment_with_label,
  without_comments,
  Labelable,
  
  -- * Hierarchical circuits
  box,
  nbox,
  box_loopM,
  loopM_boxed_if,

  -- * Block structure
  -- $BLOCK
  
  -- ** Ancillas
  -- $WITHANCILLA
  with_ancilla,
  with_ancilla_list,
  with_ancilla_init,
  -- ** Automatic uncomputing
  with_computed_fun,
  with_computed,
  with_basis_change,
  -- ** Controls
  with_controls,
  with_classical_control,
  without_controls,
  without_controls_if,
  -- ** Loops
  for,
  endfor,
  foreach,
  loop,
  loop_with_index,
  loopM,
  loop_with_indexM,
  
  -- * Operations on circuits
  -- ** Reversing
  reverse_generic,
  reverse_simple,
  reverse_generic_endo,
  reverse_generic_imp,
  reverse_generic_curried,
  reverse_simple_curried,
  reverse_endo_if,
  reverse_imp_if,
  
  -- ** Printing
  Format (..),
  FormatStyle(..),
  format_enum,
  print_unary,
  print_generic,
  print_simple,
  print_of_document,
  print_of_document_custom,
  
  -- ** Classical circuits  
  classical_to_cnot,
  classical_to_quantum,
  -- ** Ancilla uncomputation
  classical_to_reversible,
  
  -- * Circuit transformers
  -- $TRANSFORMATION
  
  -- ** User-definable transformers
  Transformer,
  T_Gate(..),
  -- ** Pre-defined transformers
  identity_transformer,
  -- ** An example transformer
  -- $TRANSEXAMPLE
  
  -- ** Applying transformers to circuits
  transform_generic,
  transform_generic_shape,
  
  -- ** Auxiliary type definitions
  InverseFlag,
  NoControlFlag,
  B_Endpoint(..),
  Endpoint,
  Ctrls,  

  -- * Automatic circuit generation from classical code
  -- $TEMPLATE
  module Quipper.CircLifting,
  module Libraries.Template,

  -- * Extended quantum data types
  -- ** Homogeneous quantum data types
  QShape,
  QData,
  CData,
  BData,
  
  -- ** Heterogeneous quantum data types
  QCData,
  QCDataPlus,
  
  -- ** Shape-related operations
  -- $SHAPE
  bit,
  qubit,
  qshape,
  qc_false,
  
  -- ** Quantum type classes
  -- $QCLASSES
  QEq (..),
  QOrd (..),
  q_lt,
  q_gt,
  q_le,
  q_ge,
  
  ) where


import Quipper.Monad
import Quipper.Generic
import Quipper.QData
import Quipper.QClasses
import Quipper.Control
import Quipper.CircLifting
import Quipper.Transformer (T_Gate(..), Transformer, Ctrls, B_Endpoint(..))
import Quipper.Circuit (InverseFlag, NoControlFlag, from_signed, get_sign)
import Quipper.Classical
import Quipper.Printing
import Quipper.Labels

import Libraries.Template
import Libraries.Auxiliary

-- $BASIC
-- 
-- This section contains various elementary gates that can be used as
-- building blocks for constructing circuits.

-- $FUNCTIONAL_ANCHOR #FUNCTIONAL#

-- $FUNCTIONAL
-- 
-- The gates in this section are in \"functional\" style, which means
-- that they return something. For example, the 'qnot' gate consumes a
-- 'Qubit', performs an operation, and outputs a new 'Qubit'. The
-- gates should be used like this:
-- 
-- > output <- qnot input
-- 
-- or, for a binary gate:
-- 
-- > (out0, out1) <- gate_W in0 in1
-- 
-- For each of these gates, we also provide a version in imperative
-- style, see <#IMPERATIVE Reversible gates in imperative style> below.

-- $IMPERATIVE_ANCHOR #IMPERATIVE#

-- $IMPERATIVE
-- 
-- The gates in this section are in \"imperative\" style, which means
-- that they operate on a qubit \"in place\" and do not return
-- anything. The gates should be used like this:
-- 
-- > qnot_at q
-- 
-- or, for a binary gate:
-- 
-- > gate_W_at q0 q1
-- 
-- For each of these gates, we also provide a version in functional
-- style, see <#FUNCTIONAL Reversible gates in functional style> above.

-- * Snippets of additional documentation lifted from import modules:

-- $CLASSICAL
--
-- The gates in this section are for constructing classical circuits. 
-- None of these gates alter or discard their inputs; each gate produces 
-- a new wire holding the output of the gate.

-- $CONTROLS
-- 
-- Some gates can be controlled by a condition involving one of more
-- \"control\" qubits and/or classical bits at circuit execution time.
-- Such gates can also be controlled by boolean conditions that are
-- known at circuit generation time (in which case the gate will not
-- be generated when the control condition is false). This section
-- provides a convenient and flexible syntax for specifying controls.
-- 
-- In Quipper, controls can be written in a way that is
-- reminiscent of (a restricted set of) ordinary boolean
-- expressions. Here are some examples:
-- 
-- > q1 .==. 0 .&&. q2 .==. 1   for Qubits q1, q2
-- 
-- > q .&&. p                   means  q .==. 1  .&&.  p .==. 1
-- 
-- > qx .==. 5                  for a QDInt qx
-- 
-- > q1 .==. 0 .&&. z <= 7      combines quantum and classical controls
-- 
-- > q ./=. b                   the negation of q .==. b;
-- >                            here b is a boolean.
-- 
-- > [p,q,r,s]                  a list of positive controls
-- 
-- > [(p, True), (q, False), (r, False), (s, True)]
-- >                            a list of positive and negative controls
--
-- Among these infix operators, @(.&&.)@ binds more weakly than
-- @(.==.)@, @(./=.)@.
-- 
-- Controls can be attached to a gate by means of the infix
-- operator 'controlled':
-- 
-- > gate `controlled` <<controls>>   

-- $BLOCK
-- 
-- The following are higher-order functions that provide a way to
-- structure quantum programs into blocks. A block can contain local
-- ancillas or local controls.

-- $WITHANCILLA The use of the 'with_ancilla' family of operators is
-- preferable to using 'qinit' and 'qterm' directly. In particular, it
-- is possible to add controls to a block created with one of the
-- 'with_ancilla' family of operators, whereas 'qinit' and 'qterm',
-- when used individually, cannot be controlled.

-- $TEMPLATE
-- 
-- The following two modules provide functions that are useful for
-- automatic circuit generation from classical code. Please see
-- "Quipper.CircLifting" for a more detailed explanation of how to use
-- this feature.

-- $TRANSFORMATION
-- 
-- Transformers are a very general way of defining mappings over
-- circuits. Possible uses of this include:
-- 
-- * gate transformations, where a whole circuit is transformed by
-- replacing each kind of gate with another gate or circuit;
-- 
-- * error correcting codes, where a whole circuit is transformed
-- replacing each qubit by some fixed number of qubits, and each gate
-- by a circuit; and
-- 
-- * simulations, where a whole circuit is mapped to a semantic
-- function by specifying a semantic function for each gate.
-- 
-- The interface is designed to allow the programmer to specify new
-- transformers easily. To define a specific transformation, the
-- programmer has to specify only three pieces of information:
-- 
-- * Types /a/=⟦Qubit⟧ and /b/=⟦Bit⟧, to serve as semantic domains.
-- 
-- * A monad /m/. This is to allow translations to have side effects
-- if desired; one can use the identity monad otherwise.
-- 
-- * For every gate /G/, a corresponding semantic function ⟦/G/⟧.  The
-- type of this function depends on what kind of gate /G/ is. For example:
-- 
-- @
-- If /G/ :: Qubit -> Circ Qubit, then ⟦/G/⟧ :: /a/ -> /m/ /a/. 
-- If /G/ :: (Qubit, Bit) -> Circ (Bit, Bit), then ⟦/G/⟧ :: (/a/, /b/) -> /m/ (/b/, /b/).
-- @ 
-- 
-- The programmer provides this information by defining a function of
-- type 'Transformer' /m/ /a/ /b/, see below. Once a
-- particular transformer has been defined, it can then be applied to
-- entire circuits. For example, for a circuit with 1 inputs and 2
-- outputs:
-- 
-- @
-- If /C/ :: Qubit -> (Qubit, Qubit), then ⟦/C/⟧ :: /a/ -> /m/ (/a/, /a/).
-- @

-- $TRANSEXAMPLE
-- 
-- The following is a short but complete example of how to write and
-- use a simple transformer. As usual, we start by importing Quipper:
-- 
-- > import Quipper
-- 
-- We will write a transformer called @sample_transformer@, which maps
-- every swap gate to a sequence of three controlled-not gates, and
-- leaves all other gates unchanged. For convenience, Quipper
-- pre-defines an 'identity_transformer', which can be used as a
-- catch-all clause to take care of all the gates that don't need to
-- be rewritten.
-- 
-- > mytransformer :: Transformer Circ Qubit Bit
-- > mytransformer (T_QGate "swap" 2 0 _ ncf f) = f $
-- >   \[q0, q1] [] ctrls -> do
-- >     without_controls_if ncf $ do
-- >       with_controls ctrls $ do
-- >         qnot_at q0 `controlled` q1
-- >         qnot_at q1 `controlled` q0
-- >         qnot_at q0 `controlled` q1
-- >         return ([q0, q1], [], ctrls)
-- > mytransformer g = identity_transformer g
-- 
-- Note how Quipper syntax has been used to define the replacement
-- circuit @new_swap@, consisting of three controlled-not gates. Also,
-- since the original swap gate may have been controlled, we have
-- added the additional controls with a 'with_controls'
-- operator. Finally, the 'without_controls_if' operator ensures that
-- if the 'NoControlFlag' is set on the original swap gate, then it
-- will also be set on the replacement circuit.
-- 
-- To try this out, we define some random circuit using swap gates:
-- 
-- > mycirc a b c d = do
-- >   swap_at a b
-- >   hadamard_at b
-- >   swap_at b c `controlled` [a, d]
-- >   hadamard_at c
-- >   swap_at c d
-- 
-- To apply the transformer to this circuit, we use the generic
-- operator 'transform_generic':
-- 
-- > mycirc2 = transform_generic mytransformer mycirc
--
-- Finally, we use a @main@ function to display the original circuit
-- and then the transformed one:
--
-- > main = do
-- >   print_simple Preview mycirc
-- >   print_simple Preview mycirc2

-- $QCLASSES
--
-- Haskell provides many convenient type classes: 'Eq', 'Ord', 'Num', etc.
-- Quipper provides quantum analogues of some of these.
-- For instance, Haskell’s @'Eq' a@ has the method
-- 
-- > (==) :: a -> a -> Bool.  
-- 
-- Correspondingly, our @'QEq' a qa ca@ has a method
-- 
-- > q_is_equal :: qa -> qa -> Circ (qa,qa,Qubit).  
-- 
-- Similarly, where Haskell’s 'Num' class has methods '+', '*', 'signum',
-- the class 'QNum' has 'q_add', 'q_mult', 'q_signum', and so on.  
-- ('QNum' is defined in "QuipperLib.Arith".)
--
-- All quantum type classes assume (a) that their instance types are
-- 'QCData', and (b) that the corresponding classical parameter types
-- are instances of the corresponding Haskell type classes.
-- 
-- Quantum type classes are designed to work well with the automatic
-- circuit generation of "Quipper.CircLifting": the methods of
-- Haskell’s standard type classes are translated into their quantum
-- analogues, where available.

-- $SHAPE Some Quipper functions, such as 'print_generic', require a
-- /shape parameter/. A shape parameter is a parameter passed to a
-- function for the sole purpose of specifying the type or size of
-- some data structure, without actually specifying any data.
-- Example: given a circuit
-- 
-- > circuit :: ([Qubit], Bit) -> Circ Qubit,
-- 
-- the command
-- 
-- > print_generic Preview circuit ([qubit,qubit,qubit], bit)
-- 
-- tells Quipper to preview the circuit for a problem size of 3 qubits
-- and 1 bit.
