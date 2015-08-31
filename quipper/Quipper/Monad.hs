-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables  #-}

-- | This module provides a high-level circuit building interface
-- intended to look \"functional\". At a given time, there is a
-- circuit being assembled. This circuit has free endpoints (on the
-- left and right) that can be bound to variables. A qubit or bit is
-- simply an endpoint in such a circuit. \"Applying\" an operation to
-- a qubit or bit simply appends the operation to the current
-- circuit. We use the 'Circ' monad to capture the side effect of
-- assembling a circuit.

module Quipper.Monad (
  -- * The ReadWrite monad
  ReadWrite(..),
  
  -- * The Circ monad  
  Circ,

  -- * Some types
  Qubit,
  Bit,
  Endpoint,
  Signed(..), -- re-exported from Quipper.Circuit
  Ctrl,
  Qulist,
  Bitlist,
  Timestep,   -- re-exported from Quipper.Circuit
  InverseFlag, -- re-exported from Quipper.Circuit
  
  -- * Conversions for wires, qubits, bits, endpoints
  wire_of_qubit,
  wire_of_bit,
  wire_of_endpoint,  
  wires_with_arity_of_endpoints,
  qubit_of_wire,
  bit_of_wire,
  endpoint_of_wire,
  endpoints_of_wires_in_arity,

  -- * Bindings for qubits and bits
  bind_qubit,
  bind_bit,
  unbind_qubit,
  unbind_bit,
  
  -- * Controls for qubits and bits
  clist_add_qubit,
  clist_add_bit,
  
  -- * Namespace management  
  provide_simple_subroutine,
  provide_subroutine,
  provide_subroutines,
  call_subroutine,
  get_namespace,
  set_namespace,

  put_subroutine_definition,
  
  -- * Basic gates
  -- ** Gates in functional style
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
  swap_qubit,
  expZt,
  rGate,
  gate_W,
  gate_iX,
  gate_iX_inv,
  global_phase,
  global_phase_anchored_list,
  qmultinot_list,
  cmultinot_list,
  named_gate_qulist,
  named_rotation_qulist,
  cnot,
  swap_bit,
  -- ** Gates in imperative style
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
  swap_qubit_at,
  expZt_at,
  rGate_at,
  gate_W_at,
  gate_iX_at,
  gate_iX_inv_at,
  qmultinot_list_at,
  cmultinot_list_at,
  named_gate_qulist_at,
  named_rotation_qulist_at,
  cnot_at,
  swap_bit_at,
  -- ** Bitwise initialization and termination functions
  qinit_qubit,
  qterm_qubit,
  qdiscard_qubit,
  prepare_qubit,
  unprepare_qubit,
  measure_qubit,
  cinit_bit,
  cterm_bit,
  cdiscard_bit,
  dterm_bit,
  
  -- ** Classical gates
  -- $CLASSICAL
  cgate_xor,
  cgate_eq,
  cgate_if_bit,
  cgate_not,
  cgate_and,
  cgate_or,
  cgate,
  cgateinv,
  
  -- ** Subroutines
  subroutine,
  
  -- ** Comments
  comment_label,
  without_comments,
  
  -- ** Dynamic lifting
  dynamic_lift_bit,
  
  -- * Other circuit-building functions
  qinit_plusminus,
  qinit_of_char,
  qinit_of_string,
  qinit_list,
  qterm_list,
  cinit_list,
  
  -- * Higher-order functions
  with_ancilla,
  with_controls,
  controlled,
  without_controls,
  without_controls_if,
  
  -- ** Deprecated special cases
  qinit_qubit_ancilla,
  qterm_qubit_ancilla,
  
  -- * Circuit transformers
  identity_transformer,
  identity_dynamic_transformer,
  apply_circuit_with_bindings,
  apply_bcircuit_with_bindings,
  apply_dbcircuit_with_bindings,
  
  -- * Encapsulated circuits
  extract_simple,
  extract_general,
  extract_in_context,
  extract_in_current_namespace,
  unextract_in_context,
  reverse_encapsulated,
  with_reserve
) where

-- import other Quipper stuff
import Quipper.Circuit
import Libraries.Auxiliary
import Quipper.Transformer
import Quipper.Control

-- import other stuff
import Control.Monad
import Data.Typeable

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)

-- ======================================================================
-- * The Circ monad

-- ----------------------------------------------------------------------
-- ** States

-- | A flag to indicate whether comments are disabled ('True') or
-- enabled ('False').
type NoCommentFlag = Bool

-- | Holds the state during circuit construction. Currently this has
-- four components: the output arity of the circuit currently being
-- assembled, the current 'Namespace', the currently active
-- 'ControlList' and 'NoControlFlag', and a flag to determine whether
-- comments are disabled. All gates that are appended will have the
-- controls from the 'ControlList' added to them.
data State = State {
  arity :: !ExtArity,
  namespace :: !Namespace,
  clist :: !ControlList,
  ncflag :: !NoControlFlag,
  nocommentflag :: !NoCommentFlag
}

-- | Return a completely empty state, suitable to be the starting
-- state for circuit construction.
empty_state :: State
empty_state = State { 
  arity = arity_empty, 
  namespace = namespace_empty,
  clist = clist_empty,
  ncflag = False,
  nocommentflag = False
  }

-- | Prepare an initial state from the given extended arity.
initial_state :: ExtArity -> State
initial_state arity = empty_state { arity = arity }

-- ----------------------------------------------------------------------
-- ** Definition of Circ

-- $ The 'Circ' monad is a 'ReadWrite' monad, wrapped with an
-- additional state.

-- | The 'Circ' monad encapsulates the type of quantum operations. For
-- example, a quantum operation that inputs two 'Qubit's and outputs a
-- 'Qubit' and a 'Bit' has the following type:
-- 
-- > (Qubit, Qubit) -> Circ (Qubit, Bit)

-- Implementation note: we could have equivalently defined 'Circ'
-- using Haskell's 'StateT' monad transformer, like this:
-- 
-- > Circ = StateT State ReadWrite. 
-- 
-- But it seems clearer, and certainly more self-contained, to write
-- out the monad laws explicitly. Moreover, 'Circ' will probably look
-- better in error messages than 'StateT' 'State' 'ReadWrite'.

newtype Circ a = Circ { getCirc :: State -> ReadWrite (a, State) }

instance Monad Circ where
  return a = Circ (\s -> return (a, s))
  f >>= g = Circ h
    where
      h s0 = do
        (a, s1) <- getCirc f s0
        getCirc (g a) s1

-- every monad is applicative, and so is this one
instance Applicative Circ where
  pure = return
  (<*>) = ap

-- every monad is a functor, and so is this one
instance Functor Circ where
  fmap = liftM

-- ======================================================================
-- ** Monad access primitives
  
-- $ Developer note: the 5 functions in this section are the /only/
-- operations that are permitted to access the monad internals (i.e.,
-- 'Circ' and 'getCirc') directly.

-- | Get the 'Circ' monad's state.
get_state :: Circ State
get_state = Circ $ \s -> return (s, s)

-- | Set the 'Circ' monad's state.
set_state :: State -> Circ ()
set_state s = Circ $ \t -> return ((), s)

-- | Pass a gate to the 'Circ' monad. Note that this is a low-level
-- monad access function, and does not update other parts of the
-- monad's data. For a higher-level function, see 'apply_gate'.
put_gate :: Gate -> Circ ()
put_gate g = Circ $ \s -> RW_Write g (return ((), s))

-- | Issue a prompt and receive a reply.
do_read :: Wire -> Circ Bool
do_read w = Circ $ \s -> RW_Read w (\bool -> return (bool, s))

-- | Issue a RW_Subroutine primitive
put_subroutine_definition :: BoxId -> TypedSubroutine -> Circ ()
put_subroutine_definition name subroutine = Circ $ \s -> RW_Subroutine name subroutine (return ((), s))

-- | This is the universal \"run\" function for the 'Circ' monad.  It
-- takes as parameters a 'Circ' computation, and an initial state. It
-- outputs 'ReadWrite' computation for the result of the 'Circ'
-- computation and the final state.
run_circ :: Circ a -> State -> ReadWrite (a, State)
run_circ = getCirc

-- ----------------------------------------------------------------------
-- ** Low-level state manipulation
  
-- $ The functions in this section are the /only/ operations that are
-- permitted to operate on states directly (i.e., to use 'get_state'
-- and 'set_state'). All other code in this module should access the
-- state using these abstractions. Code in other modules can't access
-- the state at all, but should use exported functions (and preferably
-- 'QShape.encapsulate_generic') when it is necessary to extract
-- low-level circuits.

-- | Get the 'arity' part of the 'Circ' monad's state.
get_arity :: Circ ExtArity
get_arity = do
  s <- get_state
  return (arity s)

-- | Set the 'arity' part of the 'Circ' monad's state.
set_arity :: ExtArity -> Circ ()
set_arity arity = do
  s <- get_state
  set_state s { arity = arity }
  
-- | Get the 'namespace' part of the 'Circ' monad's state.
get_namespace :: Circ Namespace
get_namespace = do
  s <- get_state
  return (namespace s)
  
-- | Set the 'namespace' part of the 'Circ' monad's state.
set_namespace :: Namespace -> Circ ()
set_namespace namespace = do
  s <- get_state
  set_state s { namespace = namespace }
  
-- | Get the 'clist' part of the 'Circ' monad's state.
get_clist :: Circ ControlList
get_clist = do
  s <- get_state
  return (clist s)
  
-- | Set the 'clist' part of the 'Circ' monad's state.
set_clist :: ControlList -> Circ ()
set_clist clist = do
  s <- get_state
  set_state s { clist = clist }

-- | Get the 'ncflag' part of the 'Circ' monad's state.
get_ncflag :: Circ NoControlFlag
get_ncflag = do
  s <- get_state
  return (ncflag s)
  
-- | Set the 'ncflag' part of the 'Circ' monad's state.
set_ncflag :: NoControlFlag -> Circ ()
set_ncflag ncflag = do
  s <- get_state
  set_state s { ncflag = ncflag }

-- | Get the 'nocommentflag' part of the 'Circ' monad's state.
get_nocommentflag :: Circ NoCommentFlag
get_nocommentflag = do
  s <- get_state
  return (nocommentflag s)
  
-- | Set the 'nocommentflag' part of the 'Circ' monad's state.
set_nocommentflag :: NoCommentFlag -> Circ ()
set_nocommentflag nocommentflag = do
  s <- get_state
  set_state s { nocommentflag = nocommentflag }

-- ----------------------------------------------------------------------
-- ** Circuit extraction

-- | Extract a circuit from a monadic term, starting from the given
-- arity. This is the \"simple\" extract function, which does not
-- allow dynamic lifting. The 'ErrMsg' argument is a stub error message
-- to be used in case an illegal operation is encountered. 
extract_simple :: ErrMsg -> ExtArity -> Circ a -> (BCircuit, a)
extract_simple e arity f = (bcirc, y) where
  comp = extract_general arity f
  (bcirc, y) = bcircuit_of_static_dbcircuit e comp


-- | Run a monadic term in the initial arity, and extract a dynamic
-- boxed circuit.
extract_general :: ExtArity -> Circ a -> DBCircuit a
extract_general arity_in f = (a0, mmap finalize comp) where
  a0 = arity_of_extarity arity_in
  s0 = initial_state arity_in
  comp = run_circ f s0
  finalize (a, s1) = (a1, n, a) where
    arity_out = arity s1
    a1 = arity_of_extarity arity_out
    n = n_of_extarity arity_out    

-- ======================================================================
-- * Some types

-- | The type of qubits.
newtype Qubit = QubitWire Wire
              deriving (Show, Eq, Ord, Typeable)

-- | The type of run-time classical bits (i.e., boolean wires in a
-- circuit).
newtype Bit = BitWire Wire
              deriving (Show, Eq, Ord, Typeable)

-- | An endpoint in a circuit. This is either a 'Qubit' or a 'Bit'.
type Endpoint = B_Endpoint Qubit Bit

-- | A control consists of an 'Endpoint' and a boolean ('True' =
-- perform gate when control wire is 1; 'False' = perform gate when
-- control wire is 0). Note that gates can be controlled by qubits and
-- classical bits.
type Ctrl = Signed Endpoint

-- | Synonym for a qubit list, for convenience.
type Qulist = [Qubit]

-- | Synonym for a bit list, for convenience.
type Bitlist = [Bit]

-- ----------------------------------------------------------------------
-- * Conversions for wires, qubits, bits, endpoints

-- | Extract the underlying low-level wire of a qubit.
wire_of_qubit :: Qubit -> Wire
wire_of_qubit (QubitWire w) = w

-- | Extract the underlying low-level wire of a bit.
wire_of_bit :: Bit -> Wire
wire_of_bit (BitWire w) = w

-- | Construct a qubit from a wire.
qubit_of_wire :: Wire -> Qubit
qubit_of_wire w = QubitWire w

-- | Construct a bit from a wire.
bit_of_wire :: Wire -> Bit
bit_of_wire w = BitWire w

-- | Extract the underlying low-level 'Wire' of an 'Endpoint'.
wire_of_endpoint :: Endpoint -> Wire
wire_of_endpoint (Endpoint_Qubit q) = wire_of_qubit q
wire_of_endpoint (Endpoint_Bit b) = wire_of_bit b

-- | Extract the underlying low-level 'Wiretype' of an 'Endpoint'.
wiretype_of_endpoint :: Endpoint -> Wiretype
wiretype_of_endpoint (Endpoint_Qubit _) = Qbit
wiretype_of_endpoint (Endpoint_Bit _) = Cbit

-- | Break a list of 'Endpoint's down into a list of 'Wire's together with an 'Arity'.  
-- (Partial inverse to 'endpoints_of_wires_in_arity'.)
wires_with_arity_of_endpoints :: [Endpoint] -> ([Wire],Arity)
wires_with_arity_of_endpoints es = 
  let ws_with_ts = map (\e -> (wire_of_endpoint e, wiretype_of_endpoint e)) es
  in (map fst ws_with_ts, IntMap.fromList ws_with_ts)

-- | Create an 'Endpoint' from a low-level 'Wire' and 'Wiretype'.
endpoint_of_wire :: Wire -> Wiretype -> Endpoint
endpoint_of_wire w Qbit = Endpoint_Qubit (qubit_of_wire w)
endpoint_of_wire w Cbit = Endpoint_Bit (bit_of_wire w)

-- | Create a list of 'Endpoint's from a list of 'Wire's together with an 'Arity',
-- assuming all wires are present in the arity.
endpoints_of_wires_in_arity :: Arity -> [Wire] -> [Endpoint]
endpoints_of_wires_in_arity a = map (\w -> endpoint_of_wire w (a IntMap.! w))

-- ----------------------------------------------------------------------
-- * Bindings for qubits and bits

-- | Bind a qubit wire to a value, and add it to the given bindings.
bind_qubit :: Qubit -> a -> Bindings a b -> Bindings a b
bind_qubit q x bindings = bind_qubit_wire (wire_of_qubit q) x bindings

-- | Bind a bit wire to a value, and add it to the given bindings.
bind_bit :: Bit -> b -> Bindings a b -> Bindings a b
bind_bit c x bindings = bind_bit_wire (wire_of_bit c) x bindings

-- | Retrieve the value of a qubit wire from the given bindings.
-- Throws an error if the wire was bound to a classical bit.
unbind_qubit :: Bindings a b -> Qubit -> a
unbind_qubit bindings q = unbind_qubit_wire bindings (wire_of_qubit q)

-- | Retrieve the value of a bit wire from the given bindings.  Throws
-- an error if the wire was bound to a qubit.
unbind_bit :: Bindings a b -> Bit -> b
unbind_bit bindings c = unbind_bit_wire bindings (wire_of_bit c)

-- ----------------------------------------------------------------------
-- * Controls for qubits and bits

-- | Add a single signed qubit as a control to a control list.
clist_add_qubit :: Qubit -> Bool -> ControlList -> ControlList
clist_add_qubit q b cl = clist_add (wire_of_qubit q) b cl

-- | Add a single signed bit as a control to a control list.
clist_add_bit :: Bit -> Bool -> ControlList -> ControlList
clist_add_bit c b cl = clist_add (wire_of_bit c) b cl

instance (ControlSource (Signed a), ControlSource (Signed b)) => ControlSource (Signed (B_Endpoint a b)) where
  to_control (Signed (Endpoint_Qubit q) b) = to_control (Signed q b)
  to_control (Signed (Endpoint_Bit c) b) = to_control (Signed c b)

instance (ControlSource a, ControlSource b) => ControlSource (B_Endpoint a b) where
  to_control (Endpoint_Qubit q) = to_control q
  to_control (Endpoint_Bit c) = to_control c
  
instance ControlSource (Signed Qubit) where
  to_control (Signed q b) = to_control (Signed (wire_of_qubit q) b)
  
instance ControlSource Qubit where  
  to_control q = to_control (Signed q True)
  
instance ControlSource (Signed Bit) where
  to_control (Signed q b) = to_control (Signed (wire_of_bit q) b)
  
instance ControlSource Bit where  
  to_control q = to_control (Signed q True)

-- ======================================================================
-- * Namespace management

-- | @'provideSimpleSubroutine' name circ in_struct out_struct is_classically_controllable@:
-- if /name/ not already bound, binds it to /circ/.
-- Note: when there’s an existing value, does /not/ check that
-- it’s equal to /circ/.  
provide_simple_subroutine :: (Typeable a, Typeable b) => 
  BoxId -> OCircuit -> CircuitTypeStructure a -> CircuitTypeStructure b -> Bool -> Circ ()
provide_simple_subroutine name ocirc input_structure output_structure is_classically_controllable = do
  s <- get_namespace
  let OCircuit (win, circ, wout) = ocirc
  let c = if controllable_circuit circ then AllCtl else if is_classically_controllable then OnlyClassicalCtl else NoCtl
  let typed_subroutine = TypedSubroutine ocirc input_structure output_structure c
  let s' = map_provide name typed_subroutine s
  set_namespace s'
  put_subroutine_definition name typed_subroutine

-- | @'provideSubroutines' namespace@:
-- Add each subroutine from the /namespace/ to the current circuit,
-- unless a subroutine of that name already exists.
provide_subroutines :: Namespace -> Circ ()
provide_subroutines state = do
  main_state <- get_namespace
  let state1 = Map.union main_state state
  set_namespace state1
  let new_subs = Map.difference state main_state -- returns subroutines that are in state, but not main_state
  mapM_ (\(n,s) -> put_subroutine_definition n s) (Map.toList new_subs) -- puts a RW_Subroutine for each new subroutine definition

-- | @'provideSubroutine' name circ@:
-- if /name/ not already bound, binds it to the main circuit of /circ/,
-- and additionally provides any missing subroutines of /circ/.
provide_subroutine :: (Typeable a, Typeable b) => 
  BoxId -> OBCircuit -> CircuitTypeStructure a -> CircuitTypeStructure b -> Bool -> Circ ()
provide_subroutine name obcirc input_structure output_structure is_classically_controllable = do
  main_state <- get_namespace
  let (ocirc,subsubroutines) = obcirc
  if Map.member name main_state 
    then return () 
    else do
      provide_simple_subroutine name ocirc input_structure output_structure is_classically_controllable
      provide_subroutines subsubroutines

-- ----------------------------------------------------------------------
-- * General gate
      
-- | Apply the specified low-level gate to the current circuit, using
-- the current controls, and updating the monad state accordingly.
-- This includes run-time well-formedness checks. This is a helper
-- function and is not directly accessible by user code.
apply_gate :: Gate -> Circ ()
apply_gate gate = do
  arity <- get_arity
  clist <- get_clist
  ncflag <- get_ncflag
  let gate' = gate_with_ncflag ncflag gate
  let gate'' = control_gate clist gate'
  case gate'' of 
    Nothing -> return ()
    Just g -> do
      let arity' = arity_append g arity
      put_gate g
      set_arity arity'
      return ()

-- ======================================================================
-- * Basic gates

-- ----------------------------------------------------------------------
-- ** Gates in functional style

-- | Apply a NOT gate to a qubit.
qnot :: Qubit -> Circ Qubit
qnot q = do
  named_gate_qulist "not" False [q] []
  return q

-- | Apply a Hadamard gate.
hadamard :: Qubit -> Circ Qubit
hadamard q = do
  named_gate_qulist "H" False [q] []
  return q

-- | An alternate name for the Hadamard gate.
gate_H :: Qubit -> Circ Qubit
gate_H = hadamard

-- | Apply a multiple-not gate, as specified by a list of booleans and
--   qubits: @qmultinot_list [(True,q1), (False,q2), (True,q3)]@ applies 
--   a not gate to /q1/ and /q3/, but not to /q2/.
qmultinot_list :: [(Qubit, Bool)] -> Circ [Qubit]
qmultinot_list qbs = do
  let qs = map fst $ filter snd qbs
  named_gate_qulist "multinot" False qs []
  return (map fst qbs)

-- | Like 'qmultinot_list', but applies to classical bits instead of
-- qubits. 
cmultinot_list :: [(Bit, Bool)] -> Circ [Bit]
cmultinot_list cs = do
  let ws = map (wire_of_bit . fst) $ filter snd cs
  sequence_ [ apply_gate (CNot w [] False) | w <- ws ]
  return (map fst cs)

-- | Apply a Pauli /X/ gate.
gate_X :: Qubit -> Circ Qubit
gate_X q = do
  named_gate_qulist "X" False [q] []
  return q

-- | Apply a Pauli /Y/ gate.
gate_Y :: Qubit -> Circ Qubit
gate_Y q = do
  named_gate_qulist "Y" False [q] []
  return q

-- | Apply a Pauli /Z/ gate.
gate_Z :: Qubit -> Circ Qubit
gate_Z q = do
  named_gate_qulist "Z" False [q] []
  return q

-- | Apply a Clifford /S/-gate.
gate_S :: Qubit -> Circ Qubit
gate_S q = do
  named_gate_qulist "S" False [q] []
  return q
  
-- | Apply the inverse of an /S/-gate.
gate_S_inv :: Qubit -> Circ Qubit
gate_S_inv q = do
  named_gate_qulist "S" True [q] []
  return q
  
-- | Apply a /T/ = √/S/ gate.
gate_T :: Qubit -> Circ Qubit
gate_T q = do
  named_gate_qulist "T" False [q] []
  return q
  
-- | Apply the inverse of a /T/-gate.
gate_T_inv :: Qubit -> Circ Qubit
gate_T_inv q = do
  named_gate_qulist "T" True [q] []
  return q
  
-- | Apply a Clifford /E/ = /H//S/[sup 3]ω[sup 3] gate. 
-- 
-- \[image E.png]
-- 
-- This gate is the unique Clifford operator with the properties /E/³
-- = /I/, /EXE/⁻¹ = /Y/, /EYE/⁻¹ = /Z/, and /EZE/⁻¹ = /X/. It is a
-- convenient gate for calculations. For example, every Clifford
-- operator can be uniquely written of the form
-- 
-- * /E/[sup /a/]/X/[sup /b/]/S/[sup /c/]ω[sup /d/],
-- 
-- where /a/, /b/, /c/, and /d/ are taken modulo 3, 2, 4, and 8,
-- respectively.
gate_E :: Qubit -> Circ Qubit
gate_E q = do
  named_gate_qulist "E" False [q] []
  return q
  
-- | Apply the inverse of an /E/-gate.
gate_E_inv :: Qubit -> Circ Qubit
gate_E_inv q = do
  named_gate_qulist "E" True [q] []
  return q
  
-- | Apply the scalar ω = [exp /i/π\/4], as a single-qubit gate.
gate_omega :: Qubit -> Circ Qubit
gate_omega q = do
  named_gate_qulist "omega" False [q] []
  return q

-- | Apply a /V/ = √/X/ gate. This is by definition the following gate
-- (see also Nielsen and Chuang, p.182):
-- 
-- \[image V.png]
gate_V :: Qubit -> Circ Qubit
gate_V q = do
  named_gate_qulist "V" False [q] []
  return q

-- | Apply the inverse of a /V/-gate.
gate_V_inv :: Qubit -> Circ Qubit
gate_V_inv q = do
  named_gate_qulist "V" True [q] []
  return q

-- | Apply a SWAP gate.
swap_qubit :: Qubit -> Qubit -> Circ (Qubit,Qubit)
swap_qubit q1 q2 = do
  named_gate_qulist "swap" False [q1, q2] []
  return (q1,q2)

-- | Apply a classical SWAP gate.
swap_bit :: Bit -> Bit -> Circ (Bit,Bit)
swap_bit c1 c2 = do
  apply_gate (CSwap (wire_of_bit c1) (wire_of_bit c2) [] False)
  return (c1,c2)

-- | Apply an [exp −/iZt/] gate. The timestep /t/ is a parameter.
expZt :: Timestep -> Qubit -> Circ Qubit
expZt t q = do
  named_rotation_qulist "exp(-i%Z)" False t [q] []
  return q

-- | Apply a rotation by angle 2π/i/\/2[sup /n/] about the /z/-axis.
-- 
-- \[image rGate.png]
rGate :: Int -> Qubit -> Circ Qubit
rGate n q = do
  named_rotation_qulist "R(2pi/%)" False (2^n) [q] []
  return q

-- | Apply a /W/ gate. The /W/ gate is self-inverse and diagonalizes
-- the SWAP gate. 
-- 
-- \[image W.png]
-- 
-- The arguments are such that 
-- 
-- > gate_W |0〉 |0〉 = |00〉
-- > gate_W |0〉 |1〉 = (|01〉+|10〉) / √2
-- > gate_W |1〉 |0〉 = (|01〉-|10〉) / √2
-- > gate_W |1〉 |1〉 = |11〉.
-- 
-- In circuit diagrams, /W/[sub 1] denotes the \"left\" qubit, and /W/[sub 2]
-- denotes the \"right\" qubit.
gate_W :: Qubit -> Qubit -> Circ (Qubit, Qubit)
gate_W q1 q2 = do
  named_gate_qulist "W" False [q1, q2] []
  return (q1, q2)

-- | Apply an /iX/ gate. This gate is used similarly to the Pauli /X/
-- gate, but with two advantages:
-- 
-- * the doubly-controlled /iX/ gate can be implemented in the
-- Clifford+/T/ gate base with /T/-count 4 (the doubly-controlled /X/
-- gate requires /T/-count 7);
-- 
-- * the /iX/-gate has determinant 1, and therefore an /n/-times
-- controlled /iX/ gate can be implemented in the Clifford+/T/ gate
-- base with no ancillas.
-- 
-- In particular, the /iX/ gate can be used to implement an additional
-- control with /T/-count 8, like this:
-- 
-- \[image iX.png]
gate_iX :: Qubit -> Circ Qubit
gate_iX q = do
  named_gate_qulist "iX" False [q] []
  return q

-- | Apply a −/iX/ gate. This is the inverse of 'gate_iX'.
gate_iX_inv :: Qubit -> Circ Qubit
gate_iX_inv q = do
  named_gate_qulist "iX" True [q] []
  return q

-- | Apply a global phase change [exp /i/π/t/], where typically /t/ ∈
-- [0,2].  This gate is uninteresting if not controlled; however, it
-- has non-trivial effect if it is used as a controlled gate.
global_phase :: Double -> Circ ()
global_phase t = do
  apply_gate (GPhase t [] [] False)
  return ()

-- | Like 'global_phase', except the gate is also \"anchored\" at a
-- particular bit or qubit. This is strictly for graphical
-- presentation purposes, to provide a hint for where the gate should
-- be printed in a circuit diagram. Backends are free to ignore this
-- hint altogether. The anchor is not actually an input to the gate,
-- and it is legal for the anchoring qubit to also be used as a
-- control control.
global_phase_anchored_list :: Double -> [Endpoint] -> Circ ()
global_phase_anchored_list t qs = do
  apply_gate (GPhase t (map wire_of_endpoint qs) [] False)
  return ()

-- | Apply a generic quantum gate to a given list of qubits and a
-- given list of generalized controls. The generalized controls are
-- really inputs to the gate, but are guaranteed not to be modified
-- if they are in a computational basis state.
named_gate_qulist :: String -> InverseFlag -> [Qubit] -> [Qubit] -> Circ ([Qubit],[Qubit])
named_gate_qulist name inv operands gencontrols = do
  apply_gate (QGate name inv (map wire_of_qubit operands) (map wire_of_qubit gencontrols) [] False)
  return (operands, gencontrols)

-- | Like 'named_gate_qulist', but produce a named gate that also
-- depends on a real parameter. This is typically used for rotations
-- or phase gates parameterized by an angle. The name can contain
-- \'%\' as a place holder for the parameter, for example @\"exp(-i%Z)\"@.
named_rotation_qulist :: String -> InverseFlag -> Timestep -> [Qubit] -> [Qubit] -> Circ ([Qubit],[Qubit])
named_rotation_qulist name inv theta operands gencontrols = do
  apply_gate (QRot name inv theta (map wire_of_qubit operands) (map wire_of_qubit gencontrols) [] False)
  return (operands, gencontrols)

-- | Apply a NOT gate to a classical bit.
cnot :: Bit -> Circ Bit
cnot b = do
  apply_gate (CNot (wire_of_bit b) [] False)
  return b

-- ----------------------------------------------------------------------
-- ** Gates in imperative style

-- | Apply a NOT gate to a qubit.
qnot_at :: Qubit -> Circ ()
qnot_at q = do
  qnot q
  return ()

-- | Apply a Hadamard gate.
hadamard_at :: Qubit -> Circ ()
hadamard_at q = do
  hadamard q
  return ()

-- | An alternate name for the Hadamard gate.
gate_H_at :: Qubit -> Circ ()
gate_H_at = hadamard_at

-- | Apply a /qmultinot_list/ gate, as specified by a list of booleans and
--   qubits: @qmultinot_list [(True,q1), (False,q2), (True,q3)]@ applies 
--   a not gate to /q1/ and /q3/, but not to /q2/.
qmultinot_list_at :: [(Qubit, Bool)] -> Circ ()
qmultinot_list_at qs = do
  qmultinot_list qs
  return ()

-- | Like 'qmultinot_list_at', but applies to classical bits instead of
-- qubits. 
cmultinot_list_at :: [(Bit, Bool)] -> Circ ()
cmultinot_list_at cs = do
  cmultinot_list cs
  return ()

-- | Apply a Pauli /X/ gate.
gate_X_at :: Qubit -> Circ ()
gate_X_at q = do
  gate_X q
  return ()

-- | Apply a Pauli /Y/ gate.
gate_Y_at :: Qubit -> Circ ()
gate_Y_at q = do
  gate_Y q
  return ()

-- | Apply a Pauli /Z/ gate.
gate_Z_at :: Qubit -> Circ ()
gate_Z_at q = do
  gate_Z q
  return ()

-- | Apply a Clifford /S/-gate.
gate_S_at :: Qubit -> Circ ()
gate_S_at q = do
  gate_S q
  return ()

-- | Apply the inverse of an /S/-gate.
gate_S_inv_at :: Qubit -> Circ ()
gate_S_inv_at q = do
  gate_S_inv q
  return ()

-- | Apply a /T/ = √/S/ gate.
gate_T_at :: Qubit -> Circ ()
gate_T_at q = do
  gate_T q
  return ()

-- | Apply the inverse of a /T/-gate.
gate_T_inv_at :: Qubit -> Circ ()
gate_T_inv_at q = do
  gate_T_inv q
  return ()

-- | Apply a Clifford /E/ = /H//S/[sup 3]ω[sup 3] gate. 
-- 
-- \[image E.png]
-- 
-- This gate is the unique Clifford operator with the properties /E/³
-- = /I/, /EXE/⁻¹ = /Y/, /EYE/⁻¹ = /Z/, and /EZE/⁻¹ = /X/. It is a
-- convenient gate for calculations. For example, every Clifford
-- operator can be uniquely written of the form
-- 
-- * /E/[sup /a/]/X/[sup /b/]/S/[sup /c/]ω[sup /d/],
-- 
-- where /a/, /b/, /c/, and /d/ are taken modulo 3, 2, 4, and 8,
-- respectively.
gate_E_at :: Qubit -> Circ ()
gate_E_at q = do
  gate_E q
  return ()

-- | Apply the inverse of an /E/-gate.
gate_E_inv_at :: Qubit -> Circ ()
gate_E_inv_at q = do
  gate_E_inv q
  return ()

-- | Apply the scalar ω = [exp /i/π\/4], as a single-qubit gate.
gate_omega_at :: Qubit -> Circ ()
gate_omega_at q = do
  gate_omega q
  return ()

-- | Apply a /V/ = √/X/ gate. This is by definition the following gate
-- (see also Nielsen and Chuang, p.182):
-- 
-- \[image V.png]
gate_V_at :: Qubit -> Circ ()
gate_V_at q = do
  gate_V q
  return ()

-- | Apply the inverse of a /V/-gate.
gate_V_inv_at :: Qubit -> Circ ()
gate_V_inv_at q = do
  gate_V_inv q
  return ()

-- | Apply a SWAP gate.
swap_qubit_at :: Qubit -> Qubit -> Circ ()
swap_qubit_at q1 q2 = do
  swap_qubit q1 q2
  return ()

-- | Apply a classical SWAP gate.
swap_bit_at :: Bit -> Bit -> Circ ()
swap_bit_at c1 c2 = do
  swap_bit c1 c2
  return ()

-- | Apply an [exp −/iZt/] gate. The timestep /t/ is a parameter.
expZt_at :: Timestep -> Qubit -> Circ ()
expZt_at t q = do
  expZt t q
  return ()

-- | Apply a rotation by angle 2π/i/\/2[sup /n/] about the /z/-axis.
-- 
-- \[image rGate.png]
rGate_at :: Int -> Qubit -> Circ ()
rGate_at n q = do
  rGate n q
  return ()

-- | Apply a /W/ gate. The /W/ gate is self-inverse and diagonalizes
-- the SWAP gate. 
-- 
-- \[image W.png]
-- 
-- The arguments are such that 
-- 
-- > gate_W |0〉 |0〉 = |00〉
-- > gate_W |0〉 |1〉 = (|01〉+|10〉) / √2
-- > gate_W |1〉 |0〉 = (|01〉-|10〉) / √2
-- > gate_W |1〉 |1〉 = |11〉.
-- 
-- In circuit diagrams, /W/[sub 1] denotes the \"left\" qubit, and /W/[sub 2]
-- denotes the \"right\" qubit.
gate_W_at :: Qubit -> Qubit -> Circ ()
gate_W_at q1 q2 = do
  gate_W q1 q2
  return ()

-- | Apply an /iX/ gate. This gate is used similarly to the Pauli /X/
-- gate, but with two advantages:
-- 
-- * the doubly-controlled /iX/ gate can be implemented in the
-- Clifford+/T/ gate base with /T/-count 4 (the doubly-controlled /X/
-- gate requires /T/-count 7);
-- 
-- * the /iX/-gate has determinant 1, and therefore an /n/-times
-- controlled /iX/ gate can be implemented in the Clifford+/T/ gate
-- base with no ancillas.
-- 
-- In particular, the /iX/ gate can be used to implement an additional
-- control with /T/-count 8, like this:
-- 
-- \[image iX.png]
gate_iX_at :: Qubit -> Circ ()
gate_iX_at q = do
  gate_iX q
  return ()

-- | Apply a −/iX/ gate. This is the inverse of 'gate_iX_at'.
gate_iX_inv_at :: Qubit -> Circ ()
gate_iX_inv_at q = do
  gate_iX_inv q
  return ()

-- | Apply a generic quantum gate to a given list of qubits and a
-- given list of generalized controls. The generalized controls are
-- really inputs to the gate, but are guaranteed not to be modified
-- if they are in a computational basis state.
named_gate_qulist_at :: String -> InverseFlag -> [Qubit] -> [Qubit] -> Circ ()
named_gate_qulist_at name inv operands gencontrols = do
  named_gate_qulist name inv operands gencontrols  
  return ()

-- | Like 'named_gate_qulist_at', but produce a named gate that also
-- depends on a real parameter. This is typically used for rotations
-- or phase gates parameterized by an angle. The name can contain
-- \'%\' as a place holder for the parameter, for example @\"exp(-i%Z)\"@.
named_rotation_qulist_at :: String -> InverseFlag -> Timestep -> [Qubit] -> [Qubit] -> Circ ()
named_rotation_qulist_at name inv t operands gencontrols = do
  named_rotation_qulist name inv t operands gencontrols  
  return ()

-- | Apply a NOT gate to a classical bit.
cnot_at :: Bit -> Circ ()
cnot_at b = do
  cnot b
  return ()

-- ----------------------------------------------------------------------
-- ** Bitwise initialization and termination functions

-- | Generate a new qubit, initialized to the parameter 'Bool'.
qinit_qubit :: Bool -> Circ Qubit
qinit_qubit b = do
  arity <- get_arity
  let w = arity_unused_wire arity
  apply_gate (QInit b w False)
  return (qubit_of_wire w)

-- | Terminate a qubit asserted to be in state /b/. 
-- 
-- We note that the assertion is relative to the precision: when gates
-- in a circuit are implemented up to some precision ε (either due to
-- physical limitations, or due to decomposition into a discrete gate
-- base), the assertion may only hold up to a corresponding precision
-- as well.
qterm_qubit :: Bool -> Qubit -> Circ ()
qterm_qubit b q = do
  apply_gate (QTerm b (wire_of_qubit q) False)
  return ()

-- | Discard a qubit destructively.
qdiscard_qubit :: Qubit -> Circ ()
qdiscard_qubit q = do
  apply_gate (QDiscard (wire_of_qubit q))
  return ()

-- | Generate a new qubit, initialized from a classical bit. Note that
-- the classical bit is simultaneously terminated. 
prepare_qubit :: Bit -> Circ Qubit
prepare_qubit c = do
  let w = wire_of_bit c
  apply_gate (QPrep w False)
  return (qubit_of_wire w)

-- | Unprepare a qubit asserted to be in a computational basis
-- state. This is the same as a measurement, but must only be applied
-- to qubits that are already known to be in one of the states |0〉 or
-- |1〉, and not in superposition. This operation is rarely (perhaps
-- never?) used in any quantum algorithms, but we include it for
-- consistency reasons, because it is formally the inverse of
-- 'prepare_qubit'.
unprepare_qubit :: Qubit -> Circ Bit
unprepare_qubit q = do
  let w = wire_of_qubit q
  apply_gate (QUnprep w False)
  return (bit_of_wire w)

-- | Apply a measurement gate (turns a qubit into a bit).
measure_qubit :: Qubit -> Circ Bit
measure_qubit q = do
  let w = wire_of_qubit q
  apply_gate (QMeas w)
  return (bit_of_wire w)

-- | Generate a new classical bit, initialized to a boolean parameter
-- /b/.
cinit_bit :: Bool -> Circ Bit
cinit_bit b = do
  arity <- get_arity
  let w = arity_unused_wire arity
  apply_gate (CInit b w False)
  return (bit_of_wire w)

-- | Terminate a classical 'Bit' asserted to be in state 'Bool'.
cterm_bit :: Bool -> Bit -> Circ ()
cterm_bit b c = do
  let w = wire_of_bit c
  apply_gate (CTerm b w False)
  return ()

-- | Terminate a classical 'Bit' with a comment indicating what the
-- observed state of the 'Bit' was, in this particular dynamic run of
-- the circuit. This is typically used to terminate a wire right after
-- a dynamic lifting has been performed.  It is not intended to be a
-- user-level operation.
-- 
-- It is important to note that a 'DTerm' gate does not, in any way,
-- represent an assertion. Unlike a 'CTerm' gate, which asserts that
-- the classical bit will have the stated value at /every/ run of the
-- circuit, the 'DTerm' gate simply records that the classical bit had
-- the stated value at some /particular/ run of the circuit.
--  
-- Operationally (e.g., in a simulator), the 'DTerm' gate can be
-- interpreted in multiple ways. In the simplest case, it is just
-- treated like a 'CDiscard' gate, and the boolean comment
-- ignored. Alternatively, it can be treated as a post-selection gate:
-- if the actual value does not equal the stated value, the entire
-- computation is aborted. Normally, 'DTerm' gates should appear in
-- the /output/, not the /input/ of simulators; therefore, the details
-- of the behavior of any particular simulator on a 'DTerm' gate are
-- implementation dependent.
dterm_bit :: Bool -> Bit -> Circ ()
dterm_bit b c = do
  let w = wire_of_bit c
  apply_gate (DTerm b w)
  return ()

-- | Discard a classical bit destructively.
cdiscard_bit :: Bit -> Circ ()
cdiscard_bit c = do
  let w = wire_of_bit c
  apply_gate (CDiscard w)
  return ()

-- ----------------------------------------------------------------------
-- ** Classical gates

-- $CLASSICAL
--
-- The gates in this section are for constructing classical circuits. 
-- None of these gates alter or discard their inputs; each gate produces 
-- a new wire holding the output of the gate.

-- | Return the \"exclusive or\" of a list of bits. 
cgate_xor :: [Bit] -> Circ Bit
cgate_xor inputs =
  cgate "xor" inputs
  
-- | Test equality of two bits, and return 'True' iff they are equal. 
cgate_eq :: Bit -> Bit -> Circ Bit
cgate_eq a b = cgate "eq" [a,b]

-- | If /a/ is 'True', then return /b/, else return /c/.
cgate_if_bit :: Bit -> Bit -> Bit -> Circ Bit
cgate_if_bit a b c = cgate "if" [a,b,c]

-- | Return the negation of its input. Note that unlike 'cnot' or
-- 'cnot_at', this gate does not alter its input, but returns a newly
-- created bit.
cgate_not :: Bit -> Circ Bit
cgate_not a = cgate "not" [a]

-- | Return the conjunction of a list of bits.
cgate_and :: [Bit] -> Circ Bit
cgate_and inputs = cgate "and" inputs

-- | Return the disjunction of a list of bits.
cgate_or :: [Bit] -> Circ Bit
cgate_or inputs = cgate "or" inputs

-- | Apply a named classical gate. This is used to define all of the
-- above classical gates, but should not usually be directly used by
-- user code.
cgate :: String -> [Bit] -> Circ Bit
cgate name inputs = do
  arity <- get_arity
  let w = arity_unused_wire arity
  apply_gate (CGate name w (map wire_of_bit inputs) False)
  return (bit_of_wire w)

-- | @'cgateinv' name w inputs@: Uncompute a named classical
-- gate. This asserts that /w/ is in the state determined by the gate
-- type and the /inputs/, then uncomputes /w/ in a reversible
-- way. This rarely used gate is formally the inverse of 'cgate'.
cgateinv :: String -> Bit -> [Bit] -> Circ ()
cgateinv name c inputs = do
  let w = wire_of_bit c
  apply_gate (CGateInv name w (map wire_of_bit inputs) False)
  return ()

-- ----------------------------------------------------------------------
-- ** Subroutines

-- | Insert a subroutine gate with specified name, and input/output
-- output types, and attach it to the given endpoints. Return the new
-- endpoints.
--
-- Note that the @['Wire']@ and 'Arity' arguments are used as a /pattern/
-- for the locations/types of wires of the subroutine; the @['Endpoint']@
-- argument (and output) specify what is attached in the current circuit.
-- The two aspects of this pattern that are respected are: the
-- lingeringness of any inputs; and the number and types of wires.
--
-- For instance (assuming for simplicity that all wires are qubits), if
-- the patterns given are “inputs [1,3,5], outputs [1,3,4]”, and the 
-- actual inputs specified are [20,21,25], then the output wires produced 
-- might be e.g. [20,21,23], [20,21,36], or [20,21,8], depending on the 
-- next available free wire.
--
-- More subtly, if
-- the patterns given are “inputs [1,2,3], outputs [3,7,8,1]”,
-- and the inputs given are [10,5,4], then the outputs will be
-- [4,/x/,/y/,10], where /x/, /y/ are two fresh wires.
--
-- Note that lingering wires may change type, for e.g. subroutines that
-- include measurements.
--
-- It is currently assumed that all these lists are linear, i.e. contain
-- no duplicates.
subroutine :: BoxId -> InverseFlag -> ControllableFlag
           -> RepeatFlag -> [Wire] -> Arity -> [Wire] -> Arity
           -> [Endpoint] -> Circ [Endpoint]
subroutine name inv scf rep win_pattern ain_pattern wout_pattern aout_pattern ein = do
  let (win,ain) = wires_with_arity_of_endpoints ein
  -- Check the given input wires match the pattern:
  when (not $ all (\(w_p,w) -> ain_pattern IntMap.! w_p == ain IntMap.! w) $ zip_strict_errmsg win_pattern win e_num_inputs) $ do 
    error e_input_types
  -- Work out which input wires are lingering, and how many new wires are needed:
  let partial_wout = map (\w_p -> let maybe_w = lookup w_p (zip win_pattern win)
                                  in (maybe_w, aout_pattern IntMap.! w_p))
                         wout_pattern
      num_new_wires = length $ filter ((== Nothing) . fst) partial_wout 
  -- Allocate new wires for the non-lingering outputs:
  arity <- get_arity
  let new_wires = arity_unused_wires num_new_wires arity
      eout = insert_new_wires partial_wout new_wires
      (wout,aout) = wires_with_arity_of_endpoints eout
  apply_gate (Subroutine name inv win ain wout aout [] False scf rep)
  return eout
  where
    insert_new_wires :: [(Maybe Wire, Wiretype)] -> [Wire] -> [Endpoint]
    insert_new_wires ((Just w,t):ws) new_wires = (endpoint_of_wire w t):(insert_new_wires ws new_wires)
    insert_new_wires ((Nothing,t):ws) (next_new:new_wires) = (endpoint_of_wire next_new t):(insert_new_wires ws new_wires)
    insert_new_wires [] [] = []
    insert_new_wires _ _ = error e_output_allocation
    e_num_inputs = "subroutine: subroutine " ++ show name ++ " applied to the wrong number of input wires"
    e_input_types = "subroutine: subroutine " ++ show name ++ " applied to input wires of incorrect type"
    e_output_allocation = "internal error: Quipper.Monad.subroutine: output wire allocation"


-- | Look up the specified subroutine in the namespace, and apply it
-- to the specified inputs, or throw an error if they are not appropriately
-- typed.
--
-- The input/output types of this function are determined dynamically
-- by the 'CircuitTypeStructure' stored with the subroutine.
call_subroutine :: (Typeable a, Typeable b) => BoxId -> RepeatFlag -> a -> Circ b
call_subroutine name r x = do
  ns <- get_namespace
  let mc = Map.lookup name ns
  case mc of 
    Nothing -> 
      error ("call_subroutine: subroutine " ++ show name ++ " does not exist in current namespace: " ++ showNames ns)
    Just (TypedSubroutine ocircuit input_structure output_structure scf) -> do
      let OCircuit (win_pattern, circuit, wout_pattern) = ocircuit
      let (ain_pattern, gates, aout_pattern, n) = circuit
      let (win, ain) = case cast input_structure of
            Just suitable_input_structure -> destructure_with suitable_input_structure x
            Nothing -> error ("call_subroutine: subroutine " ++ show name ++ " applied to input of incorrect type")
      let ein = endpoints_of_wires_in_arity ain win
      eout <- subroutine name False scf r win_pattern ain_pattern wout_pattern aout_pattern ein
      let (wout, aout) = wires_with_arity_of_endpoints eout
      
      --  The output structure of the subroutine contains the wires
      --  corresponding to the actual output type of the function and
      --  the wires that were created but forgotten, in
      --  imperative-style. (see comments in 'provide_subroutine_generic').
      let (y,_::([Qubit],[Bit])) = case cast output_structure of
            Just suitable_output_structure -> structure_with suitable_output_structure (wout, aout)
            Nothing -> error ("call_subroutine: attempt to use outputs of subroutine " ++ show name ++ " as incorrect type")
      return y

-- ----------------------------------------------------------------------
-- ** Comments
  
-- | Insert a comment in the circuit. This is not a gate, and has no
-- effect, except to mark a spot in the circuit. The comment has two
-- parts: a string (possibly empty), and a list of labelled wires
-- (possibly empty). This is a low-level function. Users should use
-- 'comment' instead.
comment_label :: String -> InverseFlag -> [(Wire, String)] -> Circ ()
comment_label s inv ws = do
  b <- get_nocommentflag
  when (not b) $ do
    apply_gate (Comment s inv ws)
  return ()

-- | Disable labels and comments for a block of code. The intended
-- usage is like this:
-- 
-- > without_comments $ do {
-- >   <<<code block>>>
-- > }
-- 
-- This is sometimes useful in situations where code is being re-used,
-- for example when one function is implemented in terms of another,
-- but should not inherit comments from it. It is also useful in the
-- definition of recursive function, where a comment should only be
-- applied at the outermost level. Finally, it can be used to suppress
-- comments from parts of circuits for presentation purposes.
without_comments :: Circ a -> Circ a
without_comments body = do
  b <- get_nocommentflag
  set_nocommentflag True
  a <- body
  set_nocommentflag b
  return a
  
-- ----------------------------------------------------------------------
-- ** Dynamic lifting
  
-- | Convert a 'Bit' (boolean circuit output) to a 'Bool' (boolean
-- parameter).
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
-- 'dynamic_lift_bit' operation interrupts the batch mode operation of
-- the quantum device (where circuits are generated ahead of time),
-- and forces interactive operation (the quantum device must wait for
-- the next portion of the circuit to be generated). This operation is
-- especially expensive if the current circuit contains unmeasured
-- qubits; in this case, the qubits must be preserved while the
-- quantum device remains on standby.
-- 
-- Also note that this operation is not supported in all contexts. It
-- is an error, for example, to use this operation in a circuit that
-- is going to be reversed, or in the body of a boxed subroutine.
-- Also, not all output devices (such as circuit viewers) support this
-- operation.
dynamic_lift_bit :: Bit -> Circ Bool
dynamic_lift_bit c = do
  b <- do_read (wire_of_bit c)
  dterm_bit b c
  return b
  
-- ======================================================================
-- * Other circuit-building functions

-- | Generate a new qubit initialized to |+〉 when /b/='False' and
-- |−〉 when /b/='True'.
qinit_plusminus :: Bool -> Circ Qubit
qinit_plusminus b = do
  q <- qinit_qubit b
  q <- hadamard q
  return q  

-- | Generate a new qubit initialized to one of |0〉, |1〉, |+〉, |−〉,
-- depending on a character /c/ which is \'0\', \'1\', \'+\', or \'-\'.
qinit_of_char :: Char -> Circ Qubit
qinit_of_char '0' = qinit_qubit False
qinit_of_char '1' = qinit_qubit True
qinit_of_char '+' = qinit_plusminus False
qinit_of_char '-' = qinit_plusminus True
qinit_of_char c = error ("qinit_of_char: unimplemented initialization: " ++ [c])

-- | Generate a list of qubits initialized to a sequence of |0〉, |1〉,
-- |+〉, |−〉, defined by a string argument e.g. \"00+0+++\".
qinit_of_string :: String -> Circ [Qubit]
qinit_of_string s = sequence (map qinit_of_char s)

-- | A version of 'qinit_qubit' that operates on lists. 
qinit_list :: [Bool] -> Circ [Qubit]
qinit_list bs = mapM qinit_qubit bs


-- | A version of 'qterm_qubit' that operates on lists. We initialize
-- left-to-right and terminate right-to-left, as this leads to more
-- symmetric and readable circuits, more stable under reversal.
-- 
-- Note: if the left argument to 'qterm_list' is longer than the right
-- argument, then it is truncated. So the first argument can be
-- ('repeat' 'False'). It is an error if the left argument is shorter
-- than the right one.
qterm_list :: [Bool] -> [Qubit] -> Circ ()
qterm_list bs qs =
  zipRightWithRightStrictM_ qterm_qubit bs qs

-- | A version of 'cinit_bit' for lists.
cinit_list :: [Bool] -> Circ [Bit]
cinit_list bs = mapM cinit_bit bs

-- ======================================================================
-- * Higher-order functions

-- | Convenient wrapper around 'qinit' and 'qterm'. This can be used
-- to introduce an ancilla with a local scope, like this:
-- 
-- > with_ancilla $ \h -> do {
-- >   <<<code block using ancilla h>>>
-- > }
-- 
-- The ancilla will be initialized to |0〉 at the beginning of the
-- block, and it is the programmer's responsibility to ensure that it
-- will be returned to state |0〉 at the end of the block.
-- 
-- A block created with 'with_ancilla' is controllable, provided that
-- the body is controllable.
with_ancilla :: (Qubit -> Circ a) -> Circ a
with_ancilla f = do
  q <- without_controls (qinit_qubit False)
  a <- f q
  without_controls (qterm_qubit False q)
  return a

-- | A syntax for \"if\"-style (classical and quantum) controls. 
-- This can be used as follows:
-- 
-- > gate1
-- > with_controls <<controls>> $ do {
-- >   gate2
-- >   gate3
-- > }
-- > gate4
-- 
-- The specified controls will be applied to gate2 and gate3. It is an
-- error to specify a control for a gate that cannot be controlled
-- (such as measurement).
  
with_controls :: ControlSource c => c -> Circ a -> Circ a
with_controls control code = do
  clist_old <- get_clist
  set_clist (combine (to_control control) clist_old)
  a <- code
  set_clist clist_old
  return a
  
-- | An infix operator to apply the given controls to a gate:
-- 
-- > gate `controlled` <<controls>>
-- 
-- It also works with functional-style gates:
-- 
-- > result <- gate `controlled` <<controls>>
-- 
-- The infix operator is left associative, so it can be applied
-- multiple times:
-- 
-- > result <- gate `controlled` <<controls1>> `controlled` <<controls2>>
-- 
-- The latter is equivalent to
-- 
-- > result <- gate `controlled` <<controls1>> .&&. <<controls2>>

controlled :: ControlSource c => Circ a -> c -> Circ a
controlled code control = with_controls control code

infixl 2 `controlled`

-- | Apply a block of gates while temporarily suspending the
-- application of controls.  This can be used to omit controls on
-- gates where they are known to be unnecessary. This is a relatively
-- low-level function and should not normally be called directly by
-- user code. Instead, it is safer to use a higher-level function such
-- as 'with_basis_change'. However, the 'without_controls' operator is
-- useful in certain situations, e.g., it can be used to preserve the
-- 'NoControlFlag' when defining transformers.
-- 
-- Usage:
-- 
-- > without_controls $ do 
-- >   <<code block>>
-- 
-- or:
-- 
-- > without_controls (gate)
-- 
-- Note that all controls specified in the /surrounding/ code are
-- disabled within the 'without_controls' block. This is even true if
-- the 'without_controls' block appears in a subroutine, and the
-- subroutine is later called in a controlled context. On the other
-- hand, it is possible to specify controls /inside/ the
-- 'without_controls' block. Consider this example:
-- 
-- > my_subcircuit = do
-- >   gate1
-- >   without_controls $ do {
-- >     gate2
-- >     gate3 `controlled` <<controls1>>
-- >   }
-- >   gate4
-- >
-- > my_circuit = do
-- >   my_subcircuit `controlled` <<controls2>>
-- 
-- In this example, controls 1 will be applied to gate 3, controls 2
-- will be applied to gates 1 and 4, and no controls will be applied
-- to gate 2.
without_controls :: Circ a -> Circ a
without_controls code = do
  clist_old <- get_clist
  ncflag_old <- get_ncflag
  set_clist clist_empty
  set_ncflag True
  a <- code
  set_clist clist_old
  set_ncflag ncflag_old
  return a
  
-- | Apply 'without_controls' if 'NoControlFlag' is 'True', otherwise
-- do nothing.
without_controls_if :: NoControlFlag -> Circ a -> Circ a
without_controls_if True = without_controls
without_controls_if False = id

-- ----------------------------------------------------------------------
-- ** Deprecated special cases of without_controls

-- | Generate a new qubit, initialized to the parameter 'Bool', that
--   is guaranteed to be used as an ancilla and terminated with
--   'qterm_qubit_ancilla'. Deprecated.
qinit_qubit_ancilla :: Bool -> Circ Qubit
qinit_qubit_ancilla b = do
  without_controls $ do
    qinit_qubit b

-- | Terminate an ancilla asserted to be in state /b/. Deprecated.
qterm_qubit_ancilla :: Bool -> Qubit -> Circ ()
qterm_qubit_ancilla b q = do
  without_controls $ do
    qterm_qubit b q

-- ======================================================================
-- * Circuit transformers

-- | The identity transformer. This just maps a low-level circuits to
-- the corresponding circuit-generating function. It can also be used
-- as a building block in other transformers, to define \"catch-all\"
-- clauses for gates that don't need to be transformed.
identity_transformer :: Transformer Circ Qubit Bit
identity_transformer (T_QGate name _ _ inv ncf f) = f $
  \ws vs c -> without_controls_if ncf $ do
    (ws', vs') <- named_gate_qulist name inv ws vs `controlled` c
    return (ws', vs', c)
identity_transformer (T_QRot name _ _ inv t ncf f) = f $
  \ws vs c -> without_controls_if ncf $ do
    (ws', vs') <- named_rotation_qulist name inv t ws vs `controlled` c
    return (ws', vs', c)
identity_transformer (T_GPhase t ncf f) = f $
  \qs c -> without_controls_if ncf $ do
    global_phase_anchored_list t qs `controlled` c
    return c
identity_transformer (T_CNot ncf f) = f $
  \q c -> without_controls_if ncf $ do
    q' <- cnot q `controlled` c
    return (q', c)
identity_transformer (T_CGate name ncf f) = f $
  \ws -> without_controls_if ncf $ do    
    v <- cgate name ws
    return (v, ws)
identity_transformer (T_CGateInv name ncf f) = f $
  \v ws -> without_controls_if ncf $ do    
    cgateinv name v ws
    return ws
identity_transformer (T_CSwap ncf f) = f $
  \w v c -> without_controls_if ncf $ do
    (w',v') <- swap_bit w v `controlled` c
    return (w',v',c)
identity_transformer (T_QPrep ncf f) = f $
  \w -> without_controls_if ncf $ do    
    v <- prepare_qubit w
    return v
identity_transformer (T_QUnprep ncf f) = f $    
  \w -> without_controls_if ncf $ do    
    v <- unprepare_qubit w
    return v
identity_transformer (T_QInit b ncf f) = f $
  without_controls_if ncf $ do
    w <- qinit_qubit b
    return w
identity_transformer (T_CInit b ncf f) = f $
  without_controls_if ncf $ do
    w <- cinit_bit b
    return w
identity_transformer (T_QTerm b ncf f) = f $
  \w -> without_controls_if ncf $ do
    qterm_qubit b w
    return ()
identity_transformer (T_CTerm b ncf f) = f $
  \w -> without_controls_if ncf $ do
    cterm_bit b w
    return ()
identity_transformer (T_QMeas f) = f $    
  \w -> do
    v <- measure_qubit w
    return v
identity_transformer (T_QDiscard f) = f $
  \w -> do
    qdiscard_qubit w
    return ()
identity_transformer (T_CDiscard f) = f $
  \w -> do
    cdiscard_bit w
    return ()
identity_transformer (T_DTerm b f) = f $
  \w -> do
    dterm_bit b w
    return ()
identity_transformer (T_Subroutine n inv ncf scf ws_pat a1 vs_pat a2 rep f) = f $
  \namespace ws c -> without_controls_if ncf $ do
    provide_subroutines namespace
    vs <- subroutine n inv scf rep ws_pat a1 vs_pat a2 ws `controlled` c
    return (vs,c)
identity_transformer (T_Comment s inv f) = f $
  \ws -> do
    comment_label s inv [ (wire_of_endpoint e, s) | (e,s) <- ws ]
    return ()

-- | The identity transformer can be enriched with a dynamic lifting operation, so
-- as to define a DynamicTransformer
identity_dynamic_transformer_with_lift :: (Bit -> Circ Bool) -> DynamicTransformer Circ Qubit Bit
identity_dynamic_transformer_with_lift f = DT {
  transformer = identity_transformer,
  define_subroutine = \name typed_subroutine -> do
    s <- get_namespace
    let s' = map_provide name typed_subroutine s
    set_namespace s'
    put_subroutine_definition name typed_subroutine,
  lifting_function = f
 }

-- | The identity DynamicTransformer uses the built in do_read operation
identity_dynamic_transformer :: DynamicTransformer Circ Qubit Bit
identity_dynamic_transformer = 
  identity_dynamic_transformer_with_lift (\b -> do_read (wire_of_bit b))

-- | We can define a dynamic transformer with a "constant" lifting function
identity_dynamic_transformer_constant :: Bool -> DynamicTransformer Circ Qubit Bit
identity_dynamic_transformer_constant b = identity_dynamic_transformer_with_lift (\_ -> return b) 

-- | Append the entire circuit /c/ to the current circuit, using the
-- given bindings. Return the new bindings.
apply_circuit_with_bindings :: Circuit -> (Bindings Qubit Bit) 
                            -> Circ (Bindings Qubit Bit)
apply_circuit_with_bindings c bindings =
  transform_circuit identity_transformer c bindings

-- | Append the entire circuit /c/ to the current circuit, using the
-- given bindings, and return the new bindings.  
-- Also, add to the current namespace state any subroutines of /c/ 
-- that are not already provided.
apply_bcircuit_with_bindings :: BCircuit -> (Bindings Qubit Bit) 
                             -> Circ (Bindings Qubit Bit)
apply_bcircuit_with_bindings (c,s) bindings = do
  provide_subroutines s
  apply_circuit_with_bindings c bindings

-- | Append the entire dynamic circuit /c/ to the current circuit,
-- using the given bindings, and return the new bindings.  Also, add
-- to the current namespace state any subroutines of /c/ that are not
-- already provided.
apply_dbcircuit_with_bindings :: DBCircuit a -> Bindings Qubit Bit
                                 -> Circ (Bindings Qubit Bit, a)
apply_dbcircuit_with_bindings dbcircuit bindings = do
  -- until the transformer interface is updated to work with dynamic
  -- circuits, we have to go the route of converting to a static
  -- circuit first. Unfortunately, this means that any dynamic
  -- liftings will given an error.
  let (bcircuit, a) = bcircuit_of_static_dbcircuit errmsg dbcircuit
  out_bindings <- apply_bcircuit_with_bindings bcircuit bindings
  return (out_bindings, a)
  where
    errmsg x = "apply_dbcircuit_with_bindings: operation unimplemented: " ++ x
  
-- ======================================================================
-- * Encapsulated circuits

-- | Similar to 'extract_simple', except we take the current output arity
-- of the /current/ circuit and make that the input arity of the
-- extracted circuit. Therefore, endpoints defined in the current
-- context can be used in /f/. This is a low-level operator, intended
-- for the construction of primitives, such as 'with_computed' or
-- 'with_basis_change', where the inner block can re-use some
-- variables without declaring them explicitly.
--
-- We also reuse the namespace of the current context, to avoid
-- recomputation of shared subroutines. 
-- 
-- As a special feature, also return the set of \"dirty\" wires, i.e.,
-- wires that were used during the execution of the body, but are free
-- at the end.
extract_in_context :: ErrMsg -> Circ a -> Circ (BCircuit, IntSet, a)
extract_in_context e f = do
  arity <- get_arity
  cur_namespace <- get_namespace
  let arity' = xintmap_makeclean arity
   -- f' :: Circ (a, ExtArity)
      f' = do
        set_namespace cur_namespace
        a <- f
        extarity <- get_arity
        return (a, extarity)
      (bcirc, ~(a, extarity)) = extract_simple e arity' f'
  return (bcirc, xintmap_dirty extarity, a)

-- | Intermediate between 'extract_simple' and 'extract_in_context':
-- we build the circuit in the namespace of the current circuit, to 
-- avoid recomputing any shared subroutines.
extract_in_current_namespace :: ErrMsg -> ExtArity -> Circ a -> Circ (BCircuit, a)
extract_in_current_namespace e arity f = do
  cur_namespace <- get_namespace
  return $ extract_simple e arity $ (set_namespace cur_namespace) >> f

-- | Append the 'BCircuit' to the end of the current circuit, using
-- the identity binding. This means, the input wires of 'BCircuit'
-- /must/ be endpoints in the current circuits. This typically happens
-- when 'BCircuit' was obtained from 'extract_in_context' in the
-- current context, or when 'BCircuit' is the inverse of a circuit
-- that has just been applied using 'unextract_in_context'. 
-- 
-- Note that this is a low-level function, intended for the
-- construction of user-level primitives such as 'with_computed' and
-- 'with_basis_change', and 'classical_to_reversible'. 
-- 
-- 'unextract_in_context' uses 'apply_gate' to do the appending,
-- so the current 'ControlList' and 'NoControlFlag' are respected.
-- However, it does not pass through the transformer interface, and
-- therefore low-level wire id's will be exactly preserved.
unextract_in_context :: BCircuit -> Circ ()
unextract_in_context (c,s) = do
  provide_subroutines s
  let (_,gs,_,_) = c
  mapM_ apply_gate gs

-- | Reverse an encapsulated circuit
-- 
-- An encapsulated circuit is a circuit together with data structures
-- holding the input endpoints and output endpoints.  The type of the
-- encapsulated circuit depends on the type of data in the endpoints,
-- so functions to encapsulate and unencapsulate circuits are provided
-- in "Quipper.Generic".
reverse_encapsulated :: (i, BCircuit, o) -> (o, BCircuit, i)
reverse_encapsulated (in_bind, c, out_bind) =
  (out_bind, reverse_bcircuit c, in_bind)

-- ----------------------------------------------------------------------
-- * Temporarily reserving wires

-- | Perform the computation in the body, but temporarily reserve a
-- set of wires. These wires must be initially free, and they must not
-- be used by the body (i.e., the body must respect reserved wires).
with_reserve :: IntSet -> Circ a -> Circ a
with_reserve ws body = do
  arity <- get_arity
  let arity1 = xintmap_reserves ws arity
  set_arity arity1
  a <- body
  arity2 <- get_arity            -- they should still be reserved
  let arity3 = xintmap_unreserves ws arity2
  set_arity arity3
  return a
