-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | Low-level quantum circuit implementation. This is our backend
-- implementation of quantum circuits. Note: there is no run-time
-- error checking at the moment. 
-- 
-- At its heart, a circuit is a list of gates. All well-definedness
-- checking (e.g. input arity, output arity, and checking that the
-- intermediate gates are connected to legitimate wires) is done
-- dynamically, at circuit generation time, and is not stored within
-- the circuit itself. This allows circuits to be produced and
-- consumed lazily.
-- 
-- Implementation note: this file is in the intermediate stage of a
-- code refactoring, and should be considered \"under renovation\".

module Quipper.Circuit where

-- import other Quipper stuff
import Libraries.Auxiliary

-- import other stuff
import Data.List
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Data.Typeable

-- ----------------------------------------------------------------------
-- * Quantum circuit data type

-- | Wire identifier. Wires are currently identified by an integer,
-- but the users of this interface should be oblivious to this.
type Wire = Int

-- | Wire type. A wire is either quantum or classical.
data Wiretype = Qbit -- ^ Quantum wire. 
              | Cbit -- ^ Classical wire.
              deriving (Show, Eq, Typeable)

-- | An arity, also known as a typing context, is a map from a finite
-- set of wires to wire types.
type Arity = IntMap Wiretype

-- | A signed item of type /a/. 'Signed' /x/ 'True' represents a
-- positive item, and 'Signed' /x/ 'False' represents a negative item.
-- 
-- When used with wires in a circuit, a positive sign is used to
-- represent a positive control, i.e., a filled dot, and a negative
-- sign is used to represent a negative control, i.e., an empty dot.
data Signed a = Signed a Bool
                   deriving (Show, Typeable) 
                     
-- | Extract the underlying item of a signed item.
from_signed :: Signed a -> a
from_signed (Signed a b) = a

-- | Extract the sign of a signed item: 'True' is positive, and
-- 'False' is negative.
get_sign :: Signed a -> Bool
get_sign (Signed a b) = b

-- | A list of controlled wires, possibly empty.
type Controls = [Signed Wire]

-- | A time step is a small floating point number used as a
-- parameter to certain gates, such as rotation gates or the
-- [exp −/iZt/] gate.
type Timestep = Double

-- | A flag that, if 'True', indicates that the gate is inverted.
type InverseFlag = Bool

-- | A flag that, if 'True', indicates that the gate is controllable,
-- but any further controls on the gate should be ignored. This is
-- used, e.g., for circuits consisting of a basis change, some
-- operation, and the inverse basis change. When controlling such a
-- circuit, it is sufficient to control the middle operation, so the
-- gates belonging to the basis change and its inverse will have the
-- NoControlFlag set.
type NoControlFlag = Bool

-- | A flag, to specify if the corresponding subroutine can be controlled.
-- Either no control allowed, or all controls, or only classical.
data ControllableFlag = NoCtl | AllCtl | OnlyClassicalCtl
  deriving (Eq, Ord, Show)

-- | An identifier for a subroutine. A boxed subroutine is currently
-- identified by a pair of: the user-defined name of the subroutine;
-- and a value uniquely identifying the type and shape of the argument.
-- 
-- For now, we represent the shape as a string, because this gives an
-- easy total 'Ord' instance, needed for "Data.Map". However, in
-- principle, one could also use a pair of a type representation and a
-- shape term. The implementation of this may change later.
data BoxId = BoxId String String
  deriving (Eq, Ord, Show)

-- | A flag that indicates how many times a particular subroutine
-- should be repeated. If non-zero, it implies some constraints on
-- the type of the subroutine.
data RepeatFlag = RepeatFlag Integer
                  deriving (Eq,Ord)

instance Show RepeatFlag where
  show (RepeatFlag n) = show n

-- When changing the 'Gate' datatype, also remember to update
-- 'gate_arity', 'gate_controls', and 'gate_reverse' below.

-- | The low-level representation of gates.
data Gate =
  -- Named reversible quantum gates.
  QGate String InverseFlag [Wire] [Wire] Controls NoControlFlag
    -- ^ A named reversible quantum gate: @'Qbit'^(m+n) ->
    -- 'Qbit'^(m+n)@.  The second @['Wire']@ argument should be
    -- \"generalized controls\", i.e. wires not modified by the
    -- gate. The gate type is uniquely determined by: the name, the
    -- number of inputs, and the number of generalized controls. Gates
    -- that differ in one of these respects should be regarded as
    -- different gates.
    
  | QRot String InverseFlag Timestep [Wire] [Wire] Controls NoControlFlag
    -- ^ A named reversible quantum gate that also depends on a real
    -- parameter. This is typically used for phase and rotation
    -- gates. The gate name can contain \'%\' as a place holder for
    -- the parameter, e.g., @\"exp(-i%Z)\"@. The remaining arguments
    -- are as for 'QGate'.

  -- A nullary quantum gate.
  | GPhase Timestep [Wire] Controls NoControlFlag
    -- ^ Global phase gate: @'1' -> '1'@. The list of wires is just a hint for graphical rendering.
  
  -- Some classical gates.
  | CNot Wire Controls NoControlFlag
    -- ^ Classical not: @'Cbit' -> 'Cbit'@.
  | CGate String Wire [Wire] NoControlFlag  
    -- ^ Generic classical gate @1 -> 'Cbit'@.
  | CGateInv String Wire [Wire] NoControlFlag  
    -- ^ Uncompute classical gate @'Cbit' -> 1@, asserting that the
    -- classical bit is in the state specified by the corresponding
    -- 'CGate'.
  | CSwap Wire Wire Controls NoControlFlag
    -- ^ Classical swap gate: @'Cbit' * 'Cbit' -> 'Cbit' * 'Cbit'@.

  -- Initialization and assertive termination.
  | QPrep Wire NoControlFlag
    -- ^ Initialization: @'Cbit' -> 'Qbit'@.
  | QUnprep Wire NoControlFlag
    -- ^ Measurement @'Qbit' -> 'Cbit'@ with an assertion that the
    -- qubit is already in a computational basis state. This kind of
    -- measurement loses no information, and is formally the inverse
    -- of 'QPrep'.
  | QInit Bool Wire NoControlFlag  
    -- ^ Initialization: @'Bool' -> 'Qbit'@. 
  | CInit Bool Wire NoControlFlag  
    -- ^ Initialization: @'Bool' -> 'Cbit'@. 
  | QTerm Bool Wire NoControlFlag  
    -- ^ Termination of a 'Qbit' wire with assertion
    -- that the qubit is in the specified state:
    -- @'Qbit' * 'Bool' -> 1@.
  | CTerm Bool Wire NoControlFlag  
    -- ^ Termination of a 'Cbit' wire with assertion
    -- that the bit is in the specified state:
    -- @'Cbit' * 'Bool' -> 1@.
  
  -- Measurement.
  | QMeas Wire
    -- ^ Measurement: @'Qbit' -> 'Cbit'@.
  | QDiscard Wire    
    -- ^ Termination of a 'Qbit' wire without
    -- assertion: @'Qbit' -> 1@
  | CDiscard Wire    
    -- ^ Termination of a 'Cbit' wire without
    -- assertion: @'Cbit' -> 1@

  -- Dynamic termination.
  | DTerm Bool Wire 
    -- ^ Termination of a 'Cbit' wire, with a comment indicating what
    -- the observed state of that wire was. This is typically inserted
    -- in a circuit after a dynamic lifting is performed. Unlike
    -- 'CTerm', this is in no way an assertion, but simply a record of
    -- observed behavior during a particular run of the algorithm.

  -- Subroutines.
  | Subroutine BoxId InverseFlag [Wire] Arity [Wire] Arity Controls NoControlFlag ControllableFlag RepeatFlag
    -- ^ Reference to a subroutine, assumed to be bound to another
    -- circuit. Arbitrary input and output arities. The domain of /a1/
    -- must include the range of /ws1/, and similarly for /a2/ and /ws2/.

  -- Comments.
  | Comment String InverseFlag [(Wire,String)]
    -- ^ A comment. Does nothing, but can be useful for marking a
    -- location or some wires in a circuit.

    deriving Show

-- ----------------------------------------------------------------------
-- * Basic information about gates

-- The following functions must be updated each time the 'Gate' data
-- type is changed.

-- | Compute the incoming and outgoing wires of a given gate
-- (excluding controls, comments, and anchors). This essentially
-- encodes the type information of the basic gates. If a wire is used
-- multiple times as an input or output, then 'gate_arity' also
-- returns it multiple times; this enables run-time type checking.
-- 
-- Note that 'gate_arity' returns the /logical/ wires, and therefore
-- excludes things like labels, comments, and graphical anchors. This
-- is in contrast to 'wires_of_gate', which returns the /syntactic/
-- set of wires used by the gate.
gate_arity :: Gate -> ([(Wire, Wiretype)], [(Wire, Wiretype)])
gate_arity (QGate n inv ws1 ws2 c ncf) = (map (\w -> (w,Qbit)) (ws1 ++ ws2) ,map (\w -> (w,Qbit)) (ws1 ++ ws2))
gate_arity (QRot n inv t ws1 ws2 c ncf) = (map (\w -> (w,Qbit)) (ws1 ++ ws2) ,map (\w -> (w,Qbit)) (ws1 ++ ws2))
gate_arity (GPhase t w c ncf) = ([], [])
gate_arity (CNot w c ncf) = ([(w, Cbit)], [(w, Cbit)])
gate_arity (CGate n w ws ncf) = (cs, (w, Cbit) : cs)
  where cs = map (\x -> (x, Cbit)) ws
gate_arity (CGateInv n w ws ncf) = ((w, Cbit) : cs, cs)
  where cs = map (\x -> (x, Cbit)) ws
gate_arity (CSwap w1 w2 c ncf) = ([(w1, Cbit), (w2, Cbit)], [(w1, Cbit), (w2, Cbit)])
gate_arity (QPrep w ncf) = ([(w, Cbit)], [(w, Qbit)])
gate_arity (QUnprep w ncf) = ([(w, Qbit)], [(w, Cbit)])
gate_arity (QInit b w ncf) = ([], [(w, Qbit)])
gate_arity (CInit b w ncf) = ([], [(w, Cbit)])
gate_arity (QTerm b w ncf) = ([(w, Qbit)], [])
gate_arity (CTerm b w ncf) = ([(w, Cbit)], [])
gate_arity (QMeas w) = ([(w, Qbit)], [(w, Cbit)])
gate_arity (QDiscard w) = ([(w, Qbit)], [])
gate_arity (CDiscard w) = ([(w, Cbit)], [])
gate_arity (DTerm b w) = ([(w, Cbit)], [])
gate_arity (Subroutine n inv ws1 a1 ws2 a2 c ncf ctrble _) = (getTypes ws1 a1, getTypes ws2 a2)
  where getTypes ws a = map (\n -> (n, fromJust (IntMap.lookup n a))) ws
gate_arity (Comment s inv ws) = ([], [])

-- | Return the controls of a gate (or an empty list if the gate has
-- no controls).
gate_controls :: Gate -> Controls
gate_controls (QGate n inv ws1 ws2 c ncf) = c
gate_controls (QRot n inv t ws1 ws2 c ncf) = c
gate_controls (GPhase t w c ncf) = c
gate_controls (CNot w c ncf) = c
gate_controls (CGate n w ws ncf) = []
gate_controls (CGateInv n w ws ncf) = []
gate_controls (CSwap w1 w2 c ncf) = c
gate_controls (QPrep w ncf) = []
gate_controls (QUnprep w ncf) = []
gate_controls (QInit b w ncf) = []
gate_controls (CInit b w ncf) = []
gate_controls (QTerm b w ncf) = []
gate_controls (CTerm b w ncf) = []
gate_controls (QMeas w) = []
gate_controls (QDiscard w) = []
gate_controls (CDiscard w) = []
gate_controls (DTerm b w) = []
gate_controls (Subroutine n inv ws1 a1 ws2 a2 c ncf ctrble _) = c
gate_controls (Comment s inv ws) = []

-- | Return the 'NoControlFlag' of a gate, or 'False' if it doesn't have one.
gate_ncflag :: Gate -> NoControlFlag
gate_ncflag (QGate n inv ws1 ws2 c ncf) = ncf
gate_ncflag (QRot n inv t ws1 ws2 c ncf) = ncf
gate_ncflag (GPhase t w c ncf) = ncf
gate_ncflag (CNot w c ncf) = ncf
gate_ncflag (CGate n w ws ncf) = ncf
gate_ncflag (CGateInv n w ws ncf) = ncf
gate_ncflag (CSwap w1 w2 c ncf) = ncf
gate_ncflag (QPrep w ncf) = ncf
gate_ncflag (QUnprep w ncf) = ncf
gate_ncflag (QInit b w ncf) = ncf
gate_ncflag (CInit b w ncf) = ncf
gate_ncflag (QTerm b w ncf) = ncf
gate_ncflag (CTerm b w ncf) = ncf
gate_ncflag (Subroutine n inv ws1 a1 ws2 a2 c ncf ctrble _) = ncf
-- The remaining gates don't have a 'NoControlFlag'. We list them
-- explicitly, so that the typechecker can warn us about new gates
-- that must be added here.
gate_ncflag (QMeas _) = False
gate_ncflag (QDiscard _) = False
gate_ncflag (CDiscard _) = False
gate_ncflag (DTerm _ _) = False
gate_ncflag (Comment _ _ _) = False


-- | Apply the given 'NoControlFlag' to the given 'Gate'. This means,
-- if the first parameter is 'True', set the gate's 'NoControlFlag',
-- otherwise do nothing. Throw an error if attempting to set the
-- 'NoControlFlag' on a gate that can't support this flag.
gate_with_ncflag :: NoControlFlag -> Gate -> Gate
gate_with_ncflag False gate = gate
gate_with_ncflag True (QGate n inv ws1 ws2 c _) = (QGate n inv ws1 ws2 c True)
gate_with_ncflag True (QRot n inv t ws1 ws2 c _) = (QRot n inv t ws1 ws2 c True)
gate_with_ncflag True (GPhase t w c _) = (GPhase t w c True)
gate_with_ncflag True (CNot w c _) = (CNot w c True)
gate_with_ncflag True (CGate n w ws _) = (CGate n w ws True)
gate_with_ncflag True (CGateInv n w ws _) = (CGateInv n w ws True)
gate_with_ncflag True (CSwap w1 w2 c _) = (CSwap w1 w2 c True)
gate_with_ncflag True (QPrep w _) = (QPrep w True)
gate_with_ncflag True (QUnprep w _) = (QUnprep w True)
gate_with_ncflag True (QInit b w _) = (QInit b w True)
gate_with_ncflag True (CInit b w _) = (CInit b w True)
gate_with_ncflag True (QTerm b w _) = (QTerm b w True)
gate_with_ncflag True (CTerm b w _) = (CTerm b w True)
gate_with_ncflag True (Subroutine n inv ws1 a1 ws2 a2 c _ ctrble repeat) = (Subroutine n inv ws1 a1 ws2 a2 c True ctrble repeat)
gate_with_ncflag True (Comment s inv ws) = (Comment s inv ws)
-- The remaining gates can't have their 'NoControlFlag' set. We list
-- them explicitly, so that the typechecker can warn us about new
-- gates that must be added here.
gate_with_ncflag True g@(QMeas _) = 
  error ("gate " ++ show g ++ " can't be used in a without_controls context")
gate_with_ncflag True g@(QDiscard _) = 
  error ("gate " ++ show g ++ " can't be used in a without_controls context")
gate_with_ncflag True g@(CDiscard _) = 
  error ("gate " ++ show g ++ " can't be used in a without_controls context")
gate_with_ncflag True g@(DTerm _ _) = 
  error ("gate " ++ show g ++ " can't be used in a without_controls context")

-- | Reverse a gate. Throw an error if the gate is not reversible.
gate_reverse :: Gate -> Gate
gate_reverse (QGate n inv ws1 ws2 c ncf) = QGate n (not inv) ws1 ws2 c ncf
gate_reverse (QRot n inv t ws1 ws2 c ncf) = QRot n (not inv) t ws1 ws2 c ncf
gate_reverse (GPhase t w c ncf) = GPhase (-t) w c ncf
gate_reverse (CNot w c ncf) = CNot w c ncf
gate_reverse (CGate n w ws ncf) = CGateInv n w ws ncf
gate_reverse (CGateInv n w ws ncf) = CGate n w ws ncf
gate_reverse (CSwap w1 w2 c ncf) = CSwap w1 w2 c ncf
gate_reverse (QPrep w ncf) = QUnprep w ncf
gate_reverse (QUnprep w ncf) = QPrep w ncf
gate_reverse (QInit b w ncf) = QTerm b w ncf
gate_reverse (CInit b w ncf) = CTerm b w ncf
gate_reverse (QTerm b w ncf) = QInit b w ncf
gate_reverse (CTerm b w ncf) = CInit b w ncf
gate_reverse (Subroutine name inv ws1 a1 ws2 a2 c ncf ctrble repeat) = Subroutine name (not inv) ws2 a2 ws1 a1 c ncf ctrble repeat
gate_reverse (Comment s inv ws) = Comment s (not inv) ws
-- The remaining gates are not reversible. We list them explicitly, so
-- that the typechecker can warn us about new gates that must be added
-- here.
gate_reverse g@(QMeas _) = error ("gate_reverse: gate not reversible: " ++ show g)
gate_reverse g@(QDiscard _) = error ("gate_reverse: gate not reversible: " ++ show g)
gate_reverse g@(CDiscard _) = error ("gate_reverse: gate not reversible: " ++ show g)
gate_reverse g@(DTerm _ _) = error ("gate_reverse: gate not reversible: " ++ show g)

-- ----------------------------------------------------------------------
-- * Auxiliary functions on gates and wires

-- | Return the set of wires used by a list of controls.
wires_of_controls :: Controls -> IntSet
wires_of_controls c = IntSet.fromList (map from_signed c)

-- | Return the set of wires used by a gate (including controls,
-- labels, and anchors). 
-- 
-- Unlike 'gate_arity', the function 'wires_of_gate' is used for
-- printing, and therefore returns all wires that are syntactically
-- used by the gate, irrespective of whether they have a logical
-- meaning.
wires_of_gate :: Gate -> IntSet
wires_of_gate (Comment s inv ws) = 
  intset_inserts (map fst ws) (IntSet.empty)
wires_of_gate (GPhase t w c ncf) = 
  intset_inserts w (wires_of_controls c)
wires_of_gate g = intset_inserts w1 (intset_inserts w2 (wires_of_controls c))
  where
    (a1, a2) = gate_arity g
    c = gate_controls g
    w1 = map fst a1
    w2 = map fst a2

-- | Like 'wires_of_gate', except return a list of wires.
wirelist_of_gate :: Gate -> [Wire]
wirelist_of_gate g = IntSet.toList (wires_of_gate g)

-- ----------------------------------------------------------------------
-- * Dynamic arities

-- | Recall that an 'Arity' is a set of typed wires, and it determines
-- the external interfaces at which circuits and gates can be
-- connected.  The type 'ExtArity' stores the same information as the
-- type 'Arity', but in a format that is more optimized for efficient
-- updating. Additionally, it also stores the set of wires ever used.

type ExtArity = XIntMap Wiretype

-- | Check whether the given gate is well-formed and can be legally
-- applied in the context of the given arity. If successful, return
-- the updated arity resulting from the gate application. If
-- unsuccessful, raise an error. Properties checked are:
-- 
-- * that each gate has non-overlapping inputs, including controls;
-- 
-- * that each gate has non-overlapping outputs, including controls;
-- 
-- * that the inputs of the gate (including controls) are actually
-- present in the current arity; 
-- 
-- * that the types of the inputs (excluding controls) match those of
-- the current arity;
-- 
-- * that the outputs of the gate (excluding controls) don't conflict
-- with any wires already existing in the current arity.

arity_append_safe :: Gate -> ExtArity -> ExtArity
arity_append_safe gate a0 = 
  case (err0, err1, err2, err3, err4) of
    (True, _, _, _, _) -> 
      error $ "Gate error: duplicate inputs in " ++ show gate
    (_, True, _, _, _) -> 
      error $ "Gate error: duplicate outputs in " ++ show gate
    (_, _, Just w, _, _) ->
      error $ "Gate application error: no such wire " ++ show w ++ ": " ++ show gate
    (_, _, _, Just (w,t), _) ->
      error $ "Gate application error: wire " ++ show w ++ ":" ++ show t ++ " has wrong type " ++ show t' ++ ": " ++ show gate
      where
        Just t' = xintmap_lookup w a0
    (_, _, _, _, Just w) ->
      error $ "Gate application error: wire " ++ show w ++ " already exists: " ++ show gate
    _ -> a2
  where
    (win, wout) = gate_arity gate
    c_ids = map from_signed (gate_controls gate)
    win_ids = map fst win
    wout_ids = map fst wout
    err0 = has_duplicates (win_ids ++ c_ids)
    err1 = has_duplicates (wout_ids ++ c_ids)
    err2 = find (\w -> not $ xintmap_member w a0) (win_ids ++ c_ids)
    err3 = find (\(w,t) -> not $ xintmap_lookup w a0 == Just t) win
    err4 = find (\w -> xintmap_member w a1) wout_ids
    a1 = xintmap_deletes win_ids a0
    a2 = xintmap_inserts wout a1

-- | Like 'arity_append', but without type checking. This is
-- potentially faster, but should only used in applications that have
-- already been thoroughly tested or type-checked.
arity_append_unsafe :: Gate -> ExtArity -> ExtArity
arity_append_unsafe gate a0 = a2
  where
    (win, wout) = gate_arity gate
    a1 = xintmap_deletes (map fst win) a0    
    a2 = xintmap_inserts wout a1

-- | For now, we disable run-time type checking, because we have not
-- yet implemented run-time types properly. Therefore, we define
-- 'arity_append' to be a synonym for 'arity_append_unsafe'.
arity_append :: Gate -> ExtArity -> ExtArity
arity_append = arity_append_unsafe

-- | Return an empty arity.
arity_empty :: ExtArity
arity_empty = xintmap_empty

-- | Return a wire unused in the current arity.
arity_unused_wire :: ExtArity -> Wire
arity_unused_wire = xintmap_freshkey

-- | Return the next /k/ wires unused in the current arity.
arity_unused_wires :: Int -> ExtArity -> [Wire]
arity_unused_wires = xintmap_freshkeys

-- | Add a new typed wire to the current arity. This returns a new
-- wire and the updated arity.
arity_alloc :: Wiretype -> ExtArity -> (Wire, ExtArity)
arity_alloc t arity = (w, arity') where
  w = xintmap_freshkey arity
  arity' = xintmap_insert w t arity

-- | Convert an extended arity to an ordinary arity.
arity_of_extarity :: ExtArity -> Arity
arity_of_extarity = xintmap_to_intmap

-- | Return the smallest wire id nowhere used in the circuit.
n_of_extarity :: ExtArity -> Int
n_of_extarity = xintmap_size

-- ----------------------------------------------------------------------
-- * Circuit abstraction

-- | A completed circuit /(a1,gs,a2,n)/ has an input arity /a1/, a
-- list of gates /gs/, and an output arity /a2/.  We also record /n/,
-- the total number of wires used by the circuit. Because wires are
-- allocated consecutively, this means that the wire id's used are
-- [0../n/-1].
type Circuit = (Arity, [Gate], Arity, Int)

-- | Return the set of all the wires in a circuit.
wirelist_of_circuit :: Circuit -> [Wire]
wirelist_of_circuit (_, _, _, n) = [0..n-1]

-- ----------------------------------------------------------------------
-- ** Reversing low-level circuits

-- | Reverse a gate list.
reverse_gatelist :: [Gate] -> [Gate]
reverse_gatelist gates = reverse (map gate_reverse gates)

-- | Reverse a circuit. Throw an error if the circuit is not reversible.
reverse_circuit :: Circuit -> Circuit
reverse_circuit (a1, gates, a2, n) = (a2, reverse_gatelist gates, a1, n)

-- ----------------------------------------------------------------------
-- ** NoControlFlag on low-level circuits

-- | Set the 'NoControlFlag' on all gates of a circuit.
circuit_to_nocontrol :: Circuit -> Circuit
circuit_to_nocontrol (a1, gates, a2, n) = (a1, gates', a2, n) where
  gates' = map (gate_with_ncflag True) gates

-- ----------------------------------------------------------------------
-- ** Ordered circuits

-- | An ordered circuit is a 'Circuit' together with an ordering on
-- (usually all, but potentially a subset of) the input and output
-- endpoints.
--
-- This extra information is required when a circuit is used within a
-- larger circuit (e.g. via a 'Subroutine' gate), to identify which wires
-- of the sub-circuit should be bound to which wires of the surrounding 
-- circuit.
newtype OCircuit = OCircuit ([Wire], Circuit, [Wire])

-- | Reverse an 'OCircuit'. Throw an error if the circuit is not reversible.
reverse_ocircuit :: OCircuit -> OCircuit
reverse_ocircuit (OCircuit (ws_in, circ, ws_out)) = OCircuit (ws_out, reverse_circuit circ, ws_out) 

-- ----------------------------------------------------------------------
-- ** Annotated circuits

-- | One often wants to consider the inputs and outputs of a circuit as
-- more structured/typed than just lists of bits/qubits; for instance,
-- a list of six qubits could be structured as a pair of triples, or a 
-- triple of pairs, or a six-bit 'QDInt'.
--
-- While for the most part this typing information is not included in 
-- low-level circuits, we need to consider it in hierarchical circuits,
-- so that the information stored in a subroutine is sufficient to call
-- the subroutine in a typed context.
--
-- Specifically, the extra information needed consists of functions to
-- destructure the input/output data as a list of typed wires, and 
-- restructure such a list of wires into a piece of data of the appropriate
-- type. 
data CircuitTypeStructure a = CircuitTypeStructure (a -> ([Wire],Arity)) (([Wire],Arity) -> a)
  deriving (Typeable)

-- | The trivial 'CircuitTypeStructure' on @(['Wire'],'Arity')@.
id_CircuitTypeStructure :: CircuitTypeStructure ([Wire],Arity)
id_CircuitTypeStructure = CircuitTypeStructure id id

-- | Use a 'CircuitTypeStructure' to destructure a piece of (suitably
-- typed) data into a list of typed wires.
destructure_with :: CircuitTypeStructure a -> a -> ([Wire],Arity)
destructure_with (CircuitTypeStructure f _) = f

-- | Use a 'CircuitTypeStructure' to structure a list of typed wires 
-- (of the appropriate length/arity) into a piece of structured data.
structure_with :: CircuitTypeStructure a -> ([Wire],Arity) -> a
structure_with (CircuitTypeStructure _ g) = g

-- ======================================================================
-- * Boxed circuits

-- | A typed subroutine consists of:
--
-- * a low-level circuit, ordered to allow binding of incoming and outgoing wires;
--
-- * functions for structuring/destructuring the inputs and outputs to and 
-- from lists of wires (these functions being dynamically typed, since the 
-- input/output type may vary between subroutines);
--
-- * a 'ControllableFlag', recording whether the circuit is controllable.
data TypedSubroutine = forall a b. (Typeable a, Typeable b) =>
  TypedSubroutine OCircuit (CircuitTypeStructure a) (CircuitTypeStructure b) ControllableFlag

-- | Extract just the 'Circuit' from a 'TypedSubroutine'.
circuit_of_typedsubroutine :: TypedSubroutine -> Circuit
circuit_of_typedsubroutine (TypedSubroutine (OCircuit (_,circ,_)) _ _ _) = circ

-- | A name space is a map from names to subroutine bindings.  These
-- subroutines can reference each other; it is the programmer’s
-- responsibility to ensure there is no circular dependency, and no
-- clash of names.
type Namespace = Map BoxId TypedSubroutine

-- | The empty namespace.
namespace_empty :: Namespace
namespace_empty = Map.empty

-- | A function to display the names of all the subroutines in a 'Namespace'.
showNames :: Namespace -> String
showNames ns = show (map (\(n,_) -> n) (Map.toList ns))

-- | A boxed circuit is a distinguished simple circuit (analogous to a “main” function) together with a namespace. 
type BCircuit = (Circuit,Namespace)

-- ----------------------------------------------------------------------
-- ** Ordered circuits

-- | An ordered boxed circuit is a 'BCircuit' together with an
-- ordering on the input and output endpoints, or equivalently, an
-- 'OCircuit' together with a namespace.
type OBCircuit = (OCircuit,Namespace)

-- | Construct an 'OBCircuit' from a 'BCircuit' and an ordering on the
-- input and output endpoints.
ob_circuit :: [Wire] -> BCircuit -> [Wire] -> OBCircuit
ob_circuit w_in (circ, ns) w_out = (OCircuit (w_in, circ, w_out), ns)

-- ======================================================================
-- ** Basic functions lifted to boxed circuits

-- All the basic functions defined on simple circuits now lift
-- trivially to boxed circuits:
 
-- | Reverse a simple boxed circuit, or throw an error if not reversible.
reverse_bcircuit :: BCircuit -> BCircuit
reverse_bcircuit (c,s) = (reverse_circuit c,s)

-- ----------------------------------------------------------------------
-- * The ReadWrite monad

-- $ The 'ReadWrite' monad encapsulates the interaction with a (real
-- or simulated) low-level quantum device.

-- | The 'ReadWrite' monad describes a standard read-write computation,
-- here specialized to the case where writes are 'Gate's, prompts are
-- 'Bit's, and reads are 'Bool's. Thus, a read-write computation can
-- do three things:
-- 
-- * terminate with a result. This is the case 'RW_Return'.
-- 
-- * write a single 'Gate' and continue. This is the case 'RW_Write'.
-- 
-- * issue a prompt, which is a 'Wire', then read a 'Bool', then
-- continue. This is the case 'RW_Read'.
data ReadWrite a = RW_Return a
                 | RW_Write !Gate (ReadWrite a)
                 | RW_Read !Wire (Bool -> ReadWrite a)
                 | RW_Subroutine BoxId TypedSubroutine (ReadWrite a)

instance Monad ReadWrite where
  return a = RW_Return a
  f >>= g = case f of
    RW_Return a -> g a
    RW_Write gate f' -> RW_Write gate (f' >>= g)
    RW_Read bit cont -> RW_Read bit (\bool -> cont bool >>= g)
    RW_Subroutine name subroutine f' -> RW_Subroutine name subroutine (f' >>= g)

-- | Transforms a read-write computation into one that behaves identically,
-- but also returns the list of gates generated.
-- 
-- This is used as a building block, for example to allow a read-write
-- computation to be run in a simulator while simultaneously using a
-- static backend to print the list of generated gates.
readwrite_wrap :: ReadWrite a -> ReadWrite ([Gate], a)
readwrite_wrap (RW_Return a) = do
  RW_Return ([], a)
readwrite_wrap (RW_Write gate comp) = do
  ~(gates, a) <- readwrite_wrap comp
  RW_Write gate (return (gate:gates, a))
readwrite_wrap (RW_Read bit cont) = do
  RW_Read bit (\bool -> readwrite_wrap (cont bool))
readwrite_wrap (RW_Subroutine name subroutine comp) =
  RW_Subroutine name subroutine (readwrite_wrap comp)

-- | Extract the contents of a static 'ReadWrite' computation. A
-- 'ReadWrite' computation is said to be static if it contains no
-- 'RW_Read' instructions, or in other words, no dynamic lifting.  If
-- an 'RW_Read' instruction is encountered, issue an error message
-- using the given stub.
readwrite_unwind_static :: ErrMsg -> ReadWrite a -> a
readwrite_unwind_static e (RW_Return a) = a
readwrite_unwind_static e (RW_Write gate comp) = readwrite_unwind_static e comp
readwrite_unwind_static e (RW_Read bit cont) = error $ e "dynamic lifting"
readwrite_unwind_static e (RW_Subroutine name subroutine comp) = readwrite_unwind_static e comp

-- | Turn a static read-write computation into a list of gates, while
-- also updating a namespace. \"Static\" means that the computation
-- may not contain any 'RW_Read' operations. If it does, the message
-- \"dynamic lifting\" is passed to the given error handler.
-- 
-- Important usage note: This function returns a triple (/gates/,
-- /ns/, /x/). The list of gates is generated lazily, and can be
-- consumed one gate at a time. However, the values /ns/ and /x/ are
-- only computed at the end of the computation. Any function using
-- them should not apply a strict pattern match to /ns/ or /x/, or
-- else the whole list of gates will be generated in memory. For
-- example, the following will blow up the memory:
-- 
-- > (gates, ns, (a, n, x)) = gatelist_of_readwrite errmsg comp
-- 
-- whereas the following will work as intended:
-- 
-- > (gates, ns, ~(a, n, x)) = gatelist_of_readwrite errmsg comp
gatelist_of_readwrite :: ErrMsg -> ReadWrite a -> Namespace -> ([Gate], Namespace, a)
gatelist_of_readwrite e (RW_Return a) ns = ([], ns, a)
gatelist_of_readwrite e (RW_Write gate comp) ns = (gate : gates, ns', a) where
  (gates, ns', a) = gatelist_of_readwrite e comp ns
gatelist_of_readwrite e (RW_Read bit cont) ns = error (e "dynamic lifting")
gatelist_of_readwrite e (RW_Subroutine name subroutine comp) ns = 
  let ns' = map_provide name subroutine ns in
  gatelist_of_readwrite e comp ns'

{-
  -- This version is inefficient. Why?
  gatelist_of_readwrite_xxx :: ErrMsg -> ReadWrite a -> ([Gate], a)
  gatelist_of_readwrite_xxx e comp = 
    readwrite_unwind_static e (readwrite_wrap comp)
-}

-- ----------------------------------------------------------------------
-- * Dynamic boxed circuits

-- | The type of dynamic boxed circuits. The type 'DBCircuit' /a/ is
-- the appropriate generalization of ('BCircuit', /a/), in a setting
-- that is dynamic rather than static (i.e., with dynamic lifting or
-- \"interactive measurement\").
type DBCircuit a = (Arity, ReadWrite (Arity, Int, a))

-- | Convert a dynamic boxed circuit to a static boxed circuit. The
-- dynamic boxed circuit may not contain any dynamic liftings, since
-- these cannot be performed in a static setting. In case any output
-- liftings are encountered, try to issue a meaningful error via the
-- given stub error message.
bcircuit_of_static_dbcircuit :: ErrMsg -> DBCircuit a -> (BCircuit, a)
bcircuit_of_static_dbcircuit e dbcirc = (bcirc, x) where
  (a0, comp) = dbcirc
  bcirc = (circ, ns)
  circ = (a0, gates, a1, n)
  (gates, ns, ~(a1, n, x)) = gatelist_of_readwrite e comp namespace_empty

-- | Convert a boxed circuit to a dynamic boxed circuit. The latter,
-- of course, contains no 'RW_Read' instructions.
dbcircuit_of_bcircuit :: BCircuit -> a -> DBCircuit a
dbcircuit_of_bcircuit bcircuit x = (a0, comp (Map.toList ns) gates) where
  (circuit, ns) = bcircuit
  (a0, gates, a1, n) = circuit
  comp ((boxid,subroutine):ns) gs = RW_Subroutine boxid subroutine (comp ns gs)
  comp [] [] = RW_Return (a1, n, x)
  comp [] (g:gs) = RW_Write g (comp [] gs)
