-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Some gates can be controlled by a condition involving one of more
-- \"control\" qubits and/or classical bits at circuit execution time.
-- Such gates can also be controlled by boolean conditions that are
-- known at circuit generation time (in which case the gate will not
-- be generated when the control condition is false). This
-- "Quipper.Control" module provides some convenient functions for
-- creating and updating such controls.

module Quipper.Control where

import Quipper.Circuit
import Libraries.Tuple

import Data.Map (Map)
import qualified Data.Map as Map

-- ======================================================================
-- * The type of controls

-- $ In the most general case, a \"control\" could be an arbitrary
-- boolean formula built up from assertions of the form /q/ = |0〉 or
-- /q/ = |1〉, where /q/ is either a qubit or a classical bit in a
-- circuit. However, we are here interested in tracking a simpler kind
-- of control.
-- 
-- A /control list/ is a conjunction (i.e., an \"and\") of assertions
-- of the form /q/ = |0〉 or /q/ = |1〉. A special case arises when the
-- conjunction involves two mutually exclusive conditions, such as /q/
-- = |0〉 and /q/ = |1〉. In this case, the control in inconsistent: it
-- can never be active. We use a special representation for the
-- inconsistent control for efficiency reasons.
-- 
-- Implementation note: a 'ControlList' is either 'Inconsistent', or
-- else a map from a finite set of wires to booleans.  Here, the
-- boolean 'True' represents a positive control, i.e., one that is
-- active when the state is |1〉 (a filled dot in circuit
-- diagrams). The boolean 'False' represents a negative control, i.e.,
-- on that is active when the state is |0〉 (an empty dot in circuit
-- diagrams).

-- | A 'ControlList' is Quipper's internal representation of the type
-- of conjunctive controls, i.e., controls that can be constructed
-- using the '.==.', './=.', and '.&&.' operators.

data ControlList =
  ControlList (Map Wire Bool)
  | Inconsistent
  deriving (Show)

-- ----------------------------------------------------------------------
-- * Functions for combining control lists
  
-- $FUNCTIONS We provide some convenient functions for building
-- control lists from simpler control lists.
  
-- | The empty control list, corresponding to a condition that is
-- always true.
clist_empty :: ControlList
clist_empty = ControlList Map.empty

-- | Add a single signed control to a control list.
clist_add :: Wire -> Bool -> ControlList -> ControlList
clist_add w b Inconsistent = Inconsistent
clist_add w b (ControlList m) =
  case Map.lookup w m of
    Just b' | b /= b' -> Inconsistent
    _ -> ControlList (Map.insert w b m)
  
-- | @combine list1 list2@: 
-- Take the conjunction of two control lists. This is more efficient
-- if /list1/ is small and /list2/ is large.
combine :: ControlList -> ControlList -> ControlList
combine Inconsistent list2 = Inconsistent
combine (ControlList m) list2 = 
  Map.foldrWithKey clist_add list2 m

-- | Like 'combine', but the first argument is of type 'Controls' from
-- the "Quipper.Circuit" module.
combine_controls :: Controls -> ControlList -> ControlList
combine_controls c list2 =
  foldl (\list (Signed w b) -> clist_add w b list) list2 c

-- | Like 'combine_controls', but also return a value of type
-- 'Controls', or 'Nothing' if the controls are inconsistent.
-- This function is for convenience.
add_to_controls :: Controls -> ControlList -> Maybe Controls
add_to_controls c clist =
  case combine_controls c clist of
    Inconsistent -> Nothing
    ControlList m -> Just [ Signed w b | (w,b) <- Map.toList m ]

-- ----------------------------------------------------------------------
-- * Controlling low-level gates

-- | Modify the given gate by applying the specified controls. If the
-- total set of controls (i.e., those specified in the gate itself and
-- those specified in the control list) is inconsistent, return
-- 'Nothing'. If it is consistent, return the appropriately controlled
-- version of the gate. Throw an error if the gate is of a kind that
-- cannot be controlled.
control_gate :: ControlList -> Gate -> Maybe Gate
control_gate clist (QGate name inv ws1 ws2 c ncf) =
  case add_to_controls c clist of
    Nothing -> Nothing
    Just c1 -> Just (QGate name inv ws1 ws2 c1 ncf)
control_gate clist (QRot name inv t ws1 ws2 c ncf) =
  case add_to_controls c clist of
    Nothing -> Nothing
    Just c1 -> Just (QRot name inv t ws1 ws2 c1 ncf)
control_gate clist (GPhase t w c ncf) =
  case add_to_controls c clist of
    Nothing -> Nothing
    Just c1 -> Just (GPhase t w c1 ncf)
control_gate clist (CNot w c ncf) =
  case add_to_controls c clist of
    Nothing -> Nothing
    Just c1 -> Just (CNot w c1 ncf)
control_gate clist (CSwap w1 w2 c ncf) =
  case add_to_controls c clist of
    Nothing -> Nothing
    Just c1 -> Just (CSwap w1 w2 c1 ncf)
control_gate clist (Subroutine name inv ws1 a1 ws2 a2 c ncf AllCtl repeat) =
  case add_to_controls c clist of
    Nothing -> Nothing
    Just c1 -> Just (Subroutine name inv ws1 a1 ws2 a2 c1 ncf AllCtl repeat)
control_gate clist (Subroutine name inv ws1 a1 ws2 a2 c ncf OnlyClassicalCtl repeat) =
  case add_to_controls c clist of
    Nothing -> Nothing
    Just c1 -> Just (Subroutine name inv ws1 a1 ws2 a2 c1 ncf OnlyClassicalCtl repeat)
control_gate clist (Comment s inv ws) = Just (Comment s inv ws)
-- Implementation note: we list all catch-all cases explicitly, so
-- that the typechecker can warn about new gates that must be added
-- here.
control_gate clist gate@(CGate _ _ _ _)    = control_gate_catch_all clist gate
control_gate clist gate@(CGateInv _ _ _ _) = control_gate_catch_all clist gate
control_gate clist gate@(QPrep _ _)        = control_gate_catch_all clist gate
control_gate clist gate@(QUnprep _ _)      = control_gate_catch_all clist gate
control_gate clist gate@(QInit _ _ _)      = control_gate_catch_all clist gate
control_gate clist gate@(CInit _ _ _)      = control_gate_catch_all clist gate
control_gate clist gate@(QTerm _ _ _)      = control_gate_catch_all clist gate
control_gate clist gate@(CTerm _ _ _)      = control_gate_catch_all clist gate
control_gate clist gate@(QMeas _)          = control_gate_catch_all clist gate
control_gate clist gate@(QDiscard _)       = control_gate_catch_all clist gate
control_gate clist gate@(CDiscard _)       = control_gate_catch_all clist gate
control_gate clist gate@(DTerm _ _)        = control_gate_catch_all clist gate
control_gate clist gate@(Subroutine _ _ _ _ _ _ _ _ NoCtl _) = control_gate_catch_all clist gate

-- | The \"catch all\" clause for 'control_gate'. This handles all
-- gates that are not controllable. If the control condition is known
-- at circuit generation time to be 'clist_empty', then we can just
-- append the gate unconditionally. All other cases are errors.
control_gate_catch_all :: ControlList -> Gate -> Maybe Gate
control_gate_catch_all clist gate =
  case clist of
    ControlList m | Map.null m -> Just gate
    _ -> error ("control_gate: gate can't be controlled: " ++ show gate)

-- | Define whether a gate can be controlled.
controllable_gate :: Gate -> Bool
controllable_gate (QGate name inv ws1 ws2 c ncf) = True
controllable_gate (QRot name inv t ws1 ws2 c ncf) = True
controllable_gate (GPhase t w c ncf) = True
controllable_gate (CNot w c ncf) = True
controllable_gate (CSwap w1 w2 c ncf) = True
controllable_gate (Subroutine name inv ws1 a1 ws2 a2 c ncf AllCtl _) = True
controllable_gate (Subroutine name inv ws1 a1 ws2 a2 c ncf OnlyClassicalCtl _) = True
controllable_gate (Comment s inv ws) = True
-- Catch-all clauses: The remaining gates are not controllable, unless
-- they have their 'NoControlFlag' set. We list all catch-all cases
-- explicitly, so that the typechecker can warn about new gates that
-- must be added here.
controllable_gate gate@(CGate _ _ _ _) = gate_ncflag gate
controllable_gate gate@(CGateInv _ _ _ _) = gate_ncflag gate
controllable_gate gate@(QPrep _ _) = gate_ncflag gate
controllable_gate gate@(QUnprep _ _) = gate_ncflag gate
controllable_gate gate@(QInit _ _ _) = gate_ncflag gate
controllable_gate gate@(CInit _ _ _) = gate_ncflag gate
controllable_gate gate@(QTerm _ _ _) = gate_ncflag gate
controllable_gate gate@(CTerm _ _ _) = gate_ncflag gate
controllable_gate gate@(QMeas _) = gate_ncflag gate
controllable_gate gate@(QDiscard _) = gate_ncflag gate
controllable_gate gate@(CDiscard _) = gate_ncflag gate
controllable_gate gate@(DTerm _ _) = gate_ncflag gate
controllable_gate gate@(Subroutine _ _ _ _ _ _ _ _ NoCtl _) = gate_ncflag gate

-- | Define whether an entire low-level circuit can be controlled
controllable_circuit :: Circuit -> Bool
controllable_circuit (_,gs,_,_) = and (map controllable_gate gs)
      
-- ----------------------------------------------------------------------
-- * Specifying control lists

-- | A \"control source\" is anything that can be used as a control on
-- a gate. The most common way to construct a control source is by
-- using the '.==.', './=.', and '.&&.' operators. In addition,
-- we provide the following instances:
-- 
-- * 'Bool'. A boolean condition that is known at circuit generation
-- time can be used as a control, which is then either trivial (the
-- gate is generated) or inconsistent (the gate is not generated).
-- 
-- * 'Wire'. This includes the type 'Bit' (for a classical
-- execution-time control) and 'Qubit' (for a quantum control). A wire
-- can be used as a shorthand notation for a positive control on that
-- wire.
-- 
-- * 'ControlList'. A control list is Quipper's internal
-- representation of a control condition, and is trivially a control
-- source.
-- 
-- * A list of control sources can be used as a control source.
class ControlSource a where
  -- | Convert a condition to a control.
  to_control :: a -> ControlList
  
instance ControlSource Bool where
  to_control True = clist_empty
  to_control False = Inconsistent
  
instance ControlSource Wire where
  to_control w = ControlList (Map.singleton w True)
  
instance ControlSource (Signed Wire) where
  to_control (Signed w b) = ControlList (Map.singleton w b)

instance ControlSource ControlList where
  to_control x = x

instance ControlSource a => ControlSource [a] where
  to_control list = foldl combine clist_empty (map to_control list)

instance ControlSource () where
  to_control _ = clist_empty

instance (ControlSource a, ControlSource b) => ControlSource (a,b) where
  to_control (a,b) = combine (to_control a) (to_control b)

instance (ControlSource a, ControlSource b, ControlSource c) => ControlSource (a,b,c) where
  to_control = to_control . untuple

instance (ControlSource a, ControlSource b, ControlSource c, ControlSource d) => ControlSource (a,b,c,d) where
  to_control = to_control . untuple

instance (ControlSource a, ControlSource b, ControlSource c, ControlSource d, ControlSource e) => ControlSource (a,b,c,d,e) where
  to_control = to_control . untuple

instance (ControlSource a, ControlSource b, ControlSource c, ControlSource d, ControlSource e, ControlSource f) => ControlSource (a,b,c,d,e,f) where
  to_control = to_control . untuple

instance (ControlSource a, ControlSource b, ControlSource c, ControlSource d, ControlSource e, ControlSource f, ControlSource g) => ControlSource (a,b,c,d,e,f,g) where
  to_control = to_control . untuple
