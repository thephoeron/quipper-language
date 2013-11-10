-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | This module provides functions for simulating certain classes of
-- circuits, for testing and debugging purposes. At the moment, the
-- only type of simulation we provide is boolean simulation. 
-- 
-- This module provides the internal implementation of the library,
-- and can be imported by other libraries. The public interface to
-- simulation is "QuipperLib.Simulation".

module QuipperLib.Simulation.ClassicalSimulation where

import Quipper
import Quipper.Internal

-- The following is a bunch of stuff we need to import because,
-- temporarily, Simulation.hs uses low-level interfaces. It should be
-- re-implemented using only high-level interfaces, or in some cases,
-- more stuff should be exported from Quipper.hs.
import Quipper.Transformer (bind_list, bindings_empty, unbind_list, Bindings, transform_bcircuit_id)
import Quipper.Circuit (RepeatFlag(..), TypedSubroutine(..), OCircuit(..), reverse_ocircuit, ControllableFlag(..), BCircuit)
import Quipper.Generic (qc_bind, qc_unbind, encapsulate_generic)

import Libraries.Auxiliary

import Data.List
import qualified Data.Map as Map

-- ======================================================================
-- * Simulation of classical circuits

-- | Auxiliary function: determine whether a \"control\" is true of false.
controls :: [Signed (B_Endpoint Bool Bool)] -> Bool
controls [] = True
controls ((Signed (Endpoint_Qubit c) b):t) = (c == b) && controls t
controls ((Signed (Endpoint_Bit c) b):t) = (c == b) && controls t

-- | Auxiliary function: compute the boolean function corresponding to
-- a 'CGate' of the given name.
simulate_cgate :: String -> [Bool] -> Bool
simulate_cgate "if" [a,b,c] = if a then b else c
simulate_cgate "if" list = error ("simulate_cgate: \"if\" needs 3 arguments, not " ++ show (length list))
simulate_cgate "and" list = and list
simulate_cgate "or" list = or list
simulate_cgate "xor" list = foldl' bool_xor False list
simulate_cgate "eq" [a,b] = (a == b)
simulate_cgate "eq" list = error ("simulate_cgate: \"eq\" needs 2 arguments, not " ++ show (length list))
simulate_cgate "not" [a] = not a
simulate_cgate "not" list = error ("simulate_cgate: \"not\" needs 1 argument, not " ++ show (length list))
simulate_cgate name list = error ("simulate_cgate: gate \"" ++ name ++ "\" not known")


-- | A "Quipper.Transformer" mapping each gate to the corresponding boolean
-- function. This will fail with an error for gates that don't act
-- within the computational basis, or if some assertion is not
-- met. Some gates are not yet implemented. 

simulate_classical :: Transformer Id Bool Bool

-- Translation of classical gates:
simulate_classical (T_CNot ncf f) = f $
  \q c -> Id (if controls c then not q else q, c)
simulate_classical (T_CSwap ncf f) = f $
  \w v c -> Id (if controls c then (v,w,c) else (w,v,c))
simulate_classical (T_CInit b ncf f) = f $
  Id b
simulate_classical (T_CTerm b ncf f) = f $
  \q -> Id (if b==q then () else error "simulate_classical: CTerm assertion not met")
simulate_classical (T_CDiscard f) = f $
  \b -> Id ()
simulate_classical (T_DTerm b f) = f $
  \b -> Id ()
simulate_classical (T_CGate name ncf f) = f $
  \list -> Id (simulate_cgate name list, list)
simulate_classical (T_CGateInv name ncf f) = f $
  \q list -> if q == simulate_cgate name list 
             then Id list 
             else error ("simulate_classical: CGateInv failed assertion " ++ show q ++ " == " ++ name ++ show list)

-- Translation of quantum gates:
simulate_classical (T_QGate "not" 1 0 _ ncf f) = f $
  \[q] [] c -> if controls c then Id([not q], [], c) else Id([q], [], c)
simulate_classical (T_QGate "multinot" _ 0 _ ncf f) = f $
  \qs [] c -> Id (if controls c then map not qs else qs, [], c)  
simulate_classical (T_QGate "swap" 2 0 _ ncf f) = f $
  \[w,v] [] c -> Id (if controls c then ([v,w], [], c) else ([w,v], [] ,c))
simulate_classical g@(T_QGate "H" 1 0 _ _ _) =
  error ("simulate_classical: gate not classical: " ++ show g)
simulate_classical g@(T_QGate "W" 2 0 _ _ _) =
  error ("simulate_classical: gate not classical: " ++ show g)
simulate_classical g@(T_QGate name _ _ inv ncf f) = f $
  \qs gctls c -> case (name, inv, qs, gctls) of
    ("X", _, [q], []) -> 
      if controls c then Id([not q], [], c) else Id([q], [], c)
    ("Y", _, [q], []) ->
      if controls c then Id([not q], [], c) else Id([q], [], c)
    ("Z", _, [q], []) -> Id([q], [], c)
    ("S", _, [q], []) -> Id([q], [], c)
    ("T", _, [q], []) -> Id([q], [], c)
    ("omega", _, [q], []) -> Id([q], [], c)
    ("iX", _, [q], []) ->
      if controls c then Id([not q], [], c) else Id([q], [], c)
    _ -> error ("simulate_classical: unimplemented gate: " ++ show g)
simulate_classical g@(T_QRot name _ _ inv t ncf f) = f $
  \qs gctls c -> case (name, inv, qs, gctls) of
    ("R(2pi/%)", _, [q], []) -> Id([q], [], c)
    ("exp(-i%Z)", _, [q], []) -> Id([q], [], c)
    _ -> error ("simulate_classical: unimplemented gate: " ++ show g)
simulate_classical g@(T_GPhase t ncf f) = f $
  \q c -> Id c
simulate_classical (T_QInit b ncf f) = f $
  Id b
simulate_classical (T_QTerm b ncf f) = f $
  \q -> if b==q then Id() else error "simulate_classical: QTerm assertion not met"
simulate_classical (T_QDiscard f) = f $
  \b -> Id()
simulate_classical (T_Comment s inv f) = f $
  \b -> Id()

-- Preparation, unpreparation, and measurement:
simulate_classical g@(T_QPrep ncf f) = f $
  \w -> Id w
simulate_classical g@(T_QUnprep ncf f) = f $
  \w -> Id w
simulate_classical g@(T_QMeas f) = f $
  \w -> Id w

-- Subroutines:
simulate_classical g@(T_Subroutine sub inv ncf scf ws_pat a1_pat vs_pat a2_pat (RepeatFlag repeat) f) = f $
  \namespace in_values c -> Id $ 
    case Map.lookup sub namespace of
    Just (TypedSubroutine sub_ocirc _ _ _) ->
      let OCircuit (in_wires, sub_circ, out_wires) = if inv then reverse_ocircuit sub_ocirc else sub_ocirc
          in_bindings = bind_list in_wires in_values bindings_empty
          out_bindings = 
            if (case scf of {AllCtl -> True; OnlyClassicalCtl -> True; NoCtl -> False})
            then if controls c then  foldl' (\in_b _ -> run_classical (sub_circ, namespace) in_b) in_bindings [1..repeat] else in_bindings
            else if length c == 0
                 then foldl' (\in_b _ -> run_classical (sub_circ, namespace) in_b) in_bindings [1..repeat]
                 else error $ "simulate_classical: attempt to control non-controllable subroutine " ++ show sub
      in (unbind_list out_bindings out_wires, c) 
    Nothing -> error $ "simulate_classical: subroutine " ++ show sub ++ " not found"

-- If adding gates: remember to list any unimplemented gates
-- explicitly, so that the type-checker can warn about new gates that
-- must be added to the list.

-- | Boolean simulation of a circuit, for testing and debugging
-- purposes.  This function makes use of the concept of a
-- /valuation/. A valuation is a partial map from circuit wires to
-- booleans, represented by the type @'Bindings' Bool@. Given a
-- circuit and a valuation for its inputs, the function
-- 'run_classical' produces a valuation for its outputs.
-- 
-- The simulation will fail with an error if the circuit contains a
-- gate not acting within the computational basis, or if some
-- assertion is not met. Not all gates are currently
-- implemented. Subroutines are not currently implemented.
-- 
run_classical :: BCircuit -> Bindings Bool Bool -> Bindings Bool Bool
run_classical = transform_bcircuit_id simulate_classical

-- ======================================================================
-- * Generic simulation

-- | Like 'run_classical_unary', but also takes a stub error message.
run_classical_errmsg :: (QCData qa, QCData qb) => ErrMsg -> (qa -> Circ qb) -> BType qa -> BType qb
run_classical_errmsg e (f :: qa -> Circ qb) input = output where
  shape = qcdata_makeshape (dummy :: qa) (dummy :: Bool) (dummy :: Bool) input
  (qa, circuit, qb) = encapsulate_generic e f shape
  valuation_in = qc_bind qa input
  valuation_out = run_classical circuit valuation_in
  output = qc_unbind valuation_out qb

-- | Boolean simulation of a circuit, for testing and debugging
-- purposes. Input a classical circuit, and output the corresponding
-- boolean function. This will fail with an error if the circuit
-- contains a gate not acting within the computational basis, or if
-- some assertion is not met.
run_classical_unary :: (QCData qa, QCData qb) => (qa -> Circ qb) -> BType qa -> BType qb
run_classical_unary = run_classical_errmsg errmsg 
  where
    errmsg x = "run_classical_unary: operation not currently permitted by simulator: " ++ x

-- | Boolean simulation of a circuit, for testing and debugging
-- purposes. Input a classical circuit, and output the corresponding
-- boolean function. This will fail with an error if the circuit
-- contains a gate not acting within the computational basis, or if
-- some assertion is not met.
-- 
-- Unlike 'run_classical_unary', this can be applied to a
-- circuit-generating function in curried form with /n/ arguments, for
-- any /n/ ≥ 0. The resulting boolean function then will also have /n/ arguments. 
-- 
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types:
-- 
-- > run_classical_generic :: (QCData qa) => Circ qa -> BType qa
-- > run_classical_generic :: (QCData qa, QCData qb) => (qa -> Circ qb) -> BType qa -> BType qb
-- > run_classical_generic :: (QCData qa, QCData qb, QCData qc) => (qa -> qb -> Circ qc) -> BType qa -> BType qb -> BType qc
-- 
-- and so forth.
 
run_classical_generic :: (QCData qa, QCData qb, QCurry qfun qa qb, Curry fun (BType qa) (BType qb)) => qfun -> fun
run_classical_generic f = g where
  f1 = quncurry f
  g1 = run_classical_errmsg errmsg f1
  g = mcurry g1
  errmsg x = "run_classical_generic: operation not currently permitted by simulator: " ++ x
    
