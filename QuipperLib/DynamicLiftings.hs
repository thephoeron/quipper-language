-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This library provides various transformers and functions for
-- performing dynamic liftings based on different mechanisms. Some use
-- simulations to do the dynamic liftings; others just do them
-- randomly. There are also functions for printing the simulated
-- circuit.
-- 
-- This code is experimental.

module QuipperLib.DynamicLiftings where

import Quipper

-- The following is a bunch of stuff we need to import because,
-- temporarily, DynamicLiftings.hs uses low-level interfaces. It
-- should be re-implemented using only high-level interfaces, or in
-- some cases, more stuff should be exported from Quipper.hs.
import Quipper.Circuit (Namespace, namespace_empty, TypedSubroutine(..), OCircuit(..), reverse_ocircuit, showNames)
import Quipper.Internal (BType)
import Quipper.Transformer
import Quipper.Monad
import Quipper.Generic (transform_unary_dynamic_shape)
import Quipper.Printing (getBit)

import QuipperLib.Simulation.QuantumSimulation

import Libraries.Auxiliary (map_provide)

-- we use the state monad to hold our \"quantum\" state
import Control.Monad.State
-- we use a random number generator to simulate \"quantum randomness\"
import System.Random hiding (split)
-- we store \"basis\" states as a map, 
--i.e., Map Qubit Bool represents a basis state.
import Data.Map (Map)
import qualified Data.Map as Map

-- ======================================================================
-- * Random Dynamic Liftings and Liftings from a List

-- | A State monad that holds a random generator.
type RandomCirc a = StateT StdGen Circ a

-- | A State monad that holds a list of booleans.
type ListCirc a = StateT [Bool] Circ a

-- | To evaluate a 'RandomCirc' we require a seed for the random generator.
evalRandomCirc :: Int -> RandomCirc a -> Circ a
evalRandomCirc seed rc = evalStateT rc (mkStdGen seed)

-- | To evaluate a 'ListCirc' we require a list of booleans.
evalListCirc :: [Bool] -> ListCirc a -> Circ a
evalListCirc bools lc = evalStateT lc bools 

-- | Lift 'evalRandomCirc' to unary random circuit generating functions.
evalRandomCirc_unary :: Int -> (a -> RandomCirc b) -> a -> Circ b
evalRandomCirc_unary seed rcirc input = evalRandomCirc seed (rcirc input)

-- | Left 'evalListCirc' to unary list circuit generating functions.
evalListCirc_unary :: [Bool] -> (a -> ListCirc b) -> a -> Circ b
evalListCirc_unary bools lcirc input = evalListCirc bools (lcirc input)

-- | Lift the underlying 'randomR' function into the RandomCirc monad.
randomRRandomCirc :: Random a => (a,a) -> RandomCirc a
randomRRandomCirc (a0,a1) = do
  stdgen <- get
  let (random_a,stdgen') = randomR (a0,a1) stdgen
  put stdgen'
  return random_a

-- | Print a RandomCirc by evaluating it with a seed in the IO monad.
print_unary_random :: (QCData qa) => Format -> (qa -> RandomCirc b) -> qa -> IO ()
print_unary_random format rcirc input = do
  seed <- randomIO
  let circ = evalRandomCirc_unary seed rcirc
  print_unary format circ input

-- | Print a LiftCirc by evaluating it in the IO Monad, so as to read
-- in a given number of booleans.
print_unary_list :: (QCData qa) => Format -> Int -> (qa -> ListCirc b) -> qa -> IO ()
print_unary_list format liftings lcirc input = do
  bools <- mapM (\() -> getBit) (replicate liftings ())
  let circ = evalListCirc_unary bools lcirc
  print_unary format circ input

-- | Lift the 'identity_transformer' using any monad transformer.
lifted_identity_transformer :: (MonadTrans t) => Transformer (t Circ) Qubit Bit
lifted_identity_transformer (T_QGate "not" 1 0 _ ncf f) = f $
  \[q] [] cs -> lift $ without_controls_if ncf $ do
    q' <- qnot q `controlled` cs
    return ([q'], [] ,cs)
lifted_identity_transformer (T_QGate "multinot" _ 0 _ ncf f) = f $
  \ws [] cs -> lift $ without_controls_if ncf $ do
    ws' <- qmultinot_list (map (\x -> (x,True)) ws) `controlled` cs
    return (ws', [], cs)
lifted_identity_transformer (T_QGate "H" 1 0 _ ncf f) = f $
  \[q] [] cs -> lift $ without_controls_if ncf $ do
    q' <- hadamard q `controlled` cs
    return ([q'], [], cs)
lifted_identity_transformer (T_QGate "swap" 2 0 _ ncf f) = f $
  \[w,v] [] cs -> lift $ without_controls_if ncf $ do
    (w',v') <- swap_qubit w v `controlled` cs
    return ([w',v'], [], cs)
lifted_identity_transformer (T_QGate "W" 2 0 _ ncf f) = f $
  \[w,v] [] cs -> lift $ without_controls_if ncf $ do
    (w',v') <- gate_W w v `controlled` cs
    return ([w',v'], [], cs)
lifted_identity_transformer (T_QGate name _ _ inv ncf f) = f $
  \ws vs c -> lift $ without_controls_if ncf $ do
    (ws', vs') <- named_gate_qulist name inv ws vs `controlled` c
    return (ws', vs', c)
lifted_identity_transformer (T_QRot name _ _ inv t ncf f) = f $
  \ws vs c -> lift $ without_controls_if ncf $ do
    (ws', vs') <- named_rotation_qulist name inv t ws vs `controlled` c
    return (ws', vs', c)
lifted_identity_transformer (T_GPhase t ncf f) = f $
  \qs c -> lift $ without_controls_if ncf $ do
    global_phase_anchored_list t qs `controlled` c
    return c
lifted_identity_transformer (T_CNot ncf f) = f $
  \q c -> lift $ without_controls_if ncf $ do
    q' <- cnot q `controlled` c
    return (q', c)
lifted_identity_transformer (T_CGate name ncf f) = f $
  \ws -> lift $ without_controls_if ncf $ do    
    v <- cgate name ws
    return (v, ws)
lifted_identity_transformer (T_CGateInv name ncf f) = f $
  \v ws -> lift $ without_controls_if ncf $ do    
    cgateinv name v ws
    return ws
lifted_identity_transformer (T_CSwap ncf f) = f $
  \w v c -> lift $ without_controls_if ncf $ do
    (w',v') <- swap_bit w v `controlled` c
    return (w',v',c)
lifted_identity_transformer (T_QPrep ncf f) = f $
  \w -> lift $ without_controls_if ncf $ do    
    v <- prepare_qubit w
    return v
lifted_identity_transformer (T_QUnprep ncf f) = f $    
  \w -> lift $ without_controls_if ncf $ do    
    v <- unprepare_qubit w
    return v
lifted_identity_transformer (T_QInit b ncf f) = f $
   lift $ without_controls_if ncf $ do
    w <- qinit_qubit b
    return w
lifted_identity_transformer (T_CInit b ncf f) = f $
   lift $ without_controls_if ncf $ do
    w <- cinit_bit b
    return w
lifted_identity_transformer (T_QTerm b ncf f) = f $
  \w -> lift $ without_controls_if ncf $ do
    qterm_qubit b w
    return ()
lifted_identity_transformer (T_CTerm b ncf f) = f $
  \w -> lift $ without_controls_if ncf $ do
    cterm_bit b w
    return ()
lifted_identity_transformer (T_QMeas f) = f $   
  \w -> lift $ do
    v <- measure_qubit w
    return v
lifted_identity_transformer (T_QDiscard f) = f $
  \w -> lift $ do
    qdiscard_qubit w
    return ()
lifted_identity_transformer (T_CDiscard f) = f $
  \w -> lift $ do
    cdiscard_bit w
    return ()
lifted_identity_transformer (T_DTerm b f) = f $
  \w -> lift $ do
    dterm_bit b w
    return ()
lifted_identity_transformer (T_Subroutine n inv ncf scf ws_pat a1 vs_pat a2 rep f) = f $
  \ns ws c -> lift $ without_controls_if ncf $ do
    vs <- subroutine n inv scf rep ws_pat a1 vs_pat a2 ws `controlled` c
    return (vs,c)
lifted_identity_transformer (T_Comment s inv f) = f $
  \ws -> lift $ do
    comment_label s inv [ (wire_of_endpoint e, s) | (e,s) <- ws ]
    return ()

-- | Dynamic lifting can make use of a random result (without caring which wire is
-- being lifted).
random_dynamic_lift :: Bit -> RandomCirc Bool
random_dynamic_lift _ = randomRRandomCirc (False,True)

-- | Dynamic lifting can pop the head off of a list of booleans, and use that to
-- lift the given wire.
list_dynamic_lift :: Bit -> ListCirc Bool
list_dynamic_lift _ = do
  xs <- get
  case xs of
    [] -> error "ListCirc list of liftings exhausted"
    (x:xs') -> do 
                put xs' 
                return x

-- | A dynamic transformer which is the identity transformer (lifted to
-- RandomCirc), except for the dynamic lifting operation.
random_dynamic_lift_transformer :: DynamicTransformer (StateT StdGen Circ) Qubit Bit
random_dynamic_lift_transformer = DT {
  transformer = lifted_identity_transformer,
  define_subroutine = \name subroutine -> do
    lift $ put_subroutine_definition name subroutine,
  lifting_function = random_dynamic_lift
  }

-- | A dynamic transformer which is the identity transformer (lifted to
-- ListCirc), except for the dynamic lifting operation.
list_dynamic_lift_transformer :: DynamicTransformer (StateT [Bool] Circ) Qubit Bit
list_dynamic_lift_transformer = DT {
  transformer = lifted_identity_transformer,
  define_subroutine = \name subroutine -> do
    lift $ put_subroutine_definition name subroutine,
  lifting_function = list_dynamic_lift
  }

-- | Print a circuit, using random dynamic liftings.
print_unary_with_random_liftings :: (QCData a,QCData b) => Format -> (a -> Circ b) -> a -> IO ()
print_unary_with_random_liftings format circ shape = do
  let lifted_circ = transform_unary_dynamic_shape random_dynamic_lift_transformer circ shape 
  print_unary_random format lifted_circ shape

-- | Print a circuit, using a list of dynamic liftings.
print_unary_with_list_liftings :: (QCData a,QCData b) => Format -> Int -> (a -> Circ b) -> a -> IO ()
print_unary_with_list_liftings format liftings circ shape = do
  let lifted_circ = transform_unary_dynamic_shape list_dynamic_lift_transformer circ shape 
  print_unary_list format liftings lifted_circ shape    

-- ======================================================================
-- * Simulating the Dynamic Liftings

-- | Add state to the Circ Monad so that we can simulate the circuit
-- and use that data for dynamic liftings.
data SimulationState = SS {
    s_quantum_state :: Amplitudes Double,
    s_classical_state :: Map Bit Bool,
    s_namespace :: Namespace, -- we need a namespace to keep track of subroutines
    s_rng :: StdGen
  }

-- | When we start a simulation, we need an empty starting state, with
-- a seed for the generator.
empty_simulation_state :: Int -> SimulationState
empty_simulation_state seed = SS { s_quantum_state = Vector [(Map.empty,1.0)], s_classical_state = Map.empty, s_namespace = namespace_empty, s_rng = mkStdGen seed}

-- | A State monad that holds our SimulationState.
type SimulatedCirc a = StateT SimulationState Circ a

-- | Evaluate a 'SimulatedCirc'. This requires a seed for the random generator.
evalSimulatedCirc :: Int -> SimulatedCirc a -> Circ a
evalSimulatedCirc seed sc = evalStateT sc (empty_simulation_state seed)

-- | Lift 'evalSimulatedCirc' to unary functions.
evalSimulatedCirc_unary :: Int -> (a -> SimulatedCirc b) -> a -> Circ b
evalSimulatedCirc_unary seed scirc input = evalSimulatedCirc seed (scirc input)

-- | Lift the underlying 'randomR' function into the SimulatedCirc monad.
randomRSimulatedCirc :: Random a => (a,a) -> SimulatedCirc a
randomRSimulatedCirc (a0,a1) = do
  state <- get
  let stdgen = s_rng state
  let (random_a,stdgen') = randomR (a0,a1) stdgen
  put (state {s_rng = stdgen'})
  return random_a

-- | A specialized put function for the quantum state that uses the current state
-- instead of a previously retrieved state.
putQS :: Amplitudes Double -> SimulatedCirc ()
putQS amps = do
  state <- get
  put (state {s_quantum_state = amps})

-- | A specialized put function for the classical state that uses the current state
-- instead of a previously retrieved state.
putCS :: Map Bit Bool -> SimulatedCirc ()
putCS bits = do
  state <- get
  put (state {s_classical_state = bits})

-- | It doesn't make sense having a quantum control on a classical gate, so
-- we can throw an error if that is the case, and just lookup the boolean
-- result otherwise.
s_classical_control :: Map Bit Bool -> Signed (B_Endpoint Qubit Bit) -> Bool
s_classical_control bits (Signed bep val) = case bep of
  (Endpoint_Bit bit) -> val == val' where val' = bits Map.! bit
  (Endpoint_Qubit _) -> error "CNot: Quantum Control on Classical Gate"

-- | Map the 's_classical_control' function to all the controls, and take the
-- 'and' of the result.
s_classical_controls :: Map Bit Bool -> Ctrls Qubit Bit -> Bool
s_classical_controls bits cs = and (map (s_classical_control bits) cs)

-- | When we want a quantum control, we will be working with one "basis state" at
-- a time, and can look up the qubit's value in that basis state to see whether
-- the control fires.
s_qc_control :: Map Bit Bool -> Map Qubit Bool -> Signed (B_Endpoint Qubit Bit) -> Bool
s_qc_control bits mqb (Signed bep val) = case bep of
  (Endpoint_Bit bit) -> val == val' where val' = bits Map.! bit
  (Endpoint_Qubit q) -> val == val' where val' = mqb Map.! q

-- | Map the 's_qc_control' function to all the controls (under the given basis 
-- state), and take the 'and' of the result.
s_qc_controls :: Map Bit Bool -> Map Qubit Bool -> Ctrls Qubit Bit -> Bool
s_qc_controls bits mqb cs = and (map (s_qc_control bits mqb) cs)

-- | Apply the given function only if the controls fire.
s_if_controls :: Map Bit Bool -> Ctrls Qubit Bit -> (Map Qubit Bool -> Amplitudes Double) ->  Map Qubit Bool -> Amplitudes Double
s_if_controls bits c f mqb = if (s_qc_controls bits mqb c) then f mqb else Vector [(mqb,1)]

-- | The 'simulated_lift_transformer' is the actual transformer that does the
-- simulation, while recreating the circuit.
simulated_lift_transformer :: Transformer (StateT SimulationState Circ) Qubit Bit
-- Translation of classical gates:
simulated_lift_transformer (T_CNot ncf f) = f $
  \b c -> do
   (b,c) <- lift $ without_controls_if ncf $ do
    b' <- cnot b `controlled` c
    return (b', c)
   state <- get
   let bits = s_classical_state state
   let ctrl = s_classical_controls bits c
   let val = bits Map.! b
   let bits' = if ctrl then (Map.insert b (not val) bits) else bits
   putCS bits'
   return (b,c)
simulated_lift_transformer (T_CInit val ncf f) = f $
  do
   b <- lift $ without_controls_if ncf $ do
    w <- cinit_bit val
    return w
   state <- get
   let bits = s_classical_state state
   putCS (Map.insert b val bits)
   return b
simulated_lift_transformer (T_CTerm b ncf f) = f $
  \w -> do
   lift $ without_controls_if ncf $ do
    cterm_bit b w
    return ()
   state <- get
   let bits = s_classical_state state
   let val = bits Map.! w
   if val /= b then error "CTerm: Assertion Incorrect"
    else do
     putCS (Map.delete w bits)
simulated_lift_transformer (T_CDiscard f) = f $
  \w -> do
   lift $ do
    cdiscard_bit w
   state <- get
   let bits = s_classical_state state
   putCS (Map.delete w bits)
simulated_lift_transformer (T_DTerm b f) = f $
  \w -> do
   lift $ do
    dterm_bit b w
   state <- get
   let bits = s_classical_state state
   putCS (Map.delete w bits)
simulated_lift_transformer (T_CGate name ncf f) = f $
  \ws -> do
   (v,ws) <- lift $ without_controls_if ncf $ do    
    v <- cgate name ws
    return (v, ws)
   state <- get
   let bits = s_classical_state state
   let list = map (\w -> bits Map.! w) ws
   let result = gateC name list
   putCS (Map.insert v result bits)
   return (v,ws) 
simulated_lift_transformer g@(T_CGateInv name ncf f) = f $
  \v ws -> do
   ws <- lift $ without_controls_if ncf $ do    
    cgateinv name v ws
    return ws
   state <- get
   let bits = s_classical_state state
   let list = map (\w -> bits Map.! w) ws
   let result = bits Map.! v
   let result' = gateC name list
   if result == result' then return ws else error "CGateInv: Uncomputation error"
-- Translation of quantum gates:
simulated_lift_transformer (T_QGate "not" 1 0 _ ncf f) = f $
  \[q] [] c -> do
   (q,c) <- lift $ without_controls_if ncf $ do
    q' <- qnot q `controlled` c
    return (q', c)
   let gate = gateQ "x"
   state <- get
   let amps = s_quantum_state state
   let bits = s_classical_state state
   let amps' = apply (s_if_controls bits c (performGateQ gate q)) amps
   putQS amps'
   return ([q], [], c)
simulated_lift_transformer (T_QGate "multinot" _ 0 _ ncf f) = f $
  \qs [] c -> do
   (qs,c) <- lift $ without_controls_if ncf $ do
     qs' <- qmultinot_list (map (\x -> (x,True)) qs) `controlled` c 
     return (qs', c)
   let gate = gateQ "x"
   state <- get
   let amps = s_quantum_state state
   let bits = s_classical_state state
   let amps' = foldr (\q a -> apply (s_if_controls bits c (performGateQ gate q)) a) amps qs
   putQS amps'
   return (qs, [], c)
simulated_lift_transformer (T_QGate "H" 1 0 _ ncf f) = f $ 
  \[q] [] c -> do
   (q,c) <- lift $ without_controls_if ncf $ do
    q' <- hadamard q `controlled` c
    return (q', c)
   let gate = gateQ "hadamard"
   state <- get
   let amps = s_quantum_state state
   let bits = s_classical_state state
   let amps' = apply (s_if_controls bits c (performGateQ gate q)) amps
   putQS amps'
   return ([q], [], c)
simulated_lift_transformer (T_QGate "swap" 2 0 _ ncf f) = f $
  \[w, v] [] c -> do
   (w,v,c) <- lift $ without_controls_if ncf $ do
    (w',v') <- swap_qubit w v `controlled` c
    return (w',v',c)
   let gate = gateQ "x"
   state <- get
   let amps = s_quantum_state state
   let bits = s_classical_state state
   let amps' = apply (s_if_controls bits ((Signed (Endpoint_Qubit w) True):c) (performGateQ gate v)) amps
   let amps'' = apply (s_if_controls bits ((Signed (Endpoint_Qubit v) True):c) (performGateQ gate w)) amps'
   let amps''' = apply (s_if_controls bits ((Signed (Endpoint_Qubit w) True):c) (performGateQ gate v)) amps''
   putQS amps'''
   return ([w, v], [], c)
simulated_lift_transformer (T_QGate "W" 2 0 _ ncf f) = f $
  \[w, v] [] c -> do
   (w,v,c) <- lift $ without_controls_if ncf $ do
    (w',v') <- gate_W w v `controlled` c
    return (w',v',c)
   let gateX = gateQ "x"
   let gateH = gateQ "hadamard"
   state <- get
   let amps = s_quantum_state state
   let bits = s_classical_state state
   let amps' = apply (s_if_controls bits ((Signed (Endpoint_Qubit w) True):c) (performGateQ gateX v)) amps
   let amps'' = apply (s_if_controls bits ((Signed (Endpoint_Qubit v) True):c) (performGateQ gateH w)) amps'
   let amps''' = apply (s_if_controls bits ((Signed (Endpoint_Qubit w) True):c) (performGateQ gateX v)) amps''
   putQS amps'''
   return ([w, v], [], c)
simulated_lift_transformer (T_QGate "trace" _ _ inv ncf f) = f $
  \ws vs c -> lift $ without_controls_if ncf $ do
    (ws', vs') <- named_gate_qulist "trace" inv ws vs `controlled` c
    return (ws', vs', c)
simulated_lift_transformer (T_QGate name _ _ inv ncf f) = f $ 
  \[q] [] c -> do
   ([q],[],c) <- lift $ without_controls_if ncf $ do
    (ws', vs') <- named_gate_qulist name inv [q] [] `controlled` c
    return (ws', vs', c)
   let gate = gateQinv name inv
   state <- get
   let amps = s_quantum_state state
   let bits = s_classical_state state
   let amps' = apply (s_if_controls bits c (performGateQ gate q)) amps
   putQS amps'
   return ([q],[],c)
simulated_lift_transformer (T_QRot name _ _ inv theta ncf f) = f $ 
  \[q] [] c -> do
   ([q],[],c) <- lift $ without_controls_if ncf $ do
    (ws', vs') <- named_rotation_qulist name inv theta [q] [] `controlled` c
    return (ws', vs', c)
   let gate = rotQinv name inv theta
   state <- get
   let amps = s_quantum_state state
   let bits = s_classical_state state
   let amps' = apply (s_if_controls bits c (performGateQ gate q)) amps
   putQS amps'
   return ([q],[],c)
simulated_lift_transformer (T_GPhase t ncf f) = f $
  \w c -> do
   c <-lift $ without_controls_if ncf $ do
    global_phase_anchored_list t w `controlled` c
    return c
   state <- get
   let gate = rotQ "exp(% pi i)" t
   let wire = -1
   let q = qubit_of_wire wire
   let amps = s_quantum_state state
   let bits = s_classical_state state
   let amps' = apply (s_if_controls bits c (vector (Map.insert q False))) amps 
   let amps'' = apply (s_if_controls bits c (performGateQ gate q)) amps'
   let (p,_,ampsf) = split amps'' q
   case p of
    0.0 -> do
     let ampsf' = apply (vector (Map.delete q)) ampsf' 
     putQS ampsf'
     return c
    _ -> error "GPhase"
simulated_lift_transformer (T_QInit val ncf f) = f $
  do
  q <- lift $ without_controls_if ncf $ do
    w <- qinit_qubit val
    return w
  state <- get
  let amps = s_quantum_state state
  let amps' = apply (vector (Map.insert q val)) amps 
  putQS amps'
  return q
simulated_lift_transformer (T_QMeas f) = f $
  \q -> do
   b <- lift $ do
    b <- measure_qubit q
    return b
   state <- get
   let amps = s_quantum_state state
   let bits = s_classical_state state
   let (p,ift,iff) = split amps q
   pp <- randomRSimulatedCirc (0,1.0)
   let (val,amps') = if p > pp then (True,ift) else (False,iff)
   let amps'' = apply (vector (Map.delete q)) amps' 
   let bits' = Map.insert b val bits
   putQS amps''
   putCS bits'
   return b
simulated_lift_transformer (T_QDiscard f) = f $
  \q -> do
   lift $ do
    qdiscard_qubit q
    return ()
   -- a discard is essentially a measurement, with the result thrown away, so we
   -- do that here, as it will reduce the size of the quantum state we are
   -- simulating over.
   state <- get
   let (p,ift,iff) = split (s_quantum_state state) q
   pp <- randomRSimulatedCirc (0,1.0)
   let amps = if p > pp then ift else iff
   let amps' = apply (vector (Map.delete q)) amps
   putQS amps'
   return ()
simulated_lift_transformer (T_QTerm b ncf f) = f $
  \q -> do
  lift $ without_controls_if ncf $ qterm_qubit b q
   -- with a real quantum computer, when we terminate a qubit with an assertion
   -- we have no way of actually checking the assertion. The best we can do is
   -- measure the qubit and then throw an error if the assertion is incorrect,
   -- which may only occur with a small probability. Here, we are able to split
   -- the quantum state and see if the qubit exists in the incorrect state with
   -- any non-zero probability, and throw an error.
  state <- get
  let amps = s_quantum_state state
  let (p,ampst,ampsf) = split amps q
  case (b,p) of
    (True,1.0) -> do
	let ampst' = apply (vector (Map.delete q)) ampst
        putQS ampst'
        return ()
    (False,0.0) -> do
	let ampsf' = apply (vector (Map.delete q)) ampsf
        putQS ampsf'
        return ()
    (True,pt) -> error ("QTerm: Assertion Incorrect (True only has probability " ++ show pt ++ ")")
    (False,pt) -> error ("QTerm: Assertion Incorrect (False only has probability " ++ show (1.0 - pt) ++ ")")
simulated_lift_transformer (T_Comment name inv f) = f $
  \ws -> do
   lift $ do
    comment_label name inv [ (wire_of_endpoint e, s) | (e,s) <- ws ]
    return ()
simulated_lift_transformer g@(T_CSwap ncf f) = f $
  \w v c -> do
   (w,v,c) <- lift $ without_controls_if ncf $ do
    (w',v') <- swap_bit w v `controlled` c
    return (w',v',c)
   error ("simulated_lift_transformer: unimplemented gate: " ++ show g)
simulated_lift_transformer g@(T_QPrep ncf f) = f $
  \w -> do
   w <- lift $ without_controls_if ncf $ do    
    v <- prepare_qubit w
    return v
   error ("simulated_lift_transformer: unimplemented gate: " ++ show g)
simulated_lift_transformer g@(T_QUnprep ncf f) = f $
  \w -> do
   w <- lift $ without_controls_if ncf $ do    
    v <- unprepare_qubit w
    return v
   error ("simulated_lift_transformer: unimplemented gate: " ++ show g)
simulated_lift_transformer g@(T_Subroutine n inv ncf scf ws_pat a1 vs_pat a2 rep f) = f $
 \ns ws c -> do
  (ws,c) <- lift $ without_controls_if ncf $ do
   vs <- subroutine n inv scf rep ws_pat a1 vs_pat a2 ws `controlled` c
   return (vs,c)
  case Map.lookup n ns of
   Just (TypedSubroutine sub_ocirc _ _ _) -> do
    let OCircuit (in_wires, sub_circ, out_wires) = if inv then reverse_ocircuit sub_ocirc else sub_ocirc
    let in_bindings = bind_list in_wires ws bindings_empty
    let sub_bcirc = (sub_circ,ns)
    out_bind <- transform_bcircuit_rec simulated_lift_transformer sub_bcirc in_bindings
    return (unbind_list out_bind out_wires, c) 
   Nothing -> error $ "simulated_lift_transformer: subroutine " ++ show n ++ " not found (in " ++ showNames ns ++ ")"

-- | Dynamic lifting can make use of a simulated result.
simulated_dynamic_lift :: Bit -> SimulatedCirc Bool
simulated_dynamic_lift b = do
  state <- get
  let bits = s_classical_state state
  case Map.lookup b bits of
   Just val -> return val
   Nothing -> error $ "simulated_dynamic_lift: bit " ++ show b ++ " not found" 

-- | A dynamic transformer which simulates the circuit, whilst
-- reconstructing it with simulated lifting results.
-- Note: do not handle classical controlling.
simulated_dynamic_lift_transformer :: DynamicTransformer (StateT SimulationState Circ) Qubit Bit
simulated_dynamic_lift_transformer = DT {
  transformer = simulated_lift_transformer,
  define_subroutine = \name subroutine -> do
    lift $ do
      s <- get_namespace
      let s' = map_provide name subroutine s
      set_namespace s'
      put_subroutine_definition name subroutine,
  lifting_function = simulated_dynamic_lift
  }

-- | Print a RandomCirc by evaluating it with a seed in the IO monad.
print_simulated :: Format -> SimulatedCirc b -> IO ()
print_simulated format scirc = do
  seed <- randomIO
  let circ = evalSimulatedCirc seed scirc
  print_unary format (\() -> circ) ()

-- | Print a circuit, using simulated liftings.
print_unary_with_simulated_liftings :: (QCData a,QCData b) => Format -> (a -> Circ b) -> BType a -> IO ()
print_unary_with_simulated_liftings format circ input = print_simulated format (lifted_circ ())
  where
    circ' = \ () -> do
                     a <- qc_init input
                     circ a
    lifted_circ = transform_unary_dynamic_shape simulated_dynamic_lift_transformer circ' () 
  

-- | Pass a (possibly) dynamic circuit through the 
-- 'simulated_dynamic_lift_transformer' and evaluate the liftings so as to
-- leave us with a static circuit that represents a single run of the original
-- circuit, with the given inputs. We also need to pass in a seed for the RNG.
simulate_liftings_unary :: (QCData a, QCData b) => Int -> (a -> Circ b) -> BType a -> Circ b
simulate_liftings_unary seed fcirc_in input = out_circ
  where
   circ_in = \() -> do
                     a <- qc_init input
                     fcirc_in a
   s_circ = transform_unary_dynamic_shape simulated_dynamic_lift_transformer circ_in ()
   out_circ = evalSimulatedCirc seed (s_circ ())

