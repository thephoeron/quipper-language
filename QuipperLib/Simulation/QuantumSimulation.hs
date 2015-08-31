-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}

-- | This module provides functions for simulating circuits, 
-- for testing and debugging purposes. 
-- It borrows ideas from the implementation of the Quantum IO Monad.
-- 
-- This module provides the internal implementation of the library,
-- and can be imported by other libraries. The public interface to
-- simulation is "QuipperLib.Simulation".

module QuipperLib.Simulation.QuantumSimulation where

import Quipper
import Quipper.Internal

-- The following is a bunch of stuff we need to import because,
-- temporarily, QuantumSimulation.hs uses low-level interfaces. It
-- should be re-implemented using only high-level interfaces, or in
-- some cases, more stuff should be exported from Quipper.hs.
import Quipper.Circuit
import Quipper.Transformer
import Quipper.Monad (qubit_of_wire)
import Quipper.Generic (encapsulate_dynamic, qc_unbind)

import Libraries.Auxiliary

-- we use the state monad to hold our \"quantum\" state
import Control.Monad.State
-- we use complex numbers as our probability amplitudes
import Quantum.Synthesis.Ring (Cplx (..), i)
-- we use a random number generator to simulate \"quantum randomness\"
import System.Random hiding (split)
-- we store \"basis\" states as a map, 
import Data.Map (Map)
import qualified Data.Map as Map

import Data.List (partition)

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)

import qualified Debug.Trace -- used in tracing the simulation of quipper computations

-- | We define our own trace function that only calls trace if the boolean
-- argument is true.
trace :: Bool -> String -> a -> a
trace False _ a = a
trace True message a = Debug.Trace.trace message a

-- ======================================================================
-- * Simulation as a Transformer

-- $ The quantum simulator takes a Quipper circuit producing function,
-- and uses a transformer to simulate the resulting circuit, one gate at a time.
-- This allows the simulation to progress in a lazy manner, allowing dynamic
-- lifting results to be passed back to the circuit producing function as
-- and when they are required (to generate further gates in the circuit).

-- $ The implementation of the quantum simulator makes use of a /State/ monad
-- to carry an underlying quantum state throughout the computation. This /State/
-- is updated by each quantum operation within the circuit. A quantum
-- state is a vector of 'basis' states, along with complex amplitudes.

-- | Gates that act on a single qubit can be defined by essentially a 2-by-2 matrix.
-- A GateR is written by rows, such that a matrix:
--
-- \[image GateR.png] 
--
-- would be written as (m00,m01,m10,m11).
type GateR r = (Cplx r,Cplx r, Cplx r, Cplx r)

-- | Scalar multiplication of a 2-by-2 matrix by a given scalar.
scale :: (Floating r) => Cplx r -> GateR r -> GateR r
scale e (a,b,c,d) = (e*a,e*b,e*c,e*d) 

-- | The inverse of a 'GateR' is its conjugate transpose.
reverseR :: (Floating r) => GateR r -> GateR r
reverseR (m00,m01,m10,m11) = (conjugate m00, conjugate m10, conjugate m01, conjugate m11)
 where
  conjugate (Cplx a b) = Cplx a (-b) 

-- | A simple pattern matching function that gives each \"gate name\"
-- a /GateR/ representation.  Adding (single qubit) quantum gates to
-- this function will give them an implementation in the
-- simulator. Any single qubit named quantum gate that needs to be
-- simulated must have a clause in this function, along with a given
-- /GateR/ that is its matrix representation. Note that unitarity is
-- not enforced, so defined gates must be checked manually to be
-- unitary operators.
-- 
-- > Example Gates:
-- > gateQ "x" = (0,1,1,0)
-- > gateQ "hadamard" = (h, h, h,-h) where h = (1/sqrt 2)
gateQ :: (Floating r) => String -> GateR r
gateQ "x" = (0,1,1,0)
gateQ "hadamard" = (h, h, h,-h) where h = Cplx (1/sqrt 2) 0
gateQ "X" = (0,1,1,0)
gateQ "Y" = (0,-i,i,0)
gateQ "Z" = (1,0,0,-1)
gateQ "S" = (1,0,0,i)
gateQ "E" = ((-1+i)/2, (1+i)/2, (-1+i)/2, (-1-i)/2)
gateQ "YY" = (h,i*h,i*h,h) where h = Cplx (1/sqrt 2) 0
gateQ "T" = (1,0,0,omega) where omega = (Cplx (1 / sqrt 2) (1 / sqrt 2)) 
gateQ "V" = scale 0.5 (a,b,b,a) where a = Cplx 1 (-1)
                                      b = Cplx 1 1
gateQ "omega" = (omega,0,0,omega) where omega = (Cplx (1 / sqrt 2) (1 / sqrt 2))
gateQ "iX" = (0,i,i,0)
gateQ name = error ("quantum gate: " ++ name ++ " not implemented")

-- | Like 'gateQ', but also conditionally invert the gate depending
-- on InverseFlag.
gateQinv :: (Floating r) => String -> InverseFlag -> GateR r
gateQinv name False = gateQ name
gateQinv name True = reverseR (gateQ name)

-- | The exponential function for 'Cplx' numbers.
expC :: (Floating r) => Cplx r -> Cplx r
expC (Cplx a b) = Cplx (exp a * cos b) (exp a * sin b)

-- | The constant π, as a complex number.
piC :: (Floating r) => Cplx r
piC = Cplx pi 0

-- | Like 'gateQ', but takes the name of a rotation and a real parameter. 
rotQ :: (Floating r) => String -> Timestep -> GateR r
rotQ "exp(-i%Z)" theta = expZtR t
  where t = fromRational (toRational theta)
rotQ "exp(% pi i)" theta = gPhase t
  where t = fromRational (toRational theta)
rotQ "R(2pi/%)" theta = (1,0,0,expC (2*piC*i/t))
  where t = fromRational (toRational theta)
rotQ "T(%)" theta = (1,0,0,expC (-i*t))
  where t = fromRational (toRational theta)
rotQ "G(%)" theta = (expC (-i*t),0,0,expC (-i*t))
  where t = fromRational (toRational theta)
rotQ "Rz(%)" theta = (expC (-i*t/2),0,0,expC (i*t/2))
  where t = fromRational (toRational theta)
rotQ name theta = error ("quantum rotation: " ++ name ++ " not implemented")

-- | Like 'rotQ', but also conditionally invert the gate depending on
-- InverseFlag.
rotQinv :: (Floating r) => String -> InverseFlag -> Timestep -> GateR r
rotQinv name False theta = rotQ name theta
rotQinv name True theta = reverseR (rotQ name theta)

-- | Return the matrix for the 'QexpZt' gate.
expZtR :: (Floating r) => r -> GateR r
expZtR t = (expC (Cplx 0 (-t)),0,0,expC (Cplx 0 t))

-- | Return the matrix for the 'GPhase' gate.
gPhase :: (Floating r) => r -> GateR r
gPhase t = (expC (Cplx 0 (t * pi)),0,0,expC (Cplx 0 (t * pi)))

-- | Translate a classical gate name into a boolean function.
-- Adding classical gates to this function will give them an implementation in
-- the simulator.
-- 
-- > Example Gate:
-- > gateC "if" [a,b,c] = if a then b else c 
gateC :: String -> ([Bool] -> Bool)
gateC "if" [a,b,c] = if a then b else c 
gateC name inputs = error ("classical gate: " ++ name ++ ", not implemented (at least for inputs: " ++ show inputs ++ " )")

-- | The type of vectors with scalars in /n/ over the basis /a/. A
-- vector is simply a list of pairs. 
data Vector n a = Vector [(a,n)]

-- | An amplitude distribution gives each classical basis state an amplitude.
type Amplitudes r = Vector (Cplx r) (Map Qubit Bool)

-- | A probability distribution gives each element a probability.
type ProbabilityDistribution r a = Vector r a

-- | A QuantumTrace is essentially a probability distribution for the current state
-- of the qubits that have been traced. We can represent this using a Vector. The
-- list of Booleans is in the same order as the list of Qubits that was being 
-- traced.
type QuantumTrace r = ProbabilityDistribution r [Bool]

-- | Normalizing is used to make sure the probabilities add up to 1.
normalize :: (Floating r) => QuantumTrace r -> QuantumTrace r
normalize (Vector xs) = Vector xs'
  where
    p' = Prelude.foldr (\(_,p) accum  -> accum + p) 0.0 xs
    xs' = map (\(bs,p) -> (bs,p / p')) xs 

-- | A 'QuantumState' is the data structure containing the state that we update
-- throughout the simulation. We need to keep track of the next available wire,
-- and a quantum state in the form of a distribution of basis states. We also
-- track a list of quantum traces, so that we have a \"tracing\" mechanism during
-- the execution of quantum circuits.
data QuantumState r = QState {
    next_wire :: Wire,
    quantum_state :: Amplitudes r,
    traces :: [QuantumTrace r], -- this will be stored in the reverse order in which
                             -- the traces occured in the circuit.
    namespace :: Namespace, -- we need a namespace to keep track of subroutines
    trace_flag :: Bool -- whether or not we trace comments during the simulation
  }

-- | When we start a simulation, we need an empty starting state.
empty_quantum_state :: (Floating r) => Bool -> r -> QuantumState r
empty_quantum_state tf _ = QState { next_wire = 0, quantum_state = Vector [(Map.empty,1)], traces = [], namespace = namespace_empty, trace_flag = tf}

-- | It doesn't make sense having a quantum control on a classical gate, so
-- we can throw an error if that is the case, and just collect the boolean
-- result otherwise.
classical_control :: Signed (B_Endpoint Qubit Bool) -> Bool
classical_control (Signed bep val) = case bep of
  (Endpoint_Bit val') -> val == val'
  (Endpoint_Qubit _) -> error "CNot: Quantum Control on Classical Gate"

-- | Map the 'classical_control' function to all the controls, and take the
-- 'and' of the result
classical_controls :: Ctrls Qubit Bool -> Bool
classical_controls cs = and (map classical_control cs)

-- | When we want a quantum control, we will be working with one \"basis state\" at
-- a time, and can look up the qubit's value in that basis state to see whether
-- the control firs.
qc_control :: Map Qubit Bool -> Signed (B_Endpoint Qubit Bool) -> Bool
qc_control mqb (Signed bep val) = case bep of
  (Endpoint_Bit val') -> val == val'
  (Endpoint_Qubit q) -> val == val' where val' = mqb Map.! q

-- | Map the 'qc_control' function to all the controls (under the given basis 
-- state), and take the 'and' of the result.
qc_controls :: Map Qubit Bool -> Ctrls Qubit Bool -> Bool
qc_controls mqb cs = and (map (qc_control mqb) cs)

-- | We can calculate the magnitude of a complex number
magnitude :: (Floating r) => Cplx r -> r
magnitude (Cplx a b) = sqrt (a^2 + b^2)

-- | The 'split' function splits a Amplitude distribution, by
-- partitioning it around the state of the given qubit within each basis state. It
-- also returns the probability of the qubit being True within the given 
-- Amplitudes. This function is used when we want to measure a qubit.
split :: (Floating r, Eq r, Ord r) => Amplitudes r -> Qubit -> (r,Amplitudes r,Amplitudes r)
split (Vector pas) q = if p < 0 || p > 1 
                       then error "p < 0 or > 1" 
                       else (p,Vector ift,Vector iff)
 where
  amp x = foldr (\(_,pa) p -> p + ((magnitude pa)*(magnitude pa))) 0 x
  apas = amp pas
  (ift,iff) = partition (\(mqb,_) -> (mqb Map.! q)) pas  
  p = if apas == 0 then 0 else (amp ift)/apas

-- | A PMonad is a Monad enriched with a 'merge' function that takes a probability,
-- and two results, and returns a merged version of these results under the given 
-- monad. This idea is taken directly from QIO.
class (Floating r, Monad m) => PMonad r m where
  merge :: r -> a -> a -> m a

-- | We can merge two measurement outcomes, and explicitly keep the first outcome 
-- as the True result, and the second as the False result.
merge_with_result :: PMonad r m => r -> a -> a -> m (Bool,a)
merge_with_result p ift iff = merge p (True,ift) (False,iff)

-- | IO forms a PMonad, where results are merged by choosing one probabilistically
-- using a random number.
instance (Floating r, Random r, Ord r) => PMonad r IO where
  merge p ift iff = do
   pp <- randomRIO (0,1)
   let res = if p > pp then ift else iff
   return res

-- | A State Monad holding a 'RandomGen' forms a 'PMonad', where results are 
-- merged by choosing one probabilistically using a random number from the 
-- 'RandomGen'.
instance (Floating r, Random r, Ord r, RandomGen g) => PMonad r (State g) where
  merge p ift iff = do
   gen <- get
   let (pp,gen') = randomR (0,1) gen
   put gen'
   let res = if p > pp then ift else iff
   return res

-- | Any numeric indexed vector forms a 'Monad'.
instance (Num n) => Monad (Vector n) where
	return a = Vector [(a,1)]
	(Vector ps) >>= f = Vector [(b,i*j) | (a,i) <- ps, (b,j) <- removeVector (f a)] where removeVector (Vector as) = as 

instance (Num n) => Applicative (Vector n) where
  pure = return
  (<*>) = ap

instance (Num n) => Functor (Vector n) where
  fmap = liftM

-- | We can show certain vectors, ignoring any 0 probabilities, and
-- combining equal terms.
instance (Show a,Eq a,Num n,Eq n,Show n) => Show (Vector n a) where 
    show (Vector ps) = show (combine (filter (\ (a,p) -> p /= 0) ps) []) 
     where
      combine [] as = as
      combine (x:xs) as = combine xs (combine' x as)
      combine' (a,p) [] = [(a,p)]
      combine' (a,p) ((a',p'):xs) = if a == a' then (a,p+p'):xs else (a',p'):(combine' (a,p) xs)

-- | 'ProbabilityDistribution' forms a 'PMonad' such that probabilistic results are 
-- \"merged\" by extending the probability distribution by the possible results.
instance (Floating r, Eq r) => PMonad r (Vector r) where
    merge 1 ift iff = Vector [(ift,1)]
    merge 0 ift iff = Vector [(iff,1)]
    merge p ift iff = Vector [(ift,p),(iff,1-p)]

-- | The 'get_trace'' function returns a probability distribution of the state of
-- a list of qubits within a given amplitude distribution.
get_trace :: (Floating r) => [Qubit] -> Amplitudes r -> QuantumTrace r
get_trace qs (Vector amps) = Vector ps
 where
  ps = map (tracing qs) amps
  tracing qs (mqb,cd) = (map (\q -> mqb Map.! q) qs,(magnitude cd)*(magnitude cd)) 

-- | Add an amplitude to an amplitude distribution, combining (adding) the amplitudes for equal states in the distribution.
add :: (Floating r) => ((Map Qubit Bool),Cplx r) -> Amplitudes r -> Amplitudes r
add (a,x) (Vector axs) = Vector (add' axs)
  where add' [] = [(a,x)]
        add' ((by @ (b,y)):bys) | a == b = (b,x+y):bys
                                | otherwise = by:(add' bys)

-- | The apply' function is used to apply a function on \"basis states\" to an 
-- entire amplitude distribution. 
apply :: (Floating r, Eq r) => (Map Qubit Bool -> Amplitudes r) -> Amplitudes r -> Amplitudes r
apply f (Vector []) = Vector []
apply f (Vector ((a,0):[])) = Vector []
apply f (Vector ((a,x):[])) = Vector (map (\(b,k) -> (b,x*k)) (fa)) where Vector fa = f a
apply f (Vector ((a,0):vas)) = apply f (Vector vas)
apply f (Vector ((a,x):vas)) = foldr add (apply f (Vector vas)) (map (\(b,k) -> (b,x*k)) (fa)) where Vector fa = f a

-- | Lift a function that returns a single basis state, to a function that
-- returns an amplitude distribution (containing a singleton).
vector :: (Floating r) => (Map Qubit Bool -> Map Qubit Bool) -> Map Qubit Bool -> Amplitudes r
vector f a = Vector [(f a,1)]

-- | apply the given function only if the controls fire.
if_controls :: (Floating r) => Ctrls Qubit Bool -> (Map Qubit Bool -> Amplitudes r) -> Map Qubit Bool -> Amplitudes r
if_controls c f mqb = if (qc_controls mqb c) then f mqb else Vector [(mqb,1)]

-- | 'performGateQ' defines how a single qubit gate is applied to a quantum state.
-- The application of a /GateR/ to a qubit in a single 'basis' state can split
-- the state into a pair of 'basis' states with corresponding amplitudes.
performGateQ :: (Floating r) => GateR r -> Qubit -> Map Qubit Bool -> Amplitudes r 
performGateQ (m00,m01,m10,m11) q mqb = if (mqb Map.! q) then (Vector [(Map.insert q False mqb,m01),(mqb,m11)])
                                                    else (Vector [(mqb,m00),(Map.insert q True mqb,m10)])

-- | The 'simulation_transformer' is the actual transformer that does the
-- simulation. The type of the 'simulation_transformer'shows that Qubits are 
-- kept as qubits, but Bits are turned into Boolean values, i.e., the results of 
-- the computation. We use a StateT Monad, acting over the IO Monad, to store a 
-- QuantumState throughout the simulation. This means we carry a state, but also 
-- have access to the IO Monad's random number generator (for probabilistic 
-- measurement).
simulation_transformer :: (PMonad r m, Ord r) => Transformer (StateT (QuantumState r) m) Qubit Bool
-- Translation of classical gates:
simulation_transformer (T_CNot ncf f) = f $
  \val c -> do
  let ctrl = classical_controls c
  let val' = if ctrl then not val else val
  return (val',c)
simulation_transformer (T_CInit val ncf f) = f $
  return val
simulation_transformer (T_CTerm b ncf f) = f $
  \val -> if val == b then return () else error "CTerm: Assertion Incorrect"
simulation_transformer (T_CDiscard f) = f $
  \val -> return ()
simulation_transformer (T_DTerm b f) = f $
  \val -> return ()
simulation_transformer (T_CGate name ncf f) = f $
  \list -> do
   let result = gateC name list
   return (result,list) 
simulation_transformer g@(T_CGateInv name ncf f) = f $
  \result list -> do
   let result' = gateC name list
   if result == result' then return list else error "CGateInv: Uncomputation error"
-- Translation of quantum gates:
simulation_transformer (T_QGate "not" 1 0 _ ncf f) = f $
  \[q] [] cs -> do
   let gate = gateQ "x"
   state <- get
   let amps = quantum_state state
   let amps' = apply (if_controls cs (performGateQ gate q)) amps
   put (state {quantum_state = amps'})
   return ([q], [], cs)
simulation_transformer (T_QGate "multinot" _ 0 _ ncf f) = f $
  \qs [] cs -> do
   let gate = gateQ "x"
   state <- get
   let amps = quantum_state state
   let amps' = foldr (\q a -> apply (if_controls cs (performGateQ gate q)) a) amps qs
   put (state {quantum_state = amps'})
   return (qs, [], cs)
simulation_transformer (T_QGate "H" 1 0 _ ncf f) = f $
  \[q] [] cs -> do
   let gate = gateQ "hadamard"
   state <- get
   let amps = quantum_state state
   let amps' = apply (if_controls cs (performGateQ gate q)) amps
   put (state {quantum_state = amps'})
   return ([q], [], cs)
simulation_transformer (T_QGate "swap" 2 0 _ ncf f) = f $
  \[w, v] [] cs -> do
   let gate = gateQ "x"
   state <- get
   let amps = quantum_state state
   let amps' = apply (if_controls ((Signed (Endpoint_Qubit w) True):cs) (performGateQ gate v)) amps
   let amps'' = apply (if_controls ((Signed (Endpoint_Qubit v) True):cs) (performGateQ gate w)) amps'
   let amps''' = apply (if_controls ((Signed (Endpoint_Qubit w) True):cs) (performGateQ gate v)) amps''
   put (state {quantum_state = amps'''})
   return ([w, v], [], cs)
simulation_transformer (T_QGate "W" 2 0 _ ncf f) = f $
  \[w, v] [] cs -> do
   let gateX = gateQ "x"
   let gateH = gateQ "hadamard"
   state <- get
   let amps = quantum_state state
   let amps' = apply (if_controls ((Signed (Endpoint_Qubit w) True):cs) (performGateQ gateX v)) amps
   let amps'' = apply (if_controls ((Signed (Endpoint_Qubit v) True):cs) (performGateQ gateH w)) amps'
   let amps''' = apply (if_controls ((Signed (Endpoint_Qubit w) True):cs) (performGateQ gateX v)) amps''
   put (state {quantum_state = amps'''})
   return ([w, v], [], cs)
simulation_transformer (T_QGate "trace" _ _ False ncf f) = f $
 \qs gc c -> do
  -- a \"trace\" gate adds the current probability distribution for the given qubits
  -- to the list of previous quantum traces
  state <- get
  let current_traces = traces state
  let amps = quantum_state state
  let new_trace = get_trace qs amps
  put (state {traces = new_trace:current_traces})
  return (qs,gc,c)
simulation_transformer (T_QGate "trace" _ _ True ncf f) = f $
 \qs gc c -> return (qs,gc,c) -- we don't do anything for the inverse \"trace\" gate
simulation_transformer (T_QGate name 1 0 inv ncf f) = f $ 
  \[q] [] c -> do
   let gate = gateQinv name inv
   state <- get
   let amps = quantum_state state
   let amps' = apply (if_controls c (performGateQ gate q)) amps
   put (state {quantum_state = amps'})
   return ([q],[],c)
simulation_transformer (T_QRot name 1 0 inv theta ncf f) = f $ 
  \[q] [] c -> do
   let gate = rotQinv name inv theta
   state <- get
   let amps = quantum_state state
   let amps' = apply (if_controls c (performGateQ gate q)) amps
   put (state {quantum_state = amps'})
   return ([q],[],c)
simulation_transformer (T_GPhase t ncf f) = f $
  \w c -> do
  state <- get
  let gate = rotQ "exp(% pi i)" t
  let wire = next_wire state
  let q = qubit_of_wire wire
  let amps = quantum_state state
  let amps' = apply (vector (Map.insert q False)) amps 
  let amps'' = apply (if_controls c (performGateQ gate q)) amps'
  let (p,ift,iff) = split amps'' q
  (val,ampsf) <- lift $ merge_with_result p ift iff 
  case val of
    False -> do
        let ampsf' = apply (vector (Map.delete q)) ampsf 
        put (state {quantum_state = ampsf'})
        return c
    _ -> error "GPhase"
simulation_transformer (T_QInit val ncf f) = f $
  do
  state <- get
  let wire = next_wire state
  let q = qubit_of_wire wire
  let wire' = wire + 1
  let amps = quantum_state state
  let amps' = apply (vector (Map.insert q val)) amps 
  put (state {quantum_state = amps', next_wire = wire'})
  return q
simulation_transformer (T_QMeas f) = f $
  \q -> do
  state <- get
  let amps = quantum_state state
  let (p,ift,iff) = split amps q
  (val,amps') <- lift $ merge_with_result p ift iff
  let amps'' = apply (vector (Map.delete q)) amps' 
  put (state {quantum_state = amps''})
  return val
simulation_transformer (T_QDiscard f) = f $
  \q -> do
   -- a discard is essentially a measurement, with the result thrown away, so we
   -- do that here, as it will reduce the size of the quantum state we are
   -- simulating over.
  state <- get
  let (p,ift,iff) = split (quantum_state state) q
  (_,amps) <- lift $ merge_with_result p ift iff
  let amps' = apply (vector (Map.delete q)) amps 
  put (state {quantum_state = amps'})
  return ()
simulation_transformer (T_QTerm b ncf f) = f $
  \q -> do
   -- with a real quantum computer, when we terminate a qubit with an assertion
   -- we have no way of actually checking the assertion. The best we can do is
   -- measure the qubit and then throw an error if the assertion is incorrect,
   -- which may only occur with a small probability. Here, we are able to split
   -- the quantum state and see if the qubit exists in the incorrect state with
   -- any non-zero probability, and throw an error.
  state <- get
  let amps = quantum_state state
  let (p,ift,iff) = split amps q
  (val,amps') <- lift $ merge_with_result p ift iff
  if val == b then put (state {quantum_state = amps'}) else error "QTerm: Assertion doesn't hold"
simulation_transformer (T_Comment "" inv f) = f $
  \_ -> return ()
   -- e.g. a comment can be (the) empty (string) if it only contains labels
simulation_transformer (T_Comment name inv f) = f $
  \_ -> do
   state <- get
   -- we don't need to do anything with a comment, but they can be useful
   -- to know where we are in the circuit, so we shall output a trace of
   -- the (non-empty) comments during a simulation. 
   trace (trace_flag state) name $ return ()
-- The remaining gates are not yet implemented:
simulation_transformer g@(T_QGate _ _ _ _ _ _) =
  error ("simulation_transformer: unimplemented gate: " ++ show g)
simulation_transformer g@(T_QRot _ _ _ _ _ _ _) =
  error ("simulation_transformer: unimplemented gate: " ++ show g)
simulation_transformer g@(T_CSwap _ _) =
  error ("simulation_transformer: unimplemented gate: " ++ show g)
simulation_transformer g@(T_QPrep _ _) =
  error ("simulation_transformer: unimplemented gate: " ++ show g)
simulation_transformer g@(T_QUnprep _ _) =
  error ("simulation_transformer: unimplemented gate: " ++ show g)
simulation_transformer g@(T_Subroutine sub inv ncf scf ws_pat a1_pat vs_pat a2_pat rep f) = f $
 \ns in_values c -> do
    case Map.lookup sub ns of
     Just (TypedSubroutine sub_ocirc _ _ _) -> do
      let OCircuit (in_wires, sub_circ, out_wires) = if inv then reverse_ocircuit sub_ocirc else sub_ocirc
      let in_bindings = bind_list in_wires in_values bindings_empty
      let sub_bcirc = (sub_circ,ns)
      out_bind <- transform_bcircuit_rec simulation_transformer sub_bcirc in_bindings
      return (unbind_list out_bind out_wires, c) 
     Nothing -> error $ "simulation_transformer: subroutine " ++ show sub ++ " not found (in " ++ showNames ns ++ ")"

-- | The simulation_transformer is also Dynamic, as the simulated wire states
-- can simply be used to perform dynamic liftings.
simulation_dynamic_transformer :: (PMonad r m, Ord r) => DynamicTransformer (StateT (QuantumState r) m) Qubit Bool
simulation_dynamic_transformer = DT {
  transformer = simulation_transformer,
  define_subroutine = \name subroutine -> return (),
  lifting_function = return
  } 

-- | Apply the 'dynamic_simulation_transformer' to a (unary) circuit generating 
-- function. 
simulate_transform_unary :: (PMonad r m, Ord r) => (QCData qa, QCData qb, QCData (QCType Bit Bit qb), QCType Bool Bool qb ~ QCType Bool Bool (QCType Bit Bit qb)) => (qa -> Circ qb)
     -> BType qa
     -> StateT (QuantumState r) m (QCType Qubit Bool (QCType Bit Bit qb))
simulate_transform_unary (f :: qa -> Circ qb) input = do
  let ((), circuit) = encapsulate_dynamic (\() -> qc_init input >>= \qi -> f qi >>= \qi' -> qc_measure qi') ()
  (cb,out_bind) <- transform_dbcircuit simulation_dynamic_transformer circuit bindings_empty
  let output = qc_unbind out_bind cb
  return output

-- | In order to simulate a circuit using an input basis vector, we need to supply
-- each quantum leaf, with a concrete (i.e., not a dummy) qubit.
qdata_concrete_shape :: (QData qa) => BType qa -> qa
qdata_concrete_shape ba = evalState mqa 0
 where
   shape = shapetype_b ba
   mqa = qdata_mapM shape f ba
   f :: Bool -> State Wire Qubit
   f _ =  do
    w <- get
    put (w+1)
    return (qubit_of_wire w)

-- | In order to simulate a circuit using an input basis vector, we need to supply
-- the transformer with a concrete set of qubit bindings.
qdata_concrete_bindings :: (QData qa) => BType qa -> Bindings Qubit Bool
qdata_concrete_bindings ba = snd $ execState mqa (0,bindings_empty)
 where
   shape = shapetype_b ba
   mqa = qdata_mapM shape f ba
   f :: Bool -> State (Wire,Bindings Qubit Bool) ()
   f b =  do
    (w,bindings) <- get
    put (w+1,bind_qubit_wire w (qubit_of_wire w) bindings)
    return () 

-- | As a helper function, in order to simulate a circuit using an input basis vector, 
-- we need to be able to convert each basis into a map from concrete qubits to their
-- value in the given basis.
qdata_to_basis :: (QData qa) => BType qa -> Map Qubit Bool
qdata_to_basis ba = snd $ execState mqa (0,Map.empty)
 where
   shape = shapetype_b ba
   mqa = qdata_mapM shape f ba
   f :: Bool -> State (Wire,Map Qubit Bool) ()
   f b =  do
    (w,m) <- get
    put (w+1,Map.insert (qubit_of_wire w) b m)
    return ()

-- | In order to simulate a circuit using an input basis vector, we need to be able
-- to convert the basis vector into a quantum state suitable for use by the simulator
-- i.e. of type Amplitudes.
qdata_vector_to_amplitudes :: (QData qa, Floating r) => Vector (Cplx r) (BType qa) -> Amplitudes r
qdata_vector_to_amplitudes (Vector das) = (Vector (map (\(a,d) -> (qdata_to_basis a,d)) das))

-- | As a helper function, in order to simulate a circuit using an input basis vector, 
-- we need to be able to convert a map from concrete qubits to their value into a basis
-- of the given concrete shape.
basis_to_qdata :: (QData qa) => qa -> Map Qubit Bool -> BType qa
basis_to_qdata qa m = getId $ qdata_mapM qa f qa
 where
  f :: Qubit -> Id Bool
  f q = case Map.lookup q m of
         Just res -> return res
         _ -> error "basis_to_qdata: qubit not in scope"

-- | In order to simulate a circuit using an input basis vector, we need to be able
-- to convert the quantum state (i.e. of type Amplitudes) into a basis vector.
amplitudes_to_qdata_vector :: (QData qa, Floating r) => qa -> Amplitudes r -> Vector (Cplx r) (BType qa)
amplitudes_to_qdata_vector qa (Vector das) = Vector (map (\(a,d) -> (basis_to_qdata qa a,d)) das)

-- | Apply the 'dynamic_simulation_transformer' to a (unary) circuit generating
-- function, starting with the quantum state set to the given vector of base states 
-- and returning the resulting vector of base states.
simulate_amplitudes_unary :: (PMonad r m, Eq r, Ord r, QData qa, QData qb, qb ~ QCType Qubit Bool qb) => (qa -> Circ qb) -> Vector (Cplx r) (BType qa) -> m (Vector (Cplx r) (BType qb))
simulate_amplitudes_unary f input@(Vector is) = do
  (out_shape,state) <- runStateT circ input_state
  let out_amps = quantum_state state 
  return (amplitudes_to_qdata_vector out_shape (apply (vector id) out_amps))
 where
  amps = qdata_vector_to_amplitudes input
  specimen = case is of
              [] -> error "simulate_amplitudes_unary: can't use empty vector"
              ((b,_):_) -> b
  shape = qdata_concrete_shape specimen
  bindings = qdata_concrete_bindings specimen
  max_wire = case wires_of_bindings bindings of
              [] -> 0
              ws -> maximum ws 
  input_state = (empty_quantum_state False undefined) {quantum_state = amps, next_wire = max_wire + 1}
  (_,circuit) = encapsulate_dynamic f shape
  circ = do
   (cb,out_bind) <- transform_dbcircuit simulation_dynamic_transformer circuit bindings
   let output = qc_unbind out_bind cb
   return output

-- | Input a source of randomness, a quantum circuit, and an initial
-- state (represented as a map from basis vectors to amplitudes).
-- Simulate the circuit and return the final state. If the circuit
-- includes measurements, the simulation will be probabilistic.
-- 
-- The type of this heavily overloaded function is difficult to
-- read. It has, for example, the following types:
-- 
-- > sim_amps :: StdGen -> (Qubit -> Circ Qubit) -> Map Bool (Cplx Double) -> Map Bool (Cplx Double)
-- > sim_amps :: StdGen -> ((Qubit,Qubit) -> Circ Qubit) -> Map (Bool,Bool) (Cplx Double) -> Map Bool (Cplx Double)
-- 
-- and so forth. Note that instead of 'Double', another real number
-- type, such as 'FixedPrec' /e/, can be used.
sim_amps :: (RandomGen g, Floating r, Random r, Ord r, QData qa, QData qb, qb ~ QCType Qubit Bool qb, Ord (BType qb)) => g -> (qa -> Circ qb) -> Map (BType qa) (Cplx r) -> Map (BType qb) (Cplx r)
sim_amps gen f input_map = output_map
 where
  input_vec = Vector (Map.toList input_map)
  circ = simulate_amplitudes_unary f input_vec
  Vector output = evalState circ gen
  output_map = Map.fromList output

-- | Input a source of randomness, a real number, a circuit, and a
-- basis state. Then simulate the circuit probabilistically. Measure
-- the final state and return the resulting basis vector.
-- 
-- The real number argument is a dummy and is never evaluated; its
-- only purpose is to specify the /type/ of real numbers that will be
-- used during the simulation.
run_unary :: (Floating r, Random r, Ord r, RandomGen g, QCData qa, QCData qb, QCData (QCType Bit Bit qb), QCType Bool Bool qb ~ QCType Bool Bool (QCType Bit Bit qb)) => g -> r ->
     (qa -> Circ qb)
     -> BType qa
     -> QCType Qubit Bool (QCType Bit Bit qb)
run_unary g r f input = evalState comp g where
  comp = evalStateT f' (empty_quantum_state False r)
  f' = simulate_transform_unary f input

-- | Like 'run_unary', but return the list of 'QuantumTrace' elements
-- that were generated during the computation. This is useful for
-- checking the intermediary state of qubits within a computation.
run_unary_trace :: (Floating r, Random r, Ord r, RandomGen g, QCData qa, QCData qb, QCData (QCType Bit Bit qb), QCType Bool Bool qb ~ QCType Bool Bool (QCType Bit Bit qb)) => g -> r ->
     (qa -> Circ qb)
     -> BType qa
     -> [QuantumTrace r]
run_unary_trace g r f input = evalState comp g where
  comp = do
    state <- execStateT f' (empty_quantum_state True r)
    let qts = traces state
    return (reverse qts)
  f' = simulate_transform_unary f input

-- | Like 'run_unary', but run in the 'IO' monad instead of passing an
-- explicit source of randomness.
run_unary_io :: (Floating r, Random r, Ord r, QCData qa, QCData qb, QCData (QCType Bit Bit qb), QCType Bool Bool qb ~ QCType Bool Bool (QCType Bit Bit qb)) => r ->
     (qa -> Circ qb)
     -> BType qa
     -> IO (QCType Qubit Bool (QCType Bit Bit qb))
run_unary_io r f input = do
  g <- newStdGen
  return (run_unary g r f input)

-- | Like 'run_unary_trace', but run in the 'IO' monad instead of
-- passing an explicit source of randomness.
run_unary_trace_io :: (Floating r, Random r, Ord r, QCData qa, QCData qb, QCData (QCType Bit Bit qb), QCType Bool Bool qb ~ QCType Bool Bool (QCType Bit Bit qb)) => r ->
     (qa -> Circ qb)
     -> BType qa
     -> IO [QuantumTrace r]
run_unary_trace_io r f input = do
  g <- newStdGen
  return (run_unary_trace g r f input)

-- | Apply the 'simulation_transformer' to a (unary) circuit, and then evaluate
-- the resulting stateful computation to get a probability distribution of possible
-- results
sim_unary :: (Floating r, Ord r, QCData qa, QCData qb, QCData (QCType Bit Bit qb), QCType Bool Bool qb ~ QCType Bool Bool (QCType Bit Bit qb)) => r ->
     (qa -> Circ qb)
     -> BType qa
     -> ProbabilityDistribution r (QCType Qubit Bool (QCType Bit Bit qb))
sim_unary r f input = evalStateT f' (empty_quantum_state False r)
  where f' = simulate_transform_unary f input

-- ======================================================================
-- * Generic functions

-- ** Generic run function

-- $ Generic functions to run Quipper circuits, via a conversion to a
-- 'SimCircuit' using "Random" to simulate quantum states.

-- | Quantum simulation of a circuit, for testing and debugging
-- purposes. Input a source of randomness, a real number, and a
-- quantum circuit. Output a corresponding probabilistic boolean
-- function.
-- 
-- The inputs to the quantum circuit are initialized according to the
-- given boolean arguments. The outputs of the quantum circuit are
-- measured, and the boolean measurement outcomes are
-- returned. 
-- 
-- The real number argument is a dummy and is never evaluated; its
-- only purpose is to specify the /type/ of real numbers that will be
-- used during the simulation.
-- 
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types (for
-- example):
-- 
-- > run_generic :: (Floating r, Random r, Ord r, RandomGen g, QCData qa) => g -> r -> Circ qa -> BType qa
-- > run_generic :: (Floating r, Random r, Ord r, RandomGen g, QCData qa, QCData qb) => g -> r -> (qa -> Circ qb) -> BType qa -> BType qb
-- > run_generic :: (Floating r, Random r, Ord r, RandomGen g, QCData qa, QCData qb, QCData qc) => g -> r -> (qa -> qb -> Circ qc) -> BType qa -> BType qb -> BType qc
-- 
-- and so forth.
run_generic :: (Floating r, Random r, Ord r, RandomGen g, QCData qa, QCDataPlus qb, QCurry qfun qa qb, 
 Curry qfun' (QCType Bool Bool qa) (QCType Qubit Bool (QCType Bit Bit qb))) => g -> r -> qfun -> qfun'
run_generic gen r f = g
 where
  f1 = quncurry f
  g1 = run_unary gen r f1
  g = mcurry g1

-- | Like 'run_generic', but also output a trace of the states of the
-- given list of qubits at each step during the evaluation.
run_generic_trace :: (Floating r, Random r, Ord r, RandomGen g, QCData qa, QCDataPlus qb, QCurry qfun qa qb,
 Curry qfun' (QCType Bool Bool qa) [QuantumTrace r]) => g -> r -> qfun -> qfun'
run_generic_trace gen r f = g 
 where
  f1 = quncurry f
  g1 = run_unary_trace gen r f1
  g = mcurry g1

-- | Like 'run_generic', but run in the 'IO' monad instead of passing
-- an explicit source of randomness.
run_generic_io :: (Floating r, Random r, Ord r, QCData qa, QCDataPlus qb, QCurry qfun qa qb, 
 Curry qfun' (QCType Bool Bool qa) (IO (QCType Qubit Bool (QCType Bit Bit qb)))) => r -> qfun -> qfun'
run_generic_io r f = g 
 where
  f1 = quncurry f
  g1 = run_unary_io r f1
  g = mcurry g1

-- | Like 'run_generic_trace', but run in the 'IO' monad instead of
-- passing an explicit source of randomness.
run_generic_trace_io :: (Floating r, Random r, Ord r, QCData qa, QCDataPlus qb, QCurry qfun qa qb,
 Curry qfun' (QCType Bool Bool qa) (IO [QuantumTrace r])) => r -> qfun -> qfun'
run_generic_trace_io r f = g 
 where
  f1 = quncurry f
  g1 = run_unary_trace_io r f1
  g = mcurry g1

-- ----------------------------------------------------------------------
-- ** Generic sim function

-- $ A generic function to simulate Quipper circuits, via a conversion
-- to a 'SimCircuit' returning a probability distribution of the
-- possible results.

-- | A generic function to simulate Quipper circuits, via a conversion
-- to a 'SimCircuit' returning a probability distribution of the
-- possible results.
-- 
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types (for
-- example):
-- 
-- > sim_generic :: (Floating r, Ord r, QCData qa) => r -> Circ qa -> ProbabilityDistribution r (BType qa)
-- > sim_generic :: (Floating r, Ord r, QCData qa, QCData qb) => r -> (qa -> Circ qb) -> BType qa -> ProbabilityDistribution r (BType qb)
-- > sim_generic :: (Floating r, Ord r, QCData qa, QCData qb, QCData qc) => r -> (qa -> qb -> Circ qc) -> BType qa -> BType qb -> ProbabilityDistribution r (BType qc)
-- 
-- and so forth.
sim_generic :: (Floating r, Ord r, QCData qa, QCDataPlus qb, QCurry qfun qa qb,
 Curry qfun' (QCType Bool Bool qa) (ProbabilityDistribution r (QCType Qubit Bool (QCType Bit Bit qb)))) => r -> qfun -> qfun'
sim_generic r f = g where
  f1 = quncurry f
  g1 = sim_unary r f1
  g = mcurry g1         

