-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module contains the interface between the simplified circuit
-- model and Quipper's internal circuit model. The main useful
-- exported functions are: 
-- 
-- * @'simplify_classical'@, which optimizes a classical circuit such
-- as those coming from Template Haskell;
-- 
-- * @'classical_to_reversible_optim'@, which provides a mechanism
-- equivalent to @'Q.classical_to_reversible'@, but with optimization
-- inlined.

module QuipperLib.ClassicalOptim.QuipperInterface where

import Data.Maybe

import qualified Test.QuickCheck as Test

import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Set.Monad as S  {- set-monad-0.1.0.0 -}
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM {- containers-0.5.2.1 -}

import qualified Quipper as Q
import qualified Quipper.Monad as Q
import qualified Quipper.QData as Q
import qualified Quipper.Circuit as Q
import qualified Quipper.Generic as Q
import qualified Quipper.Printing as Q
import qualified QuipperLib.Simulation as Q
import qualified QuipperLib.Simulation.ClassicalSimulation as Q
import qualified Quipper.Transformer as Q
import qualified Quipper.Control as Q 

import qualified QuipperLib.Arith as Q
import qualified Libraries.Auxiliary as Q

import QuipperLib.ClassicalOptim.Circuit
import QuipperLib.ClassicalOptim.Simplification


-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | Extract the list of wires from a piece of quantum data.
getListWire :: (Q.QData qc) => qc -> [Wire]
getListWire x = map Q.wire_of_qubit $ Q.qubits_of_qdata x

-- ----------------------------------------------------------------------
-- * Quipper circuits to simple circuits

-- | Translates a Quipper circuit to a simple circuit. The only gates
-- considered are initializations, terminations, and multi-controlled
-- NOT gates. All other gates are ignored.
-- 
-- Note that simple circuits do not possess termination wires: these
-- wires are simply not terminated, and all subsequent initializations
-- using the same wire ID are sent to fresh wires.
-- 
-- The state of this function is a bit complex, as it keeps track of
-- where the output wires are mapped to.
quipperGateToMyGate :: (IS.IntSet,IM.IntMap Wire,Wire) -> Q.Gate -> ((IS.IntSet,IM.IntMap Wire,Wire), Maybe Gate)
quipperGateToMyGate (s,m,f) (Q.QGate "not" _ [w] _ ctls _) = 
  ((s,m,f), Just $ Cnot (IM.findWithDefault w w m) $ map (\(Q.Signed a b) -> (IM.findWithDefault a a m,b)) ctls)
quipperGateToMyGate (s,m,f) (Q.QInit b w _) = case (IS.member w s) of 
                                              True  -> ((s,IM.insert w f m,f+1), Just $ Init b f)
                                              False -> ((s,m,f), Just $ Init b w)
quipperGateToMyGate (s,m,f) (Q.QTerm b w _) = ((IS.insert w s, m,f), Nothing)
quipperGateToMyGate smf _ = (smf, Nothing)


-- | Get the wire initialized by the gate, if it is an initialization gate.
quipperGateInitW :: Q.Gate -> Maybe Wire
quipperGateInitW (Q.QInit _ w _) = Just w
quipperGateInitW _ = Nothing

-- | Given a list of Quipper gates, get the smallest wire id not in use.
quipperGateFreshWire :: Wire -> [Q.Gate] -> Wire
quipperGateFreshWire w gs = (+) 1 $ L.foldl' max w $ catMaybes $ map quipperGateInitW gs

-- | Send a Quipper 'Q.Circuit' to a 'CircState'.
quipperCircuitToMyCirc :: Q.Circuit -> CircState
quipperCircuitToMyCirc (_, gs, _, n) = 
         emptyState { 
            circuit = catMaybes $ snd $ L.mapAccumL quipperGateToMyGate (IS.empty,IM.empty,quipperGateFreshWire n gs) gs,
            freshWire = n
         }

-- | Send a Quipper 'Q.BCircuit' to a 'CircState'.
quipperBCircuitToMyCirc :: Q.BCircuit -> CircState
quipperBCircuitToMyCirc (c,_) = quipperCircuitToMyCirc c

-- | Generate a custom error message.
myCircErrMsg :: String -> String
myCircErrMsg s = "myCirc: " ++ s

-- | Given a Quipper circuit generating function and a shape argument,
-- return a simple circuit together with the list of non-garbage
-- circuit outputs.
quipperFunToMyCirc :: (Q.QData x, Q.QData y) => (x -> Q.Circ y) -> x -> (CircState,[Wire])
quipperFunToMyCirc f shape =
     let (_, bc, output) = Q.encapsulate_generic myCircErrMsg f shape
     in (quipperBCircuitToMyCirc bc, 
         getListWire output)

-- ----------------------------------------------------------------------
-- * Simple circuits to Quipper circuits

-- | Translate a gate from the simple circuit model into a Quipper gate.
myGateToQuipperGate :: Gate -> Q.Gate
myGateToQuipperGate (Cnot w ctls) = Q.QGate "not" True [w] [] (map (\(w,b) -> Q.Signed w b) ctls) False
myGateToQuipperGate (Init b w) = Q.QInit b w False
myGateToQuipperGate NoOp  = error "myGateToQuipperGate cannot deal with NoOp"

-- | Generate a Quipper comment. The first argument is a comment
-- string, and the second argument is a label to apply to the qubits
-- in the third argument.
makeComment :: String -> String -> [Wire] -> Q.Gate
makeComment comment label ws = 
  Q.Comment comment False $ map (\(i,x) -> (i, label ++ "[" ++ (show x) ++ "]")) (zip ws [0..(length ws)-1])


-- ----------------------------------------------------------------------
-- * Algebraic optimization of Quipper circuits

-- | Optimize a Quipper 'Q.BCircuit'. The second argument is the list
-- of non-garbage outputs. A corresponding list of outputs is also
-- returned along with the circuit.
quipperBCircuitSimpl :: Q.BCircuit -> [Wire] -> (Q.BCircuit,[Wire])
quipperBCircuitSimpl (c,e) output = (((a1,c'',a2',n'),e),o')
   where
   (a1,gs,a2,n) = c
   mycirc = quipperCircuitToMyCirc c
   (c',o') = compressWires (IM.keys a1) $ simplRec $ (\x -> (x,output)) {-set_init_first output-} $ circuit $ mycirc
   i' = IM.keys a1
   c'' = (makeComment "Start classical circuit" "in" i') : 
         (map myGateToQuipperGate c') ++ 
         [makeComment "End classical circuit" "out" o']
   allwires = getAllWires c'
   a2' = IM.fromList $ map (\x -> (x,Q.Qbit)) $ IS.toAscList allwires
   n' = (+) 1 $ head $ IS.toDescList allwires


-- | Optimize a Quipper circuit producing function (together with a
-- shape argument). Return the optimized circuit as a Quipper
-- 'BCircuit', along with a list of the non-garbage circuit outputs.
simplify_classical' :: (Q.QData x, Q.QData y) => (x -> Q.Circ y) -> x -> (Q.BCircuit, [Wire])
simplify_classical' f shape = 
  let (_,bc,output) = Q.encapsulate_generic myCircErrMsg f shape in
  let list_output = getListWire output in
  quipperBCircuitSimpl bc list_output

-- | Optimize a Quipper circuit-producing function. This assumes that
-- the function only consists of pseudo-classical quantum gates, i.e.,
-- initializations, terminations, and (possibly multiply controlled)
-- NOT gates. The behavior on other kinds of circuits is undefined.
-- The second argument is a shape parameter.
simplify_classical :: (Q.QData x, Q.QData y) => (x -> Q.Circ y) -> x -> Q.Circ y
simplify_classical f shape =
  let (input,bc,output) = Q.encapsulate_generic myCircErrMsg f shape in
  let list_output = getListWire output in
  let (bc',list_output') = quipperBCircuitSimpl bc list_output in
  Q.unencapsulate_generic (input,bc', Q.qdata_of_qubits output $ map Q.qubit_of_wire list_output') shape

-- | Like 'Q.classical_to_reversible', but also apply circuit optimization.
classical_to_reversible_optim :: (Q.QData qa, Q.QData qb) => (qa -> Q.Circ qb) -> ((qa,qb) -> Q.Circ (qa,qb))
classical_to_reversible_optim f = Q.classical_to_reversible (simplify_classical f)

-- | Like 'classical_to_reversible_optim', but insert the optimized
-- circuit as a boxed subroutine.
box_classical_to_reversible_optim :: (Q.QData qa, Q.QData qb) => String -> (qa -> Q.Circ qb) -> ((qa,qb) -> Q.Circ (qa,qb))
box_classical_to_reversible_optim s f = Q.classical_to_reversible (Q.box s $ simplify_classical f)

