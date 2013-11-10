-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This module uses a state transformer monad to rebuild a circuit from
-- the CircInfoState representation. This can only be as lazy as the Quipper
-- ASCII output allows, as subroutine definitions need to be known before
-- a subroutine can be called.

module QuipperLib.QuipperASCIIParser.ASCIICirc where

import QuipperLib.QuipperASCIIParser.CircInfo hiding (run,do_gate)

import Quipper
import Quipper.Circuit
import Quipper.Monad
import Quipper.Generic

import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.State

-- | In the Quipper ASCII output, wires are identified by integers. 
-- We have to map these to Quipper's native wires and types. 
data WireState = WireState {
  wire_map :: IntMap (Wire,Wiretype),
  in_sub :: Bool, 
  subroutines_in_scope :: Map BoxId Sub
 }

-- | An initial, empty WireState, with the given subroutines_in_scope
empty_wirestate :: Map BoxId Sub -> WireState
empty_wirestate subs = WireState {wire_map = IntMap.empty, in_sub = False,
 subroutines_in_scope = subs}

-- | The 'ASCIICirc' monad is like the 'Circ' monad, except that it also
-- keeps track of an additional 'WireState'. The 'lift' function must
-- be used to lift any command for the 'Circ' monad to the 'ASCIICirc'
-- monad. 
type ASCIICirc a = StateT WireState Circ a

-- | The 'in_sub' flag can be set to True, as slightly different behavior is
-- required when evaluating a subroutine.
set_in_sub :: ASCIICirc ()
set_in_sub = do
 state <- get
 put (state {in_sub = True})

-- | Look up the qubit corresponding to a ASCII integer representation of a
-- qubit. If it doesn't already exist then initialize a new qubit.
provide_qubit :: Int -> ASCIICirc Qubit
provide_qubit r = do
  state <- get
  case (in_sub state) of
   False -> do
     let ws = wire_map state
     case IntMap.lookup r ws of
       Just (w,Qbit) -> return (qubit_of_wire w)
       Just (w,Cbit) -> error ("Quantum wire " ++ show r ++ " bound as classical " ++ show w)
       Nothing -> error ("Quantum wire " ++ show r ++ " not in scope")
   True -> return (qubit_of_wire r)

-- | Look up the bit corresponding to a ASCII integer representation of a
-- bit. If it doesn't already exist then initialize a new bit.
provide_bit :: Int -> ASCIICirc Bit
provide_bit r = do
  state <- get
  case (in_sub state) of
   False -> do
     let ws = wire_map state
     case IntMap.lookup r ws of
       Just (w,Cbit) -> return (bit_of_wire w)
       Just (w,Qbit) -> error ("Classical wire " ++ show r ++ " bound as quantum " ++ show w)
       Nothing -> error ("Classical wire " ++ show r ++ " not in scope")
   True -> return (bit_of_wire r)

-- | Look up the wire corresponding to a ASCII integer representation of a
-- bit or qubit. If it doesn't already exist then initialize a new qubit.
provide_wire :: Int -> ASCIICirc Wire
provide_wire r = do
  state <- get
  case (in_sub state) of
   False -> do
     let ws = wire_map state
     case IntMap.lookup r ws of
       Just (w,_) -> return w
       Nothing -> do
         q <- provide_qubit r
         return (wire_of_qubit q)
   True -> return r 

-- | Add a new qubit to the state.
add_qubit :: Int -> Qubit -> ASCIICirc ()
add_qubit w q = do
  state <- get
  let ws = wire_map state
  let ws' = IntMap.insert w (wire_of_qubit q,Qbit) ws
  put (state {wire_map = ws'}) 

-- | Add a new bit to the state.
add_bit :: Int -> Bit -> ASCIICirc ()
add_bit w b = do
  state <- get
  let ws = wire_map state
  let ws' = IntMap.insert w (wire_of_bit b,Cbit) ws
  put (state {wire_map = ws'})

-- | Remove a wire from the state
remove_wire :: Int -> ASCIICirc ()
remove_wire w = do
  state <- get
  let ws = wire_map state
  let ws' = IntMap.delete w ws
  put (state {wire_map = ws'}) 

-- | A helper function for providing the qubits within a control structure
provide_control :: Signed Int -> ASCIICirc (Signed Wire)
provide_control (Signed r val) = do
   w <- provide_wire r
   return (Signed w val)

-- | provides quantum wires for the controls in a control list
provide_controls :: [Signed Int] -> ASCIICirc [Signed Wire]
provide_controls = mapM provide_control

-- | Lift a Quipper circuit, preventing the addition of controls depending
-- on the given boolean.
lift_ncf :: Bool -> Circ a -> ASCIICirc a
lift_ncf False ca = lift ca
lift_ncf True ca = lift $ without_controls ca

-- | Take a Gate  and execute it in the 'ASCIICirc' monad.
do_gate :: Gate -> ASCIICirc ()
do_gate (QGate name iflg ws1 ws2 wbs ncf) = do
  qs1 <- mapM provide_qubit ws1
  qs2 <- mapM provide_qubit ws2
  cs <- provide_controls wbs
  lift_ncf ncf $ named_gate_qulist name iflg qs1 qs2 `controlled` cs
  return ()  
do_gate (QRot name iflg theta ws1 ws2 wbs ncf) = do
  qs1 <- mapM provide_qubit ws1
  qs2 <- mapM provide_qubit ws2
  cs <- provide_controls wbs 
  lift_ncf ncf $ named_rotation_qulist name iflg theta qs1 qs2 `controlled` cs
  return ()
do_gate (GPhase ts ws wbs ncf) = do
  qs <- mapM provide_qubit ws
  cs <- provide_controls wbs  
  lift_ncf ncf $ global_phase_anchored_list ts (map (\w -> endpoint_of_wire w Qbit) (map wire_of_qubit qs)) `controlled` cs
  return ()
do_gate (CNot w wbs ncf) = do
  b <- provide_bit w
  cs <- provide_controls wbs
  lift_ncf ncf $ cnot_at b `controlled` cs 
do_gate (CGate name w ws ncf) = do
  bs <- mapM provide_bit ws  
  b <- lift_ncf ncf $ cgate name bs
  add_bit w b
do_gate (CGateInv name w ws ncf) = do
  b <- provide_bit w
  bs <- mapM provide_bit ws  
  lift_ncf ncf $ cgateinv name b bs 
do_gate (CSwap w1 w2 wbs ncf) = do
  b1 <- provide_bit w1
  b2 <- provide_bit w2
  cs <- provide_controls wbs
  lift_ncf ncf $ swap b1 b2 `controlled` cs
  return ()
do_gate (QPrep w ncf) = do
  b <- provide_bit w
  q <- lift_ncf ncf $ prepare_qubit b
  add_qubit w q
do_gate (QUnprep w ncf) = do
  q <- provide_qubit w
  b <- lift_ncf ncf $ unprepare_qubit q
  add_bit w b
do_gate (QInit val w ncf) = do
  q <- lift_ncf ncf $ qinit val
  add_qubit w q
do_gate (CInit val w ncf) = do
  b <- lift_ncf ncf $ cinit val
  add_bit w b 
do_gate (QTerm val w ncf) = do
  q <- provide_qubit w
  lift_ncf ncf $ qterm val q
  remove_wire w    
do_gate (CTerm val w ncf) = do
  b <- provide_bit w
  lift_ncf ncf $ cterm val b
  remove_wire w   
do_gate (QMeas w) = do
  q <- provide_qubit w
  b <- lift $ measure q
  add_bit w b
do_gate (QDiscard w) = do
  q <- provide_qubit w
  lift $ qdiscard q
  remove_wire w 
do_gate (CDiscard w) = do
  b <- provide_bit w
  lift $ cdiscard b
  remove_wire w   
do_gate (Subroutine boxid iflg ws_in _ ws_out _ wbs ncf _ (RepeatFlag rf)) = do
  -- Note that we ignore the given arities, as they are dummy values
  -- the true values are kept in the ASCIICirc state.
  -- The controllable flag is also ignored, as it is recalculated.
  state <- get
  let subs = subroutines_in_scope state
  case (Map.lookup boxid subs) of
   Nothing -> error ("Subroutine " ++ show boxid ++ " has not been defined in: " ++ show (Map.keys subs))
   Just sub -> do
    let ins = inputs sub
    let (_,in_as) = unzip ins
    let in_wa = zip ws_in in_as
    es_in <- mapM (\(w,wt) ->
      case wt of
       Qbit -> do
                q <- provide_qubit w
                let wire = endpoint_of_wire (wire_of_qubit q) Qbit
                return wire
       Cbit -> do
                b <- provide_bit w
                let wire = endpoint_of_wire (wire_of_bit b) Cbit
                return wire
      ) in_wa
    cs <- provide_controls wbs
    let outs = outputs sub
    let es_out = map (\(w,wt) -> endpoint_of_wire w wt) outs    
    let gates = reverse (circuit sub)
    let ascii_circ = \_ -> set_in_sub >> (mapM_ do_gate gates) >> return es_out 
    let circ = run_asciicirc subs ascii_circ
    let boxid = BoxId (name sub) (shape sub)
    let error_message = \e -> "ASCIICirc.do_gate : " ++ e
    let f = \x -> do
             -- Provide subroutine generic only uses circ if it isn't already
             -- in the namespace.
             provide_subroutine_generic error_message boxid False circ x
             call_subroutine boxid (RepeatFlag rf) x
    es_out' <- case iflg of
                False -> lift_ncf ncf $ f es_in `controlled` cs
                True -> do
                         let (_,out_as) = unzip outs
                         let out_wa = zip ws_in out_as
                         es_out <- mapM (\(w,wt) ->
                           case wt of
                            Qbit -> do
                             q <- provide_qubit w
                             let wire = endpoint_of_wire (wire_of_qubit q) Qbit
                             return wire
                            Cbit -> do
                             b <- provide_bit w
                             let wire = endpoint_of_wire (wire_of_bit b) Cbit
                             return wire
                            ) out_wa 
                         lift_ncf ncf $ (reverse_generic f es_in) es_out `controlled` cs
    -- a subroutine can add/remove wires from scope, so we remove all the input
    -- wires from the state, and add all the output wires to the state.
    -- The state may have changed, so we get it again.
    state <- get
    let wires = wire_map state
    let wires' = foldr (\w ws -> IntMap.delete w ws) wires (if iflg then ws_out else ws_in)
    let wires'' = foldr (\(w,e) ws -> IntMap.insert w 
                   (case e of
                     Endpoint_Qubit q -> (wire_of_qubit q, Qbit)
                     Endpoint_Bit b -> (wire_of_bit b, Cbit)) ws) wires' 
                   (zip (if iflg then ws_in else ws_out) es_out')
    put (state {wire_map = if (in_sub state) then wires else wires''})
do_gate (Comment c iflg wlabels) = do
  qlabels <- mapM (\(w,l) ->
    do
    pw <- provide_wire w
    return (pw,l) ) wlabels
  lift $ comment_label c iflg qlabels
do_gate (DTerm val w) = do
  b <- provide_bit w
  lift $ dterm_bit val b
  remove_wire w 

-- | Allocate an input endpoint, to an endpoint in the ASCIICirc, by adding it to
-- the map of wires in scope.
allocate_input :: (Endpoint,Endpoint) -> ASCIICirc ()
allocate_input (i,e@(Endpoint_Qubit _)) = add_qubit (wire_of_endpoint e) (qubit_of_wire (wire_of_endpoint i)) 
allocate_input (i,e@(Endpoint_Bit _)) = add_bit (wire_of_endpoint e) (bit_of_wire (wire_of_endpoint i)) 

-- ----------------------------------------------------------------------
-- * Unpacking ASCIICirc

-- | Execute a parsed circuit, i.e. a CircInfoState, in the ASCIICirc monad
run_gates :: [Gate] -> Maybe [(Wire,Wiretype)] -> [Endpoint] -> [Endpoint] -> ASCIICirc [Endpoint]
run_gates gates d_outs es ins = do
  mapM_ (\i -> allocate_input i) (zip ins es)
  mapM_ (\g -> do_gate g) gates
  state <- get
  let ws_in_scope = IntMap.elems $ wire_map state
  let es_in_scope = map (\(w,wt) -> endpoint_of_wire w wt) ws_in_scope
  case d_outs of
   Nothing -> return es_in_scope
   Just out_ws -> do
    es_out <- mapM (\(w,wt) -> do
                w' <- provide_wire w
                return (endpoint_of_wire w' wt)) out_ws
    let es_in_scope' = sortBy (\e1 e2 -> compare (wire_of_endpoint e1) (wire_of_endpoint e2)) es_in_scope
    let es_out' = sortBy (\e1 e2 -> compare (wire_of_endpoint e1) (wire_of_endpoint e2)) es_out
    case es_in_scope' == es_out' of
     True -> return es_out'
     False -> return es_in_scope'

-- | Run function for the 'ASCIICirc' monad: execute the actions and
-- produce a circuit.
run_asciicirc :: Map BoxId Sub -> (a -> ASCIICirc b) -> a -> Circ b
run_asciicirc subs f es = evalStateT (f es) (empty_wirestate subs)

-- | A CircInfoState can be turned into a Circ producing function, and the required
-- input "shape".
run :: Maybe [(Wire,Wiretype)] -> [Gate] -> Map BoxId Sub -> CircInfoState -> ([Endpoint],[Endpoint] -> Circ [Endpoint])
run mins gates subs cis = (ins,circ)
 where
  d_ins = defined_inputs cis
  d_outs = defined_outputs cis
  u_ins = map set_qubit (undefined_inputs cis)
  d_es = map (\(w,wt) -> endpoint_of_wire w wt) d_ins
  u_es = map (\(w,wt) -> endpoint_of_wire w wt) u_ins
  ins = case mins of 
         Nothing -> (d_es ++ sortBy (\e1 e2 -> compare (wire_of_endpoint e1) (wire_of_endpoint e2)) u_es)
         Just wts -> map (\(w,wt) -> endpoint_of_wire w wt) wts
  asciicirc = run_gates gates d_outs ins
  circ = run_asciicirc subs asciicirc

-- | If the type of an undefined_input wire is unknown, then set it to
-- be a qubit.
set_qubit :: (Wire,Maybe Wiretype) -> (Wire,Wiretype)
set_qubit (w,Just wt) = (w,wt)
set_qubit (w,Nothing) = (w,Qbit)
