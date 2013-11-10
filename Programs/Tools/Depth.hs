-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This tool reads a circuit from standard input and outputs its depth. 

module Main where

import Quipper
import Quipper.Circuit
import Quipper.Monad
import Quipper.Transformer
import Libraries.Auxiliary

import QuipperLib.QuipperASCIIParser

import qualified Data.Map as Map
import qualified Data.IntMap as IntMap

import Data.Maybe
import Control.Monad
import Data.List
import Control.Monad.State

-- | Main function: read from 'stdin' and calculate the depth. 
main :: IO ()
main = do
  (ins,circuit) <- parse_from_stdin
  let depth_circ = transform_generic_shape depth_transformer circuit ins
  let ws = map wire_of_endpoint ins
  let ws' = map endpoint_of_endpoint ins
  let state = execState (depth_circ ws') (initial_depthstate ws)
  let result = global_depth state
  putStrLn ("Depth: " ++ show result)
  putStrLn ("T-Depth: " ++ show (global_tdepth state))

-- | Extract wires from an endpoint, keeping track of whether it was
-- a classical or quantum endpoint.
endpoint_of_endpoint :: B_Endpoint Qubit Bit -> B_Endpoint Wire Wire
endpoint_of_endpoint (Endpoint_Qubit q) = Endpoint_Qubit (wire_of_qubit q)
endpoint_of_endpoint (Endpoint_Bit b) = Endpoint_Bit (wire_of_bit b)

-- | A data structure to hold information about the current depths 
data DepthState = DS {
   global_depth  :: !Integer,  
   wire_depths   :: !(XIntMap Integer),
   global_tdepth :: !Integer,
   wire_tdepths  :: !(XIntMap Integer)
  }

-- | The initial state of the depth information depends on the wires
-- that are inputs to a circuit.
initial_depthstate :: [Wire] -> DepthState
initial_depthstate ws = DS { global_depth = 0, wire_depths = foldr (\w -> xintmap_insert w 0) xintmap_empty ws, 
                           global_tdepth = 0, wire_tdepths = foldr (\w -> xintmap_insert w 0) xintmap_empty ws }

-- | We use a State Monad to carry our state
type Depth a = State DepthState a

-- | Given a list of wires, lookup the current depth
-- of each wire, and return the maximum
input_depth :: [Wire] -> Depth (Integer,Integer)
input_depth ws = do
  state <- get
  let wd = wire_depths state
  let ds = map (\w -> fromJust (xintmap_lookup w wd)) ws
  let maxds = 
        case ds of
          [] -> 0
          ds -> maximum ds
  let wtd = wire_tdepths state
  let tds = map (\w -> fromJust (xintmap_lookup w wtd)) ws
  let maxtds = 
        case tds of
          [] -> 0
          tds -> maximum tds
  return (maxds, maxtds)

-- | Given a current depth, and a list of wires, update
-- the depth of each wire, to be one more than the current
-- depth. Also, update the global depth, if necessary.
update_depths :: (Integer,Integer) -> [Wire] -> Bool -> Depth ()
update_depths (old_depth,old_tdepth) ws addt = do
 let new_depth = old_depth + 1
 state <- get
 let gd = global_depth state
 let gd' = if gd < new_depth then new_depth else gd
 let wd = wire_depths state
 let wd' = foldr (\w -> xintmap_insert w new_depth) wd ws
 
 let new_tdepth = if addt then old_tdepth + 1 else old_tdepth
 let gdt = global_tdepth state
 let gdt' = if gdt < new_tdepth then new_tdepth else gdt
 let wdt = wire_tdepths state
 let wdt' = foldr (\w -> xintmap_insert w new_tdepth) wdt ws
 put (state {global_depth = gd', wire_depths = wd', global_tdepth = gdt', wire_tdepths = wdt'})

-- | A helper function to combine a list of wires, and
-- a list of controls, into a single list of wires.
wires_of :: [Wire] -> Ctrls Wire Wire -> [Wire]
wires_of ws c = ws ++ (map wire_of_ctrl c)
 where
  wire_of_ctrl :: Signed (B_Endpoint Wire Wire) -> Wire
  wire_of_ctrl (Signed (Endpoint_Qubit w) _) = w
  wire_of_ctrl (Signed (Endpoint_Bit w) _) = w

same_in_out :: Wire -> Ctrls Wire Wire -> Depth (Wire,Ctrls Wire Wire)
same_in_out w c = do
   let inputs = wires_of [w] c
   depth <- input_depth inputs
   let outputs = inputs
   update_depths depth outputs False
   return (w,c)

same_in_out2 :: Wire -> Wire -> Ctrls Wire Wire -> Depth (Wire,Wire,Ctrls Wire Wire)
same_in_out2 w v c = do
   let inputs = wires_of [w,v] c
   depth <- input_depth inputs
   let outputs = inputs
   update_depths depth outputs False
   return (w,v,c)

same_in_out_multi_t :: [Wire] -> Ctrls Wire Wire -> Depth ([Wire],Ctrls Wire Wire)
same_in_out_multi_t ws c = do
   let inputs = wires_of ws c
   depth <- input_depth inputs
   let outputs = inputs
   update_depths depth outputs True
   return (ws,c)  

same_in_out_multi :: [Wire] -> Ctrls Wire Wire -> Depth ([Wire],Ctrls Wire Wire)
same_in_out_multi ws c = do
   let inputs = wires_of ws c
   depth <- input_depth inputs
   let outputs = inputs
   update_depths depth outputs False
   return (ws,c)  

init_wire :: [Wire] -> Depth Wire
init_wire ws =   do
   let inputs = ws
   depth <- input_depth inputs
   state <- get
   let wires = wire_depths state
   let b = xintmap_freshkey wires
   let outputs = [b]
   update_depths depth outputs False
   return b

term_wire :: [Wire] -> Wire -> Depth ()
term_wire inputs w = do
   depth <- input_depth inputs
   let new_depth = fst(depth) + 1
   state <- get
   let gd = global_depth state
   let gd' = if gd < new_depth then new_depth else gd
   put (state {global_depth = gd'})
   return ()

depth_transformer :: Transformer (State DepthState) Wire Wire
-- Translation of classical gates:
depth_transformer (T_CNot ncf f) = f same_in_out
depth_transformer (T_CInit val ncf f) = f $ init_wire []
depth_transformer (T_CTerm b ncf f) = f $ term_wire []
depth_transformer (T_CDiscard f) = f $ term_wire []
depth_transformer (T_DTerm b f) = f $ term_wire []
depth_transformer (T_CGate name ncf f) = f $
  \ws -> do
   v <- init_wire ws
   return (v,ws) 
depth_transformer g@(T_CGateInv name ncf f) = f $
  \v ws -> do
   term_wire ws v
   return ws
-- Translation of quantum gates:
depth_transformer (T_QGate "trace" _ _ inv ncf f) = f $
  \ws vs c -> return (ws, vs, c) -- don't count a trace gate
depth_transformer (T_QGate "T" _ _ inv ncf f) = f $ 
  \qs gcs c -> do
   same_in_out_multi_t (qs++gcs) c
   return (qs,gcs,c)
depth_transformer (T_QGate name _ _ inv ncf f) = f $ 
  \qs gcs c -> do
   same_in_out_multi (qs++gcs) c 
   return (qs,gcs,c)
depth_transformer (T_QRot name _ _ inv theta ncf f) = f $ 
  \qs gcs c -> do
   same_in_out_multi (qs++gcs) c 
   return (qs,gcs,c)
depth_transformer (T_GPhase t ncf f) = f $
  \w c -> do
  same_in_out_multi [] c
  return c
depth_transformer (T_QInit val ncf f) = f $ init_wire []
depth_transformer (T_QMeas f) = f $
  \q -> do
   same_in_out q []
   return q
depth_transformer (T_QDiscard f) = f $ term_wire []
depth_transformer (T_QTerm b ncf f) = f $ term_wire []
depth_transformer (T_Comment name inv f) = f $
  \ws -> return () -- don't count a comment
depth_transformer g@(T_CSwap ncf f) = f same_in_out2
depth_transformer g@(T_QPrep ncf f) = f $
  \w -> error ("depth_transformer: unimplemented gate: " ++ show g)
depth_transformer g@(T_QUnprep ncf f) = f $
  \w -> error ("depth_transformer: unimplemented gate: " ++ show g)
depth_transformer g@(T_Subroutine n inv ncf scf ws_pat a1 vs_pat a2 rflg f) = f $
 \ns ws c -> do
  case Map.lookup n ns of
   Just (TypedSubroutine sub_ocirc _ _ _) -> do
    let RepeatFlag reps = rflg
    let OCircuit (in_wires, sub_circ, out_wires) = if inv then reverse_ocircuit sub_ocirc else sub_ocirc
    let in_bindings = bind_list in_wires ws bindings_empty
    let sub_bcirc = (sub_circ,ns)
    state_in <- get
    out_bind <- transform_bcircuit_rec depth_transformer sub_bcirc in_bindings
    state_out <- get
    put (rep_change reps state_in state_out)
    return (unbind_list out_bind out_wires, c) 
   Nothing -> error $ "depth_transformer: subroutine " ++ show n ++ " not found (in " ++ showNames ns ++ ")"

-- | The following function updates the state by multiplying the differences between
-- the given /state_out/ and the given /state_in/ by the given number of repetitions.
rep_change :: Integer -> DepthState -> DepthState -> DepthState
rep_change reps state_in state_out = DS {
 global_depth = new_global_depth,
 wire_depths = new_wire_depths,
 global_tdepth = new_global_tdepth,
 wire_tdepths = new_wire_tdepths
 }
 where
   in_global_depth = global_depth state_in
   out_global_depth = global_depth state_out
   new_global_depth = in_global_depth + (reps * (out_global_depth - in_global_depth))
   in_wire_depths = wire_depths state_in
   out_wire_depths = wire_depths state_out
   out_wire_depths_list = IntMap.toList (xintmap_to_intmap (out_wire_depths))
   new_depths = map (\(w,v_out) -> (w,
    case (xintmap_lookup w in_wire_depths) of
     Nothing -> v_out * reps
     Just v_in ->
      case v_in > v_out of
       True -> reps * v_out 
       False -> v_in + (reps * (v_out - v_in)))) out_wire_depths_list
   new_wire_depths = xintmap_inserts new_depths out_wire_depths
   in_global_tdepth = global_tdepth state_in
   out_global_tdepth = global_tdepth state_out
   new_global_tdepth = in_global_tdepth + (reps * (out_global_tdepth - in_global_tdepth))
   in_wire_tdepths = wire_tdepths state_in
   out_wire_tdepths = wire_tdepths state_out
   out_wire_tdepths_list = IntMap.toList (xintmap_to_intmap (out_wire_tdepths))
   new_tdepths = map (\(w,v_out) -> (w,
    case (xintmap_lookup w in_wire_tdepths) of
     Nothing -> v_out * reps
     Just v_in ->
      case v_in > v_out of
       True -> reps * v_out 
       False -> v_in + (reps * (v_out - v_in)))) out_wire_tdepths_list
   new_wire_tdepths = xintmap_inserts new_tdepths out_wire_tdepths
