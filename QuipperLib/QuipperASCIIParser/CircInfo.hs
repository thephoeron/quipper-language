-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This module uses a state monad to track certain circuit information
-- that is collected during parsing. This information contains
-- the inputs and outputs of a circuit, as well as an entry for each subroutine
-- that is defined within a circuit, and all the gates that make up the circuit.

module QuipperLib.QuipperASCIIParser.CircInfo where

import QuipperLib.QuipperASCIIParser.Parse (GatePlus (..),parse_ascii_line)

import Quipper
import Quipper.Circuit
import Quipper.Monad

import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map

-- ----------------------------------------------------------------------
-- * Data-types for the State

-- | Information collected about the current subroutine
data Sub = Sub {
   name :: String,
   shape :: String,
   controllable :: ControllableFlag,
   inputs :: [(Wire,Wiretype)],
   outputs :: [(Wire,Wiretype)],
   circuit :: [Gate]
 }

-- | An initial subroutine, with only a name
new_subroutine :: String -> Sub
new_subroutine n = Sub {name = n, shape = "", controllable = NoCtl, inputs = [], outputs = [], circuit = []}

-- | A 'CircInfoState' is a record containing a list of input wires, along with their
-- types, and a list of output wires, along with their types. We also keep track of 
-- whether we're in a subroutine definition, and all the subroutines that have been 
-- defined.
data CircInfoState = CircInfoState {
 used_wires :: Map Wire (Maybe Wiretype),
 defined_inputs :: [(Wire,Wiretype)],
 undefined_inputs :: [(Wire,Maybe Wiretype)],
 defined_outputs :: Maybe [(Wire,Wiretype)],
 current_subroutine :: [Sub]
 }

-- | An initial, empty CircInfoState
empty_circinfostate :: CircInfoState
empty_circinfostate = CircInfoState { used_wires = Map.empty, defined_inputs = [], 
 undefined_inputs = [], defined_outputs = Nothing, current_subroutine = [] }

-- | The 'CircInfo' Monad is used to track a 'CircInfoState' during parsing.
type CircInfo a = State CircInfoState a

-- | The CircInfo Monad tracks wires that are inputs, these can only be given in
-- a "Input" line in the parsed ASCII, so we assume that duplicate wires don't
-- occur, and we add input wires to the state without checking.
add_wire_inputs :: [(Wire,Wiretype)] -> CircInfo ()
add_wire_inputs ws = do
  state <- get
  let ms = current_subroutine state
  case ms of
   [] -> do
    let ins = defined_inputs state
    let wires = used_wires state
    put (state {defined_inputs = ws ++ ins, 
     used_wires = Map.fromList (map (\(w,wt) -> (w,Just wt)) ws)})
   (sub:rest) -> do 
    let ins = inputs sub
    let sub' = sub {inputs = ins ++ ws}
    put (state {current_subroutine = (sub':rest)})

-- | The CircInfo Monad tracks wires that are outputs, these can only be given in
-- a "Output" line in the parsed ASCII, so we assume that duplicate wires don't
-- occur, and we add output wires to the state without checking.
add_wire_outputs :: [(Wire,Wiretype)] -> CircInfo ()
add_wire_outputs ws = do
  state <- get
  let ms = current_subroutine state
  case ms of
   [] -> do
    case defined_outputs state of
     Nothing -> put (state {defined_outputs = Just ws})
     Just outs -> put (state {defined_outputs = Just (outs ++ ws)})
   (sub:rest) -> do 
    let outs = outputs sub
    let sub' = sub {outputs = outs ++ ws}
    put (state {current_subroutine = (sub':rest)})

-- | Given a a wire, check whether it is already in scope.
check_input :: Map Wire (Maybe Wiretype) -> (Wire,Maybe Wiretype) -> Bool
check_input wires (w,wt) = case Map.lookup w wires of
                            Just wt -> False
                            Nothing -> True

-- | Given a list of wires that are inputs to a gate, check whether they
-- are already in scope. The returned wires are not in scope, when used by a gate,
-- and must be declared as undefined inputs.
check_inputs :: [(Wire,Maybe Wiretype)] -> Map Wire (Maybe Wiretype) -> [(Wire,Maybe Wiretype)]
check_inputs ins wires = filter (check_input wires) ins

-- | The CircInfo Monad keeps track of all the gates that have been parsed
-- and adds them to the relevant part of the state.
add_gate :: Gate -> [(Wire,Wiretype)] -> CircInfo CircInfoOut
add_gate gate ctws = do
  state <- get
  let ms = current_subroutine state
  case ms of
    [] -> do
     let wires = used_wires state
     let ui = undefined_inputs state
     let (ws_in,ws_out) = gate_arity gate
     let ws = wirelist_of_gate gate
     let ws_unchecked = filter (\w -> (notElem w (map fst ws_in)) 
                                   && (notElem w (map fst ws_out))
                                   && (notElem w (map fst ctws))) ws 
     let ws_in' = (map (\(w,wt) -> (w, Just wt)) (ws_in ++ ctws))
                   ++ (zip ws_unchecked (repeat Nothing))
     let ui' = ui ++ check_inputs ws_in' wires
     let wires' = Map.union wires (Map.fromList (ws_in' 
                   ++ (map (\(w,wt) -> (w, Just wt)) ws_out)))
     put (state {used_wires = wires',undefined_inputs = ui'})
     return (Lazy gate)
    (sub:rest) -> do
     let gates = circuit sub
     let gates' = gate:gates
     let sub' = sub {circuit = gates'}
     put (state {current_subroutine = (sub':rest)})
     return Empty

-- | The CircInfo Monad tracks whether we are in a subroutine, and collects info
-- about that subroutine. The entrance to the subroutine contains its name.
enter_subroutine :: String -> CircInfo ()
enter_subroutine name = do
  state <- get
  let ms = current_subroutine state
  put (state {current_subroutine = ((new_subroutine name):ms)})

-- | We can add the shape to the current subroutine
add_subroutine_shape :: String -> CircInfo ()
add_subroutine_shape s = do
  state <- get
  let ms = current_subroutine state
  case ms of
    [] -> error "Shape given outside of Subroutine Definition"
    (sub:rest) -> put (state {current_subroutine = ((sub {shape = s}):rest)})

-- | The CircInfo Monad tracks whether we are in a subroutine, and collects info
-- about that subroutine. The subroutine might be controllable.
set_controllable :: ControllableFlag -> CircInfo ()
set_controllable val = do
  state <- get
  let ms = current_subroutine state
  case ms of
    [] -> error "Controllable not in Subroutine Definition" 
    (sub:rest) -> put (state {current_subroutine = ((sub {controllable = val}):rest)})

-- | A datatype to represent the various outputs a CircInfo computation
-- may require.
data CircInfoOut = Empty | Lazy Gate | SubDef (BoxId,Sub)

-- | This function returns True if the given input defines a Gate
isGate :: CircInfoOut -> Bool
isGate (Lazy _) = True
isGate _ = False

-- | This function returns True if the given inputs defines a SubDef
isSub :: CircInfoOut -> Bool
isSub (SubDef _) = True
isSub _ = False

-- | The CircInfo Monad tracks whether we are in a subroutine, and collects info
-- about that subroutine. At the end of the subroutine, it stores the subroutine
-- for later use.
exit_subroutine :: CircInfo CircInfoOut
exit_subroutine = do
  state <- get
  let ms = current_subroutine state
  case ms of
    [] -> return Empty
    (sub:rest) -> do
      let n = name sub
      let s = shape sub
      put (state {current_subroutine = rest})
      return (SubDef ((BoxId n s),sub))

-- | Take a GatePlus  and execute it in the 'CircInfo' monad.
-- Again, the executed computation may depend upon whether we're in a subroutine
-- definition.
do_gate :: GatePlus -> CircInfo CircInfoOut
do_gate (G gate wts) = add_gate gate wts
do_gate (I ws) = add_wire_inputs ws >> return Empty
do_gate (O ws) = do
 add_wire_outputs ws
 exit_subroutine
do_gate EmptyLine = return Empty
do_gate (CommentLine comment) = return Empty
do_gate (SubroutineName name) = enter_subroutine name >> return Empty
do_gate (SubroutineShape shape) = add_subroutine_shape shape >> return Empty
do_gate (Controllable b) = set_controllable b >> return Empty

-- | Monad version of 'parse_ascii_line': parse a string and execute the
-- resulting gate directly in the 'CircInfo' monad.
run_ascii_line :: String -> CircInfo CircInfoOut
run_ascii_line s = case parse_ascii_line s of
                    Nothing -> error ("unrecognized line: " ++ show s)
                    Just p -> do_gate p

-- | Parse a stream consisting of many lines of ASCII output and execute
-- the parsed gates in the 'CircInfo' monad, checking to see if the first
-- line defines the inputs to the circuit.
run_ascii_lines :: [String] -> (Maybe [(Wire,Wiretype)],CircInfo [CircInfoOut])
run_ascii_lines [] = (Nothing,return [])
run_ascii_lines [f] =  case parse_ascii_line f of
  Just (I ws) -> (Just ws, return [])
  _ -> (Nothing, run_ascii_line f >>= \x -> return [x])
-- Special case:
-- If the first line contains the input wires, we should 
-- be able to parse the circuit lazily (e.g. it is a full circuit), as
-- we don't have to parse all the gates to calculate the inputs.
run_ascii_lines (f:s) = 
  case parse_ascii_line f of
   Just (I ws) -> (Just ws, mapM run_ascii_line s)
   _ -> (Nothing, mapM run_ascii_line (f:s))
   
-- | Run function for the 'CircInfo' monad: evaluate the state and
-- produce a list of inputs, outputs, and used wires.
run :: CircInfo [CircInfoOut] -> ([Gate],Map BoxId Sub,CircInfoState)
run f = (gs, subs, cis)
 where
  gs = [x | Lazy x <- filter isGate ci_outs]
  subs = Map.fromList [x | SubDef x <- filter isSub ci_outs] 
  (ci_outs,cis) = runState f empty_circinfostate

