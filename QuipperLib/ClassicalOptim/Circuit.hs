-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides a simplified representation of classical
-- circuits.
module QuipperLib.ClassicalOptim.Circuit where

import qualified Data.Map as M
import qualified Data.List as L
import qualified Libraries.Auxiliary as Q

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)

-- ----------------------------------------------------------------------
-- * Simplified circuits

-- | The type of wires. A wire is determined by an integer ID.
type Wire = Int

-- | The type of gates.
data Gate = 
    NoOp                      -- ^ No operation.
  | Init Bool Wire            -- ^ Initialization.
  | Cnot Wire [(Wire,Bool)]   -- ^ Multi-controlled not.
    deriving (Show,Eq)

-- | Get the wire acted upon by a gate, if any.
wireOfGate :: Gate -> Maybe Wire
wireOfGate NoOp = Nothing
wireOfGate (Init _ w) = Just w
wireOfGate (Cnot w _) = Just w

-- | Get the list of controls, if any.
ctlsOfGate :: Gate -> Maybe [(Wire,Bool)]
ctlsOfGate (Cnot _ ctls) = Just ctls
ctlsOfGate _ = Nothing

-- | Evaluate a circuit on a given initial state, and return the final
-- state. A state is represented as a map from wires to booleans.
evalCirc :: M.Map Wire Bool -> [Gate] -> M.Map Wire Bool
evalCirc m [] = m
evalCirc m (NoOp:gs) = evalCirc m gs
evalCirc m ((Init b w):gs) = evalCirc (M.insert w b m) gs
evalCirc m ((Cnot w ctls):gs) = evalCirc (M.adjust (Q.bool_xor (ands m ctls)) w m) gs
     where
       ands m [] = True
       ands m ((w,b):ctls) = ((m M.! w) `Q.bool_xor` (not b)) && (ands m ctls)

-- ----------------------------------------------------------------------
-- * Simplified Circ monad

-- | A data structure to represent a \"circuit under
-- construction\". This holds the data needed for circuit generation.
data CircState = CS {
  circuit :: [Gate],  -- ^ The circuit so far.
  freshWire :: Wire   -- ^ The next fresh wire.
} deriving (Show)

-- | The empty state.
emptyState :: CircState
emptyState = CS {circuit = [], freshWire = 0}

-- | A simplified @Circ@ monad.
data Circ a =  Circ (CircState -> (CircState, a))

instance Monad Circ where
  return x = Circ (\y -> (y,x))
  (>>=) (Circ c) f = Circ (\s -> let (s',x) = c s in
                                 let (Circ c') = f x in
                                 c' s')

instance Applicative Circ where
  pure = return
  (<*>) = ap

instance Functor Circ where
  fmap = liftM

-- ----------------------------------------------------------------------
-- * Low-level access functions

-- | Retrieve the next fresh wire.
getFresh :: Circ Wire
getFresh = Circ (\s -> (s, freshWire s))

-- | Increment the value of the fresh wire.
incrementFresh :: Circ ()
incrementFresh = Circ (\s -> (s { freshWire = freshWire s + 1 }, ()))

-- | Add a new gate to the circuit.
addGate :: Gate -> Circ ()
addGate g = Circ (\s -> (s {circuit = g : (circuit s)}, ()))

-- | Get the circuit out of the monad.
extractCircuit :: Circ a -> [Gate]
extractCircuit (Circ c) = circuit $ fst $ c emptyState

-- ----------------------------------------------------------------------
-- * Higher-level access functions

-- | Initialize a new wire.
init :: Bool -> Circ Wire
init b = do
  w <- getFresh
  addGate (Init b w)
  incrementFresh
  return w

-- | Add a multi-controlled not gate.
cnot :: Wire -> [(Wire,Bool)] -> Circ ()
cnot w ws = do
  addGate (Cnot w ws)
  return ()

-- ----------------------------------------------------------------------
-- * Pretty-printing

-- $ These functions are only used for testing.

-- | Pretty-print a circuit as a list of gates.
printCircuit :: Circ a -> IO ()
printCircuit c = do
  mapM_ putStrLn $ map show $ reverse $ extractCircuit c 

-- | Print a gate as Quipper code.
print_quipperStyle :: Gate -> IO ()
print_quipperStyle (Init b w) = putStrLn ("  x" ++ (show w) ++ " <- Q.qinit " ++ (show b))
print_quipperStyle (Cnot w ctls) = putStrLn ("  Q.qnot x" ++ (show w) ++ " `Q.controlled` " ++ 
                                             (L.intercalate " Q..&&. " $ map (\(w,b) -> "x" ++ (show w) ++ " Q..==. " ++ (show b) ++ " ") ctls))
print_quipperStyle g = putStrLn ("  Q.comment \"" ++ (show g) ++ "\"")
