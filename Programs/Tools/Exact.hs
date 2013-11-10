-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This tool decomposes all gates that permit exact Clifford+/T/
-- representations into the following concrete gate base for
-- Clifford+/T/:
-- 
-- * controlled-not (with one positive or negative control),
-- 
-- * any single-qubit Clifford gates,
-- 
-- * /T/ and /T/[sup †].
-- 
-- Classical controls and classical gates are not subject to the gate
-- base, and are left untouched.
module Main where

import Quipper
import QuipperLib.QuipperASCIIParser
import QuipperLib.Decompose

-- | Main function: read from 'stdin', do the decomposition, and write
-- to 'stdout'.
main :: IO ()
main = do
  (ins,circuit) <- parse_from_stdin  
  let decomposed_circuit = decompose_generic Exact circuit
  print_generic ASCII decomposed_circuit ins
