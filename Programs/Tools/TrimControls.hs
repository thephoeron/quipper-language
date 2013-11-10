-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This tool trims excess controls from gates. Specifically, it
-- decomposes a circuit so that:
-- 
-- * not-gates, Pauli /X/-, /Y/-, and /Z/-gates, and /iX/-gates have
-- at most two controls;
-- 
-- * phase gates of the form Diag(1, φ) have no controls; and
-- 
-- * all other gates have at most one control.
module Main where

import Quipper
import QuipperLib.QuipperASCIIParser
import QuipperLib.Decompose

-- | Main function: read from 'stdin', do the decomposition, and write
-- to 'stdout'.
main :: IO ()
main = do
  (ins,circuit) <- parse_from_stdin
  let decomposed_circuit = decompose_generic TrimControls circuit
  print_generic ASCII decomposed_circuit ins
