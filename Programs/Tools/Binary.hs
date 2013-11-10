-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This tool decomposes a circuit into binary gates.

module Main where

import Quipper
import QuipperLib.QuipperASCIIParser
import QuipperLib.Decompose

-- | Main function: read from 'stdin', do the decomposition, and write
-- to 'stdout'.
main :: IO ()
main = do
  (ins,circuit) <- parse_from_stdin
  let decomposed_circuit = decompose_generic Binary circuit
  print_generic ASCII decomposed_circuit ins
