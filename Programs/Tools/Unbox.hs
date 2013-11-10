-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This tool unwinds a circuit by inlining all top-level boxed
-- subroutines.  It can sometimes be used to pre-process circuits for
-- use by other tools that may not yet work correctly with boxed
-- subroutines. Note, however, that this can substantially increase
-- the size of the circuit representation.
-- 
-- Note that only top-level boxed subroutines are inlined; the tool
-- may have to be applied several times to remove all levels of boxes.
-- 
-- This is only an illustration for how to write such tools; another
-- tool could be written that does \"deep\" unboxing.

module Main where

import Quipper
import QuipperLib.QuipperASCIIParser
import QuipperLib.Unboxing

-- | Main function: read from 'stdin', do the decomposition, and write
-- to 'stdout'.
main :: IO ()
main = do
  (ins,circuit) <- parse_from_stdin  
  let unboxed_circuit = unbox circuit
  print_generic ASCII unboxed_circuit ins
