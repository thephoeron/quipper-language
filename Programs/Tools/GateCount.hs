-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This tool reads a circuit from standard input and calculates gate
-- counts.

module Main where

import Quipper
import QuipperLib.QuipperASCIIParser

-- | Main function: read from 'stdin', and write gate counts to
-- 'stdout'.
main :: IO ()
main = do
  (ins,circuit) <- parse_from_stdin
  print_generic GateCount circuit ins
