-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This tool reads a circuit from standard input and converts it to
-- the graphical EPS format. The converted circuit is written to
-- standard output.

module Main where

import Quipper
import QuipperLib.QuipperASCIIParser

-- | Main function: read from 'stdin' and write to 'stdout'.
main :: IO ()
main = do
  (ins,circuit) <- parse_from_stdin
  print_generic EPS circuit ins
