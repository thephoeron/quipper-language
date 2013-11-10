-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This tool is the identity function on circuits: it reads a
-- circuit from standard input, and then outputs the same circuit to
-- standard output. This program serves as an illustration for how to
-- write the simplest kind of standalone circuit processing tool.

module Main where

import Quipper
import QuipperLib.QuipperASCIIParser

-- | Main function: read from 'stdin', then write to 'stdout'. 
main :: IO ()
main = do
  (ins,circuit) <- parse_from_stdin
  print_generic ASCII circuit ins
