-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This tool reads a circuit from standard input and displays it in
-- the previewer. For the previewer to work, Acrobat Reader must be
-- installed. 
-- 
-- Note that it is possible to interrupt the circuit generation with
-- Ctrl-C; in this case, the circuit generated up to that point will
-- be displayed. A second Ctrl-C will kill the program.

module Main where

import Quipper
import QuipperLib.QuipperASCIIParser

-- | Main function: read from 'stdin' and call the previewer. 
main :: IO ()
main = do
  (ins,circuit) <- parse_from_stdin_with_handler
  print_generic Preview circuit ins
