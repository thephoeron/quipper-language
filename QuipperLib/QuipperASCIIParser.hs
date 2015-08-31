-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This module is the main interface to the QuipperASCIIParser
-- library.  It provides functions for parsing circuits in the ASCII
-- format written by 'print_generic' and similar functions.

module QuipperLib.QuipperASCIIParser where

import qualified QuipperLib.QuipperASCIIParser.CircInfo as CI
import qualified QuipperLib.QuipperASCIIParser.ASCIICirc as AC

import Quipper
import Quipper.Monad

import Libraries.PortableSignals
import System.IO
import Data.List

-- | Parse a string containing a circuit in the format output by
-- Quipper's ASCII format. Return a circuit producing function of the
-- parsed circuit, along with a specimen \"shape\" for the input of
-- the parsed circuit.
parse_circuit :: String -> ([Endpoint],[Endpoint] -> Circ [Endpoint])
parse_circuit all_lines = AC.run mins gates subs circ_info
 where
  split_lines = lines' all_lines
  (mins, ci) = CI.run_ascii_lines split_lines
  (gates,subs,circ_info) = CI.run ci


-- | Like 'lines', except that the last line is omitted if it doesn't
-- end with a newline character
lines' :: String -> [String]
lines' [] = []
lines' s = case elemIndex '\n' s of
            Nothing -> []
            Just n -> (take (n) s):lines' (drop (n+1) s)

-- | Like 'parse_circuit', but read the circuit from the standard
-- input stream, rather than from a string. This can be used to build
-- stand-alone tools that process circuits in a pipeline. 
parse_from_stdin :: IO ([Endpoint], [Endpoint] -> Circ [Endpoint])
parse_from_stdin = do
  all_lines <- hGetContents stdin  
  return $ parse_circuit all_lines

-- | Like 'parse_from_stdin', but as a special convenience, this 
-- function also installs a signal handler that will intercept the first 
-- kill signal (e.g., Ctrl-C) and close the standard input stream. 
-- This means that whichever part of the circuit was generated before the 
-- first Ctrl-C can still be processed as a partial circuit. Note that the 
-- second kill signal will still kill the program. Note that this is only
-- defined for Non-Windows OS environments.
parse_from_stdin_with_handler :: IO ([Endpoint], [Endpoint] -> Circ [Endpoint])
parse_from_stdin_with_handler = do
  installHandler Interrupt (CatchOnce (hClose stdin))
  all_lines <- hGetContents stdin  
  return $ parse_circuit all_lines
