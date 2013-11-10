-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides some functions that are useful in the
-- processing of command line options, and that are shared between
-- several algorithms.

module Libraries.CommandLine where

import Libraries.Auxiliary (string_of_list)

-- import other stuff
import System.Exit
import System.IO
import Data.List
import Data.Char

-- ----------------------------------------------------------------------
-- * Option processing
      
-- | Exit with an error message after a command line error. This also
-- outputs information on where to find command line help.
optfail :: String -> IO a
optfail msg = do
  hPutStr stderr msg
  hPutStrLn stderr "Try --help for more info."
  exitFailure

-- | Parse a string to an integer, or return 'Nothing' on failure.
parse_int :: (Integral r) => String -> Maybe r
parse_int s = case reads s of
  [(n, "")] -> Just (fromInteger n)
  _ -> Nothing

-- | Parse a string to a list of integers, or return 'Nothing' on failure.
parse_list_int :: String -> Maybe [Int]      
parse_list_int s = case reads s of
  [(ns, "")] -> Just ns
  _ -> Nothing

-- | Parse a string to a 'Double', or return 'Nothing' on failure.
parse_double :: String -> Maybe Double
parse_double s = case reads s of
  [(n, "")] -> Just n
  _ -> Nothing

-- | In an association list, find the key that best matches the given
-- string. If one key matches exactly, return the corresponding
-- key-value pair. Otherwise, return a list of all key-value pairs
-- whose key have the given string as a prefix. This list could be of
-- length 0 (no match), 1 (unique match), or greater (ambiguous key).
-- Note: the keys in the association list must be lower case. The
-- input string is converted to lower case as well, resulting in
-- case-insensitive matching.
match_enum :: [(String, a)] -> String -> [(String, a)]
match_enum list key =
  case lookup s list of
    Just v -> [(s,v)]
    Nothing -> filter (\(k,v) -> isPrefixOf s k) list
  where
    s = map toLower key
    
-- | Pretty-print a list of possible values for a parameter. The
-- first argument is the name of the parameter, and the second
-- argument is its enumeration.
show_enum :: String -> [(String, a)] -> String    
show_enum param list =
  "Possible values for " ++ param ++ " are: " ++
  string_of_list "" ", " "" "no possible values" fst list ++ ".\n"
