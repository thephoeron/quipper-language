-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- ----------------------------------------------------------------------
-- | This module contains the code for parsing the ASCII output from
-- Quipper, into a GatePlus.
-- This program is heavily based on, and heavily borrows from the QCLParser.

module QuipperLib.QuipperASCIIParser.Parse where

import Quipper.Circuit
import Data.IntMap hiding (map)

import Text.ParserCombinators.ReadP
import Data.Char (isDigit)
import qualified Data.Map as Map

-- ----------------------------------------------------------------------
-- | A type for gates, plus other circuit output, empty lines, and subroutine defs.
data GatePlus = G Gate [(Wire,Wiretype)]
              | I [(Wire,Wiretype)]
              | O [(Wire,Wiretype)]
              | EmptyLine
              | CommentLine String
              | SubroutineName String
	      | SubroutineShape String
              | Controllable ControllableFlag
 deriving Show

-- ----------------------------------------------------------------------
-- * Parsing

-- | Parse a string literal. 
string_literal :: ReadP String
string_literal = do
  char '"'
  s <- string_with_escaped_chars ""
  char '"'
  return s
 where
  string_with_escaped_chars :: String -> ReadP String
  string_with_escaped_chars input = do
   s <- munch (\x -> x /= '\\' && x /= '"')
   let s'  = input ++ s
   rest <- look
   case rest of
    '"' : _ -> return s'
    '\\' : _ -> do
      e <- escaped_char
      string_with_escaped_chars (s' ++ [e])
    _ -> do
      pfail

-- | Parse an escaped character, such as @\0@, @\n@, @\\@, etc.
escaped_char :: ReadP Char
escaped_char = do
  char '\\'
  c <- get
  return (Map.findWithDefault c c map)
  where
    -- The official escape codes. We allow any other escaped character
    -- to denote itself. We do not permit "\&" to denote the empty string.
    map = Map.fromList [
      ('0', '\0'),
      ('a', '\a'),
      ('b', '\b'),
      ('f', '\f'),
      ('n', '\n'),
      ('r', '\r'),
      ('t', '\t'),
      ('v', '\v'),
      ('"', '\"'),
      ('\'', '\''),
      ('\\', '\\')
      ]

-- | Parse a signless integer. We avoid the usual trick ('readS_to_P'
-- 'reads'), because this introduces backtracking errors.
int :: ReadP Int
int = do
  s <- munch1 isDigit
  return $ (read s :: Int)

-- | Parse a floating point number. We avoid the usual trick
-- ('readS_to_P' 'reads'), because this introduces backtracking
-- errors.
double :: ReadP Double
double = do
  (s, _) <- gather parse_double
  return $ (read s :: Double)
  where
    parse_double = do
      option '+' (char '+' +++ char '-')
      munch isDigit
      optional (char '.' >> munch1 isDigit)
      optional (char 'e' >> option '+' (char '+' +++ char '-') >> int)
      
-- | Parse a comma separated list.
commalist :: ReadP a -> ReadP [a]
commalist elt = sepBy elt (skipSpaces >> char ',' >> skipSpaces)

-- | Parse a control structure.
control :: ReadP (Signed Wire,Wiretype)
control = do
  val <- choice [char '+',char '-']
  skipSpaces
  w <- int
  c <- option 'q' (char 'c')
  let wt = case c of
            'c' -> Cbit
            _ -> Qbit
  return (Signed w (val == '+'),wt)

-- | Parse a list of controls.
controls :: ReadP ([Signed Wire],[(Wire,Wiretype)])
controls = do
  skipSpaces
  string "with controls=["
  cwts <- commalist control
  char ']'
  let cs = map fst cwts
  let wts = map (\(Signed w _,wt) -> (w,wt)) cwts
  return (cs,wts)

-- | Parse a 'Wiretype'.
wiretype :: ReadP Wiretype
wiretype = do
  c <- choice [string "Qbit",string "Cbit"]
  case c of
    "Qbit" -> return Qbit
    "Cbit" -> return Cbit
    _ -> error "The impossible has happened"

-- | Parse a wire and its type.
wire :: ReadP (Int,Wiretype)
wire = do
  skipSpaces
  w <- int
  char ':'
  t <- wiretype
  return (w,t)

-- | Parse a list of input/output wires and types.
wires :: ReadP [(Int,Wiretype)]
wires = do
  skipSpaces
  ws <- commalist wire
  return ws

-- | Parse the string \"none\", 
-- returning an empty list of input/output wires and types.
none :: ReadP [(Int,Wiretype)]
none = do
  skipSpaces
  string "none"
  return []

-- | Consume an optional \"*\". Return 'True' if consumed, and 'False'
-- otherwise.
inversechar :: ReadP Bool  
inversechar = do
  c <- option '+' (char '*')
  return (c == '*')

-- | Consume a label.
label' :: ReadP (Int,String)
label' = do
  w <- int
  char ':'
  lab <- string_literal
  return (w,lab)

-- | Consumer any character other than \')\', \']\', or \',\'.
labelchar :: ReadP String
labelchar = do
  c <- satisfy (\x -> not (x `elem` ")],"))
  return [c]

-- | Consume an index of the form [...].
labelbracket :: ReadP String
labelbracket = do
  char '['
  s <- munch (\x -> not (x `elem` "[]"))
  char ']'
  return ("[" ++ s ++ "]")

-- | Consume a list of labels.
labels :: ReadP [(Int,String)]
labels = do
    skipSpaces
    char '('
    ls <- commalist label'
    char ')'
    return ls

-- | Consume a 'BoxId' followed by a \']\' character.
{-
ascii_of_boxid (BoxId name shape) = show name ++ ", shape " ++ show shape
-}
box_id :: ReadP BoxId
box_id = do
   name <- string_literal
   skipSpaces
   char ','
   skipSpaces
   string "shape"
   skipSpaces
   shape <- string_literal
   return (BoxId name shape)

-- | Consume an optional 'NoControlFlag', returning 'False' if it isn't present.
nocontrolflag :: ReadP NoControlFlag
nocontrolflag = do
 skipSpaces
 ncf <- option "" (string "with nocontrol")
 return (ncf == "with nocontrol")

-- | Parse a single line of ASCII output into a 'Gate'. This function needs to be
-- kept in line with Quipper's 'ascii_render_gate' function.
ascii_line :: ReadP GatePlus
ascii_line = choice [
    do -- Inputs: w:Type, w:Type ...
    string "Inputs:"
    ws <- choice [wires,none]
    eof
    return (I ws),
    do -- Outputs: w:Type, w:Type ...
    string "Outputs:"
    ws <- choice [wires,none]
    eof
    return (O ws),
    do -- An empty line can be parsed as an EmptyLine
    skipSpaces
    eof
    return EmptyLine,
    do -- "A comment in a circuit is any line beginnning with a # character"
    -- The comment is stored for later use as a CommentLine
    skipSpaces
    char '#'
    skipSpaces
    comment <- manyTill (satisfy (\_ -> True)) eof
    eof
    return (CommentLine comment),
    do -- Subroutine: "name" (keeping unquoted version for backward comp.)
    string "Subroutine: "
    name <- string_literal +++ manyTill (satisfy (\_ -> True)) eof
    eof
    return (SubroutineName name),
    do -- Shape: "shape" (keeping unquoted version for backward comp.)
    string "Shape: "
    shape <- string_literal +++ manyTill (satisfy (\_ -> True)) eof
    eof
    return (SubroutineShape shape),
    do -- Controllable: yes/no/classically
    string "Controllable: "
    val_string <- choice [string "yes",string "no", string "classically"]
    let val = case val_string of
               "yes" -> AllCtl
               "no" -> NoCtl
               "classically" -> OnlyClassicalCtl
               _ -> error "The impossible happened"
    eof
    return (Controllable val),
{-
For backward compatibility:
ascii_render_gate (QNot w c ncf) = 
  "QNot(" ++ show w ++ ")" 
  ++ ascii_render_controls wtm c 
  ++ ascii_render_nocontrolflag ncf
-}
    do 
    string "QNot("
    w <- int
    char ')'
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    return (G (QGate "not" False [w] [] cs ncf) wts),
{-
For backward compatibility:
ascii_render_gate (QMultinot ws c ncf) = 
  "QMultinot(" ++ string_of_list "" ", " "" "" show ws ++ ")" 
  ++ ascii_render_controls wtm c 
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QMultinot("
    ws <- commalist int
    char ')'
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    return (G (QGate "multinot" False ws [] cs ncf) wts),    
{-
For backward compatibility:
ascii_render_gate (QHad w c ncf) = 
  "QHad(" ++ show w ++ ")" 
  ++ ascii_render_controls wtm c 
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QHad("
    w <- int
    char ')'
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    return (G (QGate "H" False [w] [] cs ncf) wts),
{-
For backward compatibility:
ascii_render_gate (QSwap w1 w2 c ncf) = 
  "QSwap(" ++ show w1 ++ "," ++ show w2 ++ ")" 
  ++ ascii_render_controls wtm c 
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QSwap("
    w1 <- int
    char ','
    w2 <- int
    char ')'
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    return (G (QGate "swap" False [w1, w2] [] cs ncf) wts),
{-
For backward compatibility:
ascii_render_gate (QW w1 w2 c ncf) = 
  "QW(" ++ show w1 ++ "," ++ show w2 ++ ")" 
  ++ ascii_render_controls wtm c 
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QW("
    w1 <- int
    char ','
    w2 <- int
    char ')'
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    return (G (QGate "W" False [w1, w2] [] cs ncf) wts),
{-
ascii_render_gate (GPhase t ws c ncf) = 
  "GPhase() with t=" ++ show t 
  ++ ascii_render_controls wtm c 
  ++ ascii_render_nocontrolflag ncf
  ++ string_of_list " with anchors=[" ", " "]" "" show ws
-}
    do
    string "GPhase() with t="
    t <- double
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    ws <- option [] (do
      skipSpaces
      string "with anchors=["
      ws <- commalist int
      char ']'
      return ws )
    eof
    return (G (GPhase t ws cs ncf) wts),
{-
ascii_render_gate (QGate name inv ws1 ws2 c ncf) = 
  "QGate[" ++ show name ++ "]" 
  ++ optional inv "*" 
  ++ (string_of_list "(" "," ")" "()" show ws1)
  ++ (string_of_list "; [" "," "]" "" show ws2)
  ++ ascii_render_controls wtm c
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QGate["
    name <- string_literal
    char ']'
    inv <- inversechar
    char '('
    ws1 <- commalist int
    char ')'
    ws2 <- option [] (do
      string "; ["
      ws <- commalist int
      char ']'
      return ws )
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    return (G (QGate name inv ws1 ws2 cs ncf) wts),   
{-
ascii_render_gate (QRot name inv theta ws1 ws2 c ncf) = 
  "QRot[" ++ show name ++ "," ++ (show theta) ++ "]" 
  ++ optional inv "*"
  ++ (string_of_list "(" "," ")" "()" show ws1)
  ++ (string_of_list "; [" "," "]" "" show ws2)
  ++ ascii_render_controls wtm c
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QRot["
    name <- string_literal
    char ','
    theta <- double
    char ']'
    inv <- inversechar
    char '('
    ws1 <- commalist int
    char ')'
    ws2 <- option [] ( do
      string "; ["
      ws <- commalist int
      char ']'
      return ws )
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    return (G (QRot name inv theta ws1 ws2 cs ncf) wts),
{-
ascii_render_gate (CNot w c ncf) = 
  "CNot(" ++ show w ++ ")" 
  ++ ascii_render_controls wtm c
  ++ ascii_render_nocontrolflag ncf
-}
    do 
    string "CNot("
    w <- int
    char ')'
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    return (G (CNot w cs ncf) wts),
{-
ascii_render_gate (CGate n w c ncf) = 
  "CGate[" ++ show n ++ "]" ++ (string_of_list "(" "," ")" "()" show (w:c))
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "CGate["
    name <- string_literal
    string "]("
    ws <- commalist int
    char ')'
    ncf <- nocontrolflag
    eof
    return (G (CGate name (head ws) (tail ws) ncf) []),
{-
ascii_render_gate (CGateInv n w c ncf) = 
  "CGate[" ++ show n ++ "]" ++ "*" ++ (string_of_list "(" "," ")" "()" show (w:c))
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "CGate["
    name <- string_literal
    string "]*("
    ws <- commalist int
    char ')'
    ncf <- nocontrolflag
    eof
    return (G (CGateInv name (head ws) (tail ws) ncf) []),
{-
ascii_render_gate (CSwap w1 w2 c ncf) = 
  "CSwap(" ++ show w1 ++ "," ++ show w2 ++ ")" 
  ++ ascii_render_controls wtm c
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "CSwap("
    w1 <- int
    char ','
    w2 <- int
    char ')'
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    return (G (CSwap w1 w2 cs ncf) wts),
{-
ascii_render_gate (QPrep w ncf) = 
  "QPrep(" ++ show w ++ ")"
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QPrep("
    w <- int
    char ')'
    ncf <- nocontrolflag
    eof
    return (G (QPrep w ncf) []),
{-
ascii_render_gate (QUnprep w ncf) = 
  "QUnprep(" ++ show w ++ ")"
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QUnprep("
    w <- int
    char ')'
    ncf <- nocontrolflag
    eof
    return (G (QUnprep w ncf) []),
{-
ascii_render_gate (QInit b w ncf) = 
  "QInit" ++ (if b then "1" else "0") ++ "(" ++ show w ++ ")"
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QInit"
    val_char <- choice [char '0',char '1']
    let val = val_char == '1'
    char '('
    w <- int
    char ')'
    ncf <- nocontrolflag
    eof
    return (G (QInit val w ncf) []),
{-
ascii_render_gate (CInit b w ncf) = 
  "CInit" ++ (if b then "1" else "0") ++ "(" ++ show w ++ ")"
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "CInit"
    val_char <- choice [char '0',char '1']
    let val = val_char == '1'
    char '('
    w <- int
    char ')'
    ncf <- nocontrolflag
    eof
    return (G (CInit val w ncf) []),
{-
ascii_render_gate (QTerm b w ncf) = 
  "QTerm" ++ (if b then "1" else "0") ++ "(" ++ show w ++ ")"
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "QTerm"
    val_char <- choice [char '0',char '1']
    let val = val_char == '1'
    char '('
    w <- int
    char ')'
    ncf <- nocontrolflag
    eof
    return (G (QTerm val w ncf) []),
{-
ascii_render_gate (CTerm b w ncf) = 
  "CTerm" ++ (if b then "1" else "0") ++ "(" ++ show w ++ ")"
  ++ ascii_render_nocontrolflag ncf
-}
    do
    string "CTerm"
    val_char <- choice [char '0',char '1']
    let val = val_char == '1'
    char '('
    w <- int
    char ')'
    ncf <- nocontrolflag
    eof
    return (G (CTerm val w ncf) []),
{-
ascii_render_gate (QMeas w) = 
  "QMeas(" ++ show w ++ ")"
-}
    do
    string "QMeas("
    w <- int
    char ')'
    eof
    return (G (QMeas w) []),
{-
ascii_render_gate (QDiscard w) = 
  "QDiscard(" ++ show w ++ ")"
-}
    do
    string "QDiscard("
    w <- int
    char ')'
    eof
    return (G (QDiscard w) []),
{-
ascii_render_gate (CDiscard w) = 
  "CDiscard(" ++ show w ++ ")"
-}
    do
    string "CDiscard("
    w <- int
    char ')'
    eof
    return (G (CDiscard w) []),
{-
ascii_render_gate (DTerm b w) = 
  "DTerm" ++ (if b then "1" else "0") ++ "(" ++ show w ++ ")"
-}
    do
    string "DTerm"
    vc <- char '0' +++ char '1'
    let b = case vc of
             '0' -> False
             '1' -> True
             _ -> error "The impossible has happend" 
    char '('
    w <- int
    char ')'
    eof
    return (G (DTerm b w) []),
{-
ascii_render_gate (Subroutine boxid inv ws1 a1 ws2 a2 c ncf scf) = 
  "Subroutine" ++ show_rep ++ "[" ++ show (string_of_boxid boxid) ++ "]"
  ++ optional inv "*"
  ++ " "
  ++ (string_of_list "(" "," ")" "()" show ws1)
  ++ (string_of_list " -> (" "," ")" "()" show ws2)
  ++ ascii_render_controls wtm c
  ++ ascii_render_nocontrolflag ncf
  where
    show_rep = if rep == RepeatFlag 1 then "" else "(x" ++ show rep ++ ")"
-}
-- The parser returns a subroutine with dummy arities, and controllable flag,
-- and repeat flag, as
-- this information is not in a subroutine line in the ASCII output. 
-- The information is added when the GatePlus is evaluated, as the first phase of
-- parsing will have collected the information. 
    do
    string "Subroutine"
    reps <- option 1 $ do
     string "(x"
     r <- int
     char ')'
     return (toInteger r)
    char '['
    boxid <- box_id
    char ']'
    inv <- inversechar
    string " ("
    ws1 <- commalist int
    string ") -> ("
    ws2 <- commalist int
    char ')'
    (cs,wts) <- option ([],[]) controls
    ncf <- nocontrolflag
    eof
    let dummy = error "attempted evaluation of a dummy value"
    return (G (Subroutine boxid inv ws1 dummy ws2 dummy cs ncf dummy (RepeatFlag reps)) wts),   
{-
ascii_render_gate (Comment s inv ws) = 
  "Comment[" ++ show s ++ "]" 
  ++ optional inv "*"
  ++ (string_of_list "(" ", " ")" "()" (\(w,s) -> show w ++ ":" ++ show s) ws)
-}
    do
    string "Comment"
    skipSpaces
    char '['
    comment <- string_literal
    char ']'
    inv <- inversechar
    ls <- labels
    eof
    return (G (Comment comment inv ls) [])
  ]

-- | The overall parsing function, reading a line of ASCII output, and
-- producing a 'GatePlus'.
parse_ascii_line :: String -> Maybe GatePlus
parse_ascii_line s =
  case readP_to_S ascii_line s of
    (h, _):_ -> Just h
    _ -> Nothing
  where
    readline = do
      skipSpaces
      l <- ascii_line
      skipSpaces
      eof
      return l      
      

