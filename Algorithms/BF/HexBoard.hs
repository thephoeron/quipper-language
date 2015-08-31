-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides the code for drawing Hex boards in graphical
-- format. See "Algorithms.BF.Main" for an overview of the boolean formula algorithm.

module Algorithms.BF.HexBoard 
(
  output_start_board,
  output_HexBoards
)
where

import Quipper

import Algorithms.BF.BooleanFormula
import Algorithms.BF.Hex

import Graphics.EasyRender
import Text.Printf

-- ----------------------------------------------------------------------
-- * Shared functions

-- | An enumeration of the colors a cell on the Hex board can be
-- colored.
data HexColor = Empty | Red | Blue deriving (Eq,Show)

-- | Convert a description of the pieces on a Hex board to a list of
-- the colors of the cells on the Hex board. Also check that the
-- hex boards are of the correct length.
hexboard_to_colorlist :: Int -> HexBoard -> [HexColor]
hexboard_to_colorlist xy_max (red,blue) = 
  if length red == xy_max && length blue == xy_max then 
    map color (zip red blue)
  else
    error "hexboard length mismatch"
  where
    color (_, True) = Blue
    color (True, _) = Red
    color (_, _) = Empty

-- ----------------------------------------------------------------------
-- * ASCII output

-- | Output multiple HexBoards in ASCII, for the given oracle.
ascii_of_HexBoards :: BooleanFormulaOracle -> [HexBoard] -> String
ascii_of_HexBoards oracle boards = ascii_of_ColorBoards x_max y_max colorBoards
  where 
    x_max = oracle_x_max oracle
    y_max = oracle_y_max oracle
    xy_max = x_max * y_max
    colorBoards = map (hexboard_to_colorlist xy_max) boards

-- | Output multiple lists of colors, that represent HexBoards, in ASCII, 
-- for the given oracle.
ascii_of_ColorBoards :: Int -> Int -> [[HexColor]] -> String
ascii_of_ColorBoards x_max y_max cbs = concat (map (ascii_of_ColorBoard 1 x_max) cbs)

-- | Output a single list of colors, that represents a HexBoard, in ASCII,
-- for the given oracle /x/ dimension.
ascii_of_ColorBoard :: Int -> Int -> [HexColor] -> String
ascii_of_ColorBoard _ _ [] = "\n"
ascii_of_ColorBoard spaces n cs = 
  show (map color_to_bash (take n cs)) ++ '\n':(replicate spaces ' ')
  ++ ascii_of_ColorBoard (spaces+1) n (drop n cs)

-- | An alternate enumeration of the colors a cell on the Hex board
-- can be colored, so we can use bash escape color codes in the ASCII
-- output.
data BashColor = BashEmpty | BashRed | BashBlue deriving Eq

-- | A function to convert HexColor to BashColor
color_to_bash :: HexColor -> BashColor
color_to_bash Empty = BashEmpty
color_to_bash Red = BashRed
color_to_bash Blue = BashBlue

-- | An instance of Show for BashColor, so the string for each color contains 
-- the bash escape code for that color, and a single character.
instance Show BashColor where
  show BashEmpty = " "
  show BashRed =   "\^[\ESC[1;31m\^]#\^[\ESC[0m\^]"
  show BashBlue =  "\^[\ESC[1;34m\^]*\^[\ESC[0m\^]"

-- ----------------------------------------------------------------------
-- * Graphical output

-- | Given an oracle, and a list of Hex board descriptions of the
-- given size, output a graphical representation of the Hex boards,
-- one per page.
document_of_HexBoards :: BooleanFormulaOracle -> [HexBoard] -> Document ()
document_of_HexBoards oracle boards = do
  sequence_ [ drawPage w h b | b <- boards ]
  where
    w = oracle_x_max oracle
    h = oracle_y_max oracle
    
-- | Draw a Hex board of dimensions /w/ × /h/ on a page by itself. 
-- The drawing takes place in the following user coordinate system:
-- 
-- \[image hex-coord.png]
drawPage :: Int -> Int -> HexBoard -> Document ()
drawPage w h board = do
  newpage (width*sc) (height*sc) $ do
    scale sc sc
    translate 0.5 (height-1)
    setlinewidth 0.05
    sequence_ [drawCell (i `mod` w) (i `div` w) color | (color, i) <- zip cboard [0..] ]
    where
      width = fromIntegral (2*w + h - 1) * sqrt 0.75 + 1
      height = 0.5 + 1.5 * fromIntegral h + 1
      cboard = hexboard_to_colorlist (w*h) board
      sc = 18  -- each cell is 1/2 inch wide
      
-- | Draw a single hex cell of the given color, at position /x/ \"over\" and /y/ \"across\".
drawCell :: Int -> Int -> HexColor -> Draw ()
drawCell x y color = draw_subroutine alt $ do
  block $ do
    translate (s*x0) y0
    moveto 0 0
    lineto s (0.5)
    lineto (2*s) 0
    lineto (2*s) (-1)
    lineto s (-1.5)
    lineto 0 (-1)
    closepath
    fillstroke (Color_RGB r g b)
  where
    x0 = fromIntegral (2*x+y)
    y0 = (-1.5) * fromIntegral y
    s = sqrt 0.75
    (r,g,b) = drawcolor color
    drawcolor Red = (1, 0, 0)
    drawcolor Blue = (0, 0, 1)
    drawcolor Empty = (1, 1, 1)
    alt = [custom_ps $ printf "%.0f %.0f %.0f %f %f hexagon\n" r g b x0 y0]

-- | A version of 'print_of_document' that is enhanced with PostScript
-- definitions local to this module.
my_print_of_document :: Format -> Document a -> IO a
my_print_of_document = print_of_document_custom cust where
  cust = custom {   
    ps_defs = "/hexagon { gsave exch s mul exch translate 0 0 moveto s .5 rlineto s -.5 rlineto 0 -1 rlineto s neg -.5 rlineto s neg .5 rlineto closepath gsave setrgbcolor fill grestore stroke grestore } bind def\n" ++
              "/s 0.75 sqrt def\n"
    }

-- ----------------------------------------------------------------------
-- * Functions taking a Format parameter

-- | Output the starting 'HexBoard' in the given format, for the given oracle.
output_start_board :: Format -> BooleanFormulaOracle -> IO ()
output_start_board f o = output_HexBoards f o [board]
  where board = start_board o

-- | Output multiple 'HexBoard's in the given format, for the given oracle.
output_HexBoards :: Format -> BooleanFormulaOracle -> [HexBoard] -> IO ()
output_HexBoards PS bfo hbs = my_print_of_document PS (document_of_HexBoards bfo hbs)
output_HexBoards PDF bfo hbs = my_print_of_document PDF (document_of_HexBoards bfo hbs) 
output_HexBoards ASCII bfo hbs = Prelude.putStr (ascii_of_HexBoards bfo hbs)
output_HexBoards Preview bfo hbs = my_print_of_document Preview (document_of_HexBoards bfo hbs)
output_HexBoards GateCount _ _ = error "GateCount is not a valid format for displaying a Hex Board"
output_HexBoards EPS bfo hbs = output_HexBoards PS bfo hbs
output_HexBoards (CustomStyle _ ) _ _ = error "CustomStyle not currently supported"

-- ----------------------------------------------------------------------
