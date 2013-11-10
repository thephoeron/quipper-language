-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module provides efficient functions for rendering vector
-- graphics to a number of formats, including EPS, PostScript, and
-- PDF. It provides an abstraction for multi-page documents, as well
-- as a set of graphics primitives for page descriptions. 
-- 
-- The graphics model is similar to that of the PostScript and PDF
-- languages, but we only implement a subset of their functionality.
-- Care has been taken that graphics rendering is done efficiently and
-- as lazily as possible; documents are rendered \"on the fly\",
-- without the need to store the whole document in memory.
-- 
-- The provided document description model consists of two separate
-- layers of abstraction:
-- 
-- * /drawing/ is concerned with placing marks on a fixed surface, and
-- takes place in the 'Draw' monad;
-- 
-- * /document structure/ is concerned with a sequence of pages, their
-- bounding boxes, and other meta-data. It takes place in the
-- 'Document' monad.

module Libraries.Render (
  -- * Types
  -- ** Coordinates
  X,
  Y,
  -- ** Color
  Color(..),
  
  -- ** Fonts
  Basefont(..),
  Font(..),
  nominalsize,
  text_width,
  
  -- ** Alignment
  Alignment,
  align_left,
  align_center,
  align_right,
  
  -- * The Document monad
  -- $DOCUMENTMODEL
  Document,
  newpage,
  newpage_defer,
  endpage,
  
  -- * The Draw monad  
  -- $DRAWINGMODEL
  Draw,
  
  -- ** Path construction commands
  -- $PATHCONSTRUCTION
  newpath,
  moveto,
  lineto,
  curveto,
  closepath,
  arc,
  arc_append,
  oval,
  rectangle,
  
  -- ** Painting commands
  stroke,
  fill,
  fillstroke,
  
  -- ** Text commands
  textbox,
  
  -- ** Graphics parameters
  -- $GRAPHICSPARAMETERS
  setlinewidth,
  setcolor,
  
  -- ** Coordinate system
  -- $COORDINATESYSTEM
  translate,
  scale,
  
  -- ** Comments
  comment,
  
  -- ** Block structure
  -- $BLOCKSTRUCTURE
  block,
  
  -- * Backends
  -- $BACKENDS
  RenderFormat(..),
  render_stdout,
  render_file,
  render_string,
  
  -- * Customization
  -- $CUSTOMIZATION
  
  -- ** Custom drawing commands
  -- $CUSTOMCOMMANDS
  draw_subroutine,
  custom_ps,  
  custom_pdf,
  custom_ascii,

  -- ** Customization interface
  Custom(..),
  custom,
  
  -- ** Customized rendering functions
  -- $CUSTOMRENDER
  render_custom_stdout,
  render_custom_file,
  render_custom_string,
  ) where

import Libraries.Auxiliary

import Codec.Compression.Zlib
import Control.Monad.State
import qualified Data.ByteString.Lazy as ByteString
import Data.Char
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import System.IO
import Text.Printf

-- ----------------------------------------------------------------------
-- * Types

-- ----------------------------------------------------------------------
-- ** Coordinates

-- | The type of /x/-coordinates.
type X = Double

-- | The type of /y/-coordinates.
type Y = Double

-- ----------------------------------------------------------------------
-- ** Colors

-- | The type of colors.
data Color =
  Color_RGB Double Double Double -- ^ Red, green and blue components,
                                 -- in the range from 0.0 (dark) to
                                 -- 1.0 (bright).
  | Color_Gray Double            -- ^ Gray value, in the range from
                                 -- 0.0 (black) to 1.0 (white).
  deriving (Show)

-- ----------------------------------------------------------------------
-- ** Fonts

-- | A enumeration type for base fonts. For the time being, we only
-- offer TimesRoman and Helvetica.
data Basefont = TimesRoman | Helvetica
  deriving (Show)

-- | A type representing font metrics for a given base font. The first
-- component is the default width of characters; the second component
-- is a map from characters to widths.
type Fontmetric = (Double, Map Char Double)

-- | Define a font metric for each base font.
metric :: Basefont -> Fontmetric
metric TimesRoman = metric_timesroman
metric Helvetica = metric_helvetica

-- | Font metrics for TimesRoman.
metric_timesroman :: Fontmetric
metric_timesroman = (0.5, m) where
  m = Map.fromList $ map (\(n,w) -> (chr n, w))
      [(32,0.25), (33,0.332031), (34,0.40625), (37,0.832031), (38,0.777344),
       (39,0.332031), (40,0.332031), (41,0.332031), (44,0.25), (45,0.332031),
       (46,0.25), (47,0.277344), (58,0.277344), (59,0.277344), (63,0.441406),
       (64,0.917969), (65,0.71875), (66,0.664062), (67,0.664062), (68,0.71875),
       (69,0.609375), (71,0.71875), (72,0.71875), (73,0.332031), (74,0.386719),
       (75,0.71875), (76,0.609375), (77,0.886719), (78,0.71875), (79,0.71875),
       (81,0.71875), (82,0.664062), (84,0.609375), (85,0.71875), (86,0.71875),
       (87,0.941406), (88,0.71875), (89,0.71875), (90,0.609375), (91,0.332031),
       (92,0.277344), (93,0.332031), (94,0.46875), (96,0.332031),
       (97,0.441406), (99,0.441406), (101,0.441406), (102,0.332031),
       (105,0.277344), (106,0.277344), (108,0.277344), (109,0.777344),
       (114,0.332031), (115,0.386719), (116,0.277344), (119,0.71875),
       (122,0.441406), (123,0.476562), (124,0.199219), (125,0.476562),
       (161,0.332031), (164,0.164062), (169,0.179688), (170,0.441406),
       (172,0.332031), (173,0.332031), (180,0.25), (182,0.449219),
       (183,0.347656), (184,0.332031), (185,0.441406), (186,0.441406),
       (188,1.0), (189,1.0), (191,0.441406), (193,0.332031), (194,0.332031),
       (195,0.332031), (196,0.332031), (197,0.332031), (198,0.332031),
       (199,0.332031), (200,0.332031), (202,0.332031), (203,0.332031),
       (205,0.332031), (206,0.332031), (207,0.332031), (208,1.0),
       (225,0.886719), (227,0.273438), (232,0.609375), (233,0.71875),
       (234,0.886719), (241,0.664062), (245,0.277344), (248,0.277344),
       (250,0.71875)]

-- | Font metrics for Helvetica.
metric_helvetica :: Fontmetric
metric_helvetica = (0.277344, m) where
  m = Map.fromList $ map (\(n,w) -> (chr n, w))
      [(34,0.351562), (35,0.554688), (36,0.554688), (37,0.886719),
      (38,0.664062), (39,0.21875), (40,0.332031), (41,0.332031), (42,0.386719),
      (43,0.582031), (45,0.332031), (48,0.554688), (49,0.554688),
      (50,0.554688), (51,0.554688), (52,0.554688), (53,0.554688),
      (54,0.554688), (55,0.554688), (56,0.554688), (57,0.554688),
      (60,0.582031), (61,0.582031), (62,0.582031), (63,0.554688), (64,1.01172),
      (65,0.664062), (66,0.664062), (67,0.71875), (68,0.71875), (69,0.664062),
      (70,0.609375), (71,0.777344), (72,0.71875), (74,0.5), (75,0.664062),
      (76,0.554688), (77,0.832031), (78,0.71875), (79,0.777344), (80,0.664062),
      (81,0.777344), (82,0.71875), (83,0.664062), (84,0.609375), (85,0.71875),
      (86,0.664062), (87,0.941406), (88,0.664062), (89,0.664062),
      (90,0.609375), (94,0.46875), (95,0.554688), (96,0.21875), (97,0.554688),
      (98,0.554688), (99,0.5), (100,0.554688), (101,0.554688), (103,0.554688),
      (104,0.554688), (105,0.21875), (106,0.21875), (107,0.5), (108,0.21875),
      (109,0.832031), (110,0.554688), (111,0.554688), (112,0.554688),
      (113,0.554688), (114,0.332031), (115,0.5), (117,0.554688), (118,0.5),
      (119,0.71875), (120,0.5), (121,0.5), (122,0.5), (123,0.332031),
      (124,0.257812), (125,0.332031), (126,0.582031), (161,0.332031),
      (162,0.554688), (163,0.554688), (164,0.164062), (165,0.554688),
      (166,0.554688), (167,0.554688), (168,0.554688), (169,0.1875),
      (170,0.332031), (171,0.554688), (172,0.332031), (173,0.332031),
      (174,0.5), (175,0.5), (177,0.554688), (178,0.554688), (179,0.554688),
      (182,0.535156), (183,0.347656), (184,0.21875), (185,0.332031),
      (186,0.332031), (187,0.554688), (188,1.0), (189,1.0), (191,0.609375),
      (193,0.332031), (194,0.332031), (195,0.332031), (196,0.332031),
      (197,0.332031), (198,0.332031), (199,0.332031), (200,0.332031),
      (202,0.332031), (203,0.332031), (205,0.332031), (206,0.332031),
      (207,0.332031), (208,1.0), (225,1.0), (227,0.367188), (232,0.554688),
      (233,0.777344), (234,1.0), (235,0.363281), (241,0.886719), (248,0.21875),
      (249,0.609375), (250,0.941406), (251,0.609375)]

-- | Look up the width of a character in the given metric.
char_metric :: Fontmetric -> Char -> Double
char_metric (d, m) c = case Map.lookup c m of
  Nothing -> d
  Just w -> w
  
-- | Look up with width of a string in the given metric.
string_metric :: Fontmetric -> String -> Double
string_metric metric s = sum [ char_metric metric c | c <- s ]

-- | A data type describing a scaled font. This consists of a base
-- font and a point size.
data Font = Font Basefont Double
  deriving (Show)

-- | Return the nominal point size of a font.
nominalsize :: Font -> Double
nominalsize (Font basefont pointsize) = pointsize

-- | Return the width of the given string in the given font.
text_width :: Font -> String -> Double
text_width (Font basefont pointsize) s = pointsize * string_metric m s
  where
    m = metric basefont

-- ----------------------------------------------------------------------
-- ** Alignment

-- | A real number representing text alignment.  0 = left aligned, 0.5
-- = centered, 1 = right aligned. Intermediate values are also
-- possible. For example, an alignment value of 0.25 means one quarter
-- of the way between left aligned and right aligned.
type Alignment = Double

-- | Left alignment.
align_left :: Alignment
align_left = 0.0

-- | Centered alignment.
align_center :: Alignment
align_center = 0.5

-- | Right alignment.
align_right :: Alignment
align_right = 1.0

-- ----------------------------------------------------------------------
-- * The Document monad
  
-- $DOCUMENTMODEL 
-- 
-- Document description takes place in the 'Document' monad. A basic
-- multi-page document has the following structure:
-- 
-- > document :: Document ()
-- > document = do
-- >   newpage x y $ do
-- >     <<<drawing commands>>>
-- >   newpage x y $ do
-- >     <<<drawing commands>>>
-- >   ...
-- 
-- Here, each 'newpage' command describes one page of the
-- document. The parameters /x/ and /y/ specify the dimensions of the
-- page bounding box. They are expressed in units of PostScript
-- points, i.e., multiples of 1/72 inch.
-- 
-- Sometimes the bounding box for a page is not known until after the
-- page content has been generated. For this purpose, we also provide
-- the following alternative to the 'newpage' command:
-- 
-- >   newpage_defer $ do
-- >     <<<drawing commands>>>
-- >     endpage x y
-- 
-- It works just like the 'newpage' command, except that the bounding
-- box is given at the end.

-- | The Document monad.
data Document a =
  Document_Return a                       -- ^ Terminate with a result.
  | Document_Page X Y (Draw (Document a)) -- ^ Page with bounding box
                                          -- known at the beginning.
  | Document_Page_defer (Draw (X, Y, Document a)) 
                                          -- ^ Page with bounding box
                                          -- known at the end.

instance Monad Document where
  return a = Document_Return a
  f >>= g = case f of
    Document_Return a -> g a
    Document_Page x y draw -> Document_Page x y draw' where
      draw' = do
        f' <- draw
        return (f' >>= g)
    Document_Page_defer draw -> Document_Page_defer draw' where
      draw' = do
        (x, y, f') <- draw
        return (x, y, f' >>= g)
                     
-- ----------------------------------------------------------------------
-- ** A vacuous run function
        
-- | Skip document without rendering.        
document_skip :: Document a -> a
document_skip (Document_Return a) = a
document_skip (Document_Page x y draw) = document_skip a where
  a = draw_skip draw
document_skip (Document_Page_defer draw) = document_skip a where
  (x, y, a) = draw_skip draw

-- ----------------------------------------------------------------------
-- ** User-level document structuring commands

-- | Create a page of the given bounding box, containing the given
-- drawing.
newpage :: X -> Y -> Draw a -> Document a
newpage x y draw =
  Document_Page x y draw' where
    draw' = do
      a <- draw
      return (Document_Return a)
            
-- | Create a page containing the given drawing, with the bounding box
-- computed at the end of the drawing routines.
newpage_defer :: Draw (X, Y, a) -> Document a
newpage_defer draw =
  Document_Page_defer draw' where
    draw' = do
      (x, y, a) <- draw
      return (x, y, Document_Return a)

-- | End the page with the given bounding box.
endpage :: X -> Y -> Draw (X, Y, ())
endpage x y = do
  return (x, y, ())

-- ----------------------------------------------------------------------
-- * The Draw monad

-- $DRAWINGMODEL 
-- 
-- The description of the visible content of a page take place in the
-- 'Draw' monad. It takes the form of a sequence of drawing commands,
-- for example:
-- 
-- >     moveto 10 10
-- >     lineto 10 100
-- >     lineto 100 100
-- >     lineto 100 10
-- >     closepath
-- >     stroke
-- 
-- The graphics model is similar to that of the PostScript and PDF
-- languages. The basic concept is that of a /path/, which is a
-- sequence of straight and curved line segments. Paths are first
-- constructed using /path construction commands/, and then painted
-- using /painting commands/, depending on a set of current 
-- /graphics parameters/ and a current /coordinate system/.
-- 
-- We also provide block structure. Changes to the graphics state
-- (color, coordinate system, etc.) that are done within a block are
-- local to the block.
-- 
-- >     block $ do
-- >       <<drawing commands>>
  
-- ----------------------------------------------------------------------
-- ** Internal definition of the Draw monad

-- | An abstract data type describing individual drawing commands.
data DrawCommand =
  Newpath        -- ^ Set the current path to empty.
  | Moveto X Y   -- ^ Start a new subpath at the given coordinates.
  | Lineto X Y   -- ^ Append a straight line to the current subpath.
  | Curveto X Y X Y X Y -- ^ Append a Bezier curve segment.
  | Closepath    -- ^ Close the current subpath.
  | Stroke       -- ^ Stroke and clear the current path.
  | Fill Color   -- ^ Fill and clear the current path.
  | FillStroke Color -- ^ Fill and stroke and clear the current path.
  | TextBox Alignment Font Color X Y X Y Double String -- ^ Text.
  | SetLineWidth Double  -- ^ Set current line width.
  | SetColor Color -- ^ Set current color.
  | Translate X Y  -- ^ Translate current coordinate system.
  | Scale X Y      -- ^ Scale the current coordinate system.
  | Rotate Double  -- ^ Rotate the current coordinate system.
  | Comment String -- ^ A human-readable comment, not rendered
  | Subroutine (Draw ()) [CustomDef]
                 -- ^ A subroutine is a composite drawing command. In
                 -- addition to a default definition that works for
                 -- any backend, it can also have optional specialized
                 -- definitions for particular backends.
  deriving (Show)

-- $ In understanding how the 'Draw' monad works, it is useful to keep
-- in mind that there is an isomorphism
-- 
-- @Draw /a/@ ≅ @Draw ()@ ×. /a/,
-- 
-- where \"×.\" is left-strict product, i.e., if the left-hand-side is
-- undefined, then so is the entire expression.

-- | The Draw monad.
data Draw a = 
  Draw_Return a                     -- ^ Terminate with a result.
  | Draw_Write DrawCommand (Draw a) -- ^ Write a command and continue.
  | Draw_Block (Draw (Draw a))      -- ^ Block structure. Perform the
                                    -- commands of the outer 'Draw' in
                                    -- a temporary copy of the
                                    -- graphics state, then continue
                                    -- with the inner 'Draw' in the
                                    -- original graphics state.
    deriving (Show)
    
instance Monad Draw where
  return a = Draw_Return a
  f >>= g = case f of
    Draw_Return a -> g a
    Draw_Write cmd f' -> Draw_Write cmd (f' >>= g)
    Draw_Block draw -> Draw_Block draw' where
      draw' = do
        f' <- draw
        return (f' >>= g)

-- ----------------------------------------------------------------------
-- ** Low-level operations for the Draw monad

-- | Write the given command to the 'Draw' monad.
draw_write :: DrawCommand -> Draw ()
draw_write cmd = 
  Draw_Write cmd (Draw_Return ())  

-- | Create a new subroutine.
draw_subroutine :: [CustomDef] -> Draw () -> Draw ()
draw_subroutine alt draw =
  draw_write (Subroutine draw alt)

-- | Write a block to the 'Draw' monad.
draw_block :: Draw a -> Draw a
draw_block draw = 
  Draw_Block draw' where
    draw' = do
      a <- draw
      return (Draw_Return a)
      
-- ----------------------------------------------------------------------
-- ** A vacuous run function

-- | Skip draw actions without rendering.
draw_skip :: Draw a -> a
draw_skip (Draw_Return x) = x
draw_skip (Draw_Write cmd cont) = draw_skip cont
draw_skip (Draw_Block f) = draw_skip (draw_skip f)

-- ----------------------------------------------------------------------
-- ** User-level drawing commands

-- ----------------------------------------------------------------------
-- *** Path construction commands

-- $PATHCONSTRUCTION
--   
-- During path construction, there is a notion of /current path/ and
-- /current point/. A path may consist of zero or more connected
-- subpaths, and each subpath is either open or closed. 

-- | Set the current path to empty.
newpath :: Draw ()
newpath = draw_write (Newpath)

-- | Start a new subpath at (/x/,/y/). The point (/x/,/y/) becomes the
-- current point.
moveto :: X -> Y -> Draw ()
moveto x y = draw_write (Moveto x y)

-- | Extend the current subpath by a straight line segment from the
-- current point to (/x/,/y/). The point (/x/,/y/) becomes the current
-- point.
lineto :: X -> Y -> Draw ()
lineto x y = draw_write (Lineto x y)

-- | @'curveto' /x1/ /y1/ /x2/ /y2/ /x/ /y/@: Extend the current
-- subpath by a Bezier curve segment from the current point to
-- (/x/,/y/), with control points (/x1/,/y1/) and (/x2/,/y2/). The
-- point (/x/,/y/) becomes the current point.
curveto :: X -> Y -> X -> Y -> X -> Y -> Draw ()
curveto x1 y1 x2 y2 x y = draw_write (Curveto x1 y1 x2 y2 x y)

-- | Close the current subpath. If necessary, connect the subpath's
-- final and initial points by a straight line segment. Note that a
-- closed path is rendered differently than a non-closed path whose
-- initial and final points coincide, because in the latter case, the
-- endpoints are capped rather than mitered.
closepath :: Draw ()
closepath = draw_write (Closepath)

-- ----------------------------------------------------------------------
-- *** Painting commands

-- | Stroke the current path, using the current line color, line
-- width, and other graphics parameters. This operation implicitly
-- resets the current path to empty.
stroke :: Draw ()
stroke = draw_write (Stroke)

-- | Fill the current path, using the given color. This operation
-- implicitly resets the current path to empty. 
fill :: Color -> Draw ()
fill color = draw_write (Fill color)

-- | Fill the current path, using the given color; also stroke the
-- path using the current line color. This operation implicitly resets
-- the current path to empty.
fillstroke :: Color -> Draw ()
fillstroke color = draw_write (FillStroke color)

-- ----------------------------------------------------------------------
-- *** Text

-- | @'textbox' /a/ /f/ /c/ /x0/ /y0/ /x1/ /y1/ /b/ /s/@: Write the
-- given string on an imaginary line from point (/x0/,/y0/) to
-- (/x1/,/y1/), using font /f/ and color /c/. If the text is too wide
-- to fit on the line, it is scaled down. Otherwise, it is aligned
-- according to the alignment parameter /a/. The parameter /b/
-- specifies an additional offset by which to lower the text, with
-- respect to the text's nominal size. For example, if /b/=0, then the
-- above-mentioned imaginary line from (/x0/,/y0/) to (/x1/,/y1/)
-- coincides with the text's usual baseline. If /b/=0.5, then this
-- line approximately goes through the center of each character.
-- 
-- \[image textbox.png]
textbox :: Alignment -> Font -> Color -> X -> Y -> X -> Y -> Double -> String -> Draw ()
textbox a f c x0 y0 x1 y1 b s = draw_write (TextBox a f c x0 y0 x1 y1 b s)

-- ----------------------------------------------------------------------
-- *** Graphics parameters

-- $GRAPHICSPARAMETERS
-- 
-- The painting commands rely on a set of graphics parameters. The
-- graphics parameters are initially set to default values, and can be
-- altered with the following commands.

-- | Set the line width. The initial line width is 1.
setlinewidth :: Double -> Draw ()
setlinewidth x = draw_write (SetLineWidth x)

-- | Set the current color for stroking. The initial stroke color is
-- black.
setcolor :: Color -> Draw ()
setcolor color = draw_write (SetColor color)

-- ----------------------------------------------------------------------
-- *** Coordinate system

-- $COORDINATESYSTEM
-- 
-- Coordinates, lengths, widths, etc, are all interpreted relative to
-- a /current coordinate system/. The initial coordinate system of
-- each page has the origin in the lower left corner, with each unit
-- equaling one PostScript point (1/72 inch). The following commands
-- can be used to change the current coordinate system.

-- | Translate the current coordinate system by (/x/,/y/).
translate :: X -> Y -> Draw ()
translate x y = draw_write (Translate x y)

-- | Scale the current coordinate system by (/s/,/t/). Here, /s/ is
-- the scaling factor in the /x/-direction, and /t/ is the scaling
-- factor in the /y/-direction.
scale :: X -> Y -> Draw ()
scale x y = draw_write (Scale x y)

-- | Rotate the current coordinate system by /angle/, measured
-- counterclockwise in degrees.
rotate :: Double -> Draw ()
rotate angle = draw_write (Rotate angle)

-- ----------------------------------------------------------------------
-- *** Comments

-- | Insert a human-readable comment in the content stream. This is
-- for information only, and is not rendered in the graphical output.
comment :: String -> Draw ()
comment s = draw_write (Comment s)

-- ----------------------------------------------------------------------
-- *** Block structure

-- $BLOCKSTRUCTURE 
-- 
-- Drawing operations can be grouped into blocks with the 'block'
-- operator. Changes to the graphics parameters and coordinate system
-- are local to the block. It is undefined whether changes to the
-- current path made within a block persist after the end of the block
-- (they do in PDF, but not in PostScript). Therefore, path
-- construction should not be broken up across end-of-block boundaries.

-- | Perform a block of commands in a local copy of the graphics
-- state. This is intended to be used like this:
-- 
-- >     block $ do
-- >       <<drawing commands>>
block :: Draw a -> Draw a
block = draw_block

-- ----------------------------------------------------------------------
-- *** Derived commands

-- $ PDF has no built-in command for drawing circular arcs, so we
-- define it here. Since PostScript does have such a command, we use
-- the 'draw_subroutine' mechanism.

-- | Start a new subpath consisting of a circular arc segment. The
-- arc segment is centered at (/x/,/y/), has radius /r/, and extends
-- from angle /a1/ to angle /a2/, measured in degrees,
-- counterclockwise from the /x/-axis. The arc is drawn clockwise if
-- /a2/ ≥ /a1/, and counterclockwise otherwise. The final point
-- becomes the new current point.
arc :: X -> Y -> Double -> Double -> Double -> Draw ()
arc x y r a1 a2 = draw_subroutine alt $ do
  arc_internal False x y r r a1 a2
    where
      alt = [custom_ps $ printf "%f %f moveto\n" x0 y0 ++ printf "%f %f %f %f %f %s\n" x y r a1 a2 (if a1 <= a2 then "arc" else "arcn"),
             custom_ascii $ printf "Arc %f %f %f %f %f\n" x y r a1 a2]
      x0 = x + r * cos (pi/180 * a1)
      y0 = y + r * sin (pi/180 * a1)

-- | Like 'arc', except append to the current subpath. If necessary,
-- add a straight line segment from the current point to the starting
-- point of the arc.
arc_append :: X -> Y -> Double -> Double -> Double -> Draw ()
arc_append x y r a1 a2 = draw_subroutine alt $ do
  arc_internal True x y r r a1 a2
    where
      alt = [custom_ps $ printf "%f %f %f %f %f %s\n" x y r a1 a2 (if a1 <= a2 then "arc" else "arcn"),
             custom_ascii $ printf "Arc_append %f %f %f %f %f\n" x y r a1 a2]

-- | Append a new closed subpath consisting of an oval centered at
-- (/x/,/y/), with horizontal and vertical radii /rx/ and /ry/,
-- respectively.
oval :: X -> Y -> X -> Y -> Draw ()
oval x y rx ry = do
  arc_internal False x y rx ry 0 360
  closepath

-- | The common implementation of 'arc', 'arc_append', and 'oval'. The
-- first parameter is a boolean flag indicating whether to append to
-- an existing subpath or start a new subpath. The fourth and fifth
-- parameter are the horizontal and vertical radius.
arc_internal :: Bool -> X -> Y -> Double -> Double -> Double -> Double -> Draw ()
arc_internal connect x y rx ry a1 a2 = do
  if connect then lineto x0 y0 else moveto x0 y0
  -- We divide the arc into n segments of 90 degrees or less.
  sequence_ [ aux a | i <- [0..n-1], let a = a1 + (fromIntegral i)*phi ]
  where
    (x0, y0) = point rx ry a1
    n = int_ceiling (abs(a2 - a1) / 90)
    phi = if n > 0 then (a2 - a1) / (fromIntegral n) else 0
    alpha = 4/3 * c / (1+c)
    c = cos' (phi/2)
    point rx ry a = (x + rx * cos' a, y + ry * sin' a)
    cos' x = cos (pi/180 * x)
    sin' x = sin (pi/180 * x)
    along (x0,y0) (x1,y1) alpha = (x0 + alpha * (x1-x0), y0 + alpha * (y1-y0))
    aux a = curveto x1 y1 x2 y2 x3 y3
      where
        (x0, y0) = point rx ry a
        (x3, y3) = point rx ry (a + phi)
        (xp, yp) = point (rx/c) (ry/c) (a + phi/2)
        (x1, y1) = along (x0, y0) (xp, yp) alpha
        (x2, y2) = along (x3, y3) (xp, yp) alpha

-- | @'rectangle' /x/ /y/ /w/ /h/@: Draw a rectangle of width /w/ and
-- height /h/, starting from (/x/,/y/). If /w/ and /h/ are positive,
-- then (/x/,/y/) is the lower left corner.
rectangle :: X -> Y -> X -> Y -> Draw ()
rectangle x y w h = draw_subroutine alt def where
  def = do
    moveto x y
    lineto x (y+h)
    lineto (x+w) (y+h)
    lineto (x+w) y
    closepath
  alt = [
    custom_pdf $ printf "%f %f %f %f re\n" x y w h,
    custom_ascii $ printf "Rectangle %f %f %f %f\n" x y w h
    ]

-- ----------------------------------------------------------------------
-- * Customization

-- $CUSTOMIZATION
-- 
-- The document and drawing abstractions provided by this module are
-- purposely kept general-purpose, and do not include
-- application-specific features. However, we provide a mechanism by
-- which applications can provide customized drawing commands and
-- other custom features.

-- ** Custom drawing commands

-- $CUSTOMCOMMANDS
-- 
-- It is sometimes useful to use customized drawing commands. For
-- example, an application that draws many rectangles might like to
-- define a custom 'rectangle' function for appending a rectangle to
-- the current path. Of course this can be defined as an ordinary
-- Haskell function, using elementary drawing commands:
-- 
-- > my_rect :: X -> Y -> X -> Y -> Draw ()
-- > my_rect x0 y0 x1 y1 = do
-- >   moveto x0 y0
-- >   lineto x0 y1
-- >   lineto x1 y1
-- >   lineto x1 y0
-- >   closepath
-- 
-- However, sometimes it is nice to make use of specialized abilities
-- of individual backends. For example, PDF already has a built-in
-- rectangle drawing command, and PostScript has the ability to define
-- custom subroutines within the document text. Using these features
-- can decrease the size of the generated documents. 
-- 
-- We therefore provide a facility for defining new drawing commands
-- with backend-specific implementations. For example, a more general
-- version of the above 'my_rect' function can be defined as
-- follows:
-- 
-- > my_rect :: X -> Y -> X -> Y -> Draw ()
-- > my_rect x0 y0 x1 y1 = draw_subroutine alt $ do
-- >   moveto x0 y0
-- >   lineto x0 y1
-- >   lineto x1 y1
-- >   lineto x1 y0
-- >   closepath
-- >  where
-- >   alt = [
-- >     custom_ps $      printf "%f %f %f %f rect\n" x0 y0 x1 y1,
-- >     custom_pdf $     printf "%f %f %f %f re\n" x0 y0 (x1-x0) (y1-y0),
-- >     custom_ascii $   printf "My_rect %f %f %f %f\n" x0 y0 x1 y1
-- >     ]
-- 
-- The idea is to provide a default definition in terms of primitive
-- drawing commands, as well as a list of various backend specific
-- definitions. In the case of PostScript subroutines, the PostScript
-- file must then also be supplied with a definition for the /rect/
-- subroutine, which can be done with the command 'render_ps_custom':
-- 
-- > my_ps_defs = "/rect { ... } bind def\n"
-- >
-- > my_render_ps = render_ps_custom custom { ps_defs = my_ps_defs }
-- 
-- Note that the 'draw_subroutine' customization mechanism is entirely
-- optional. Its purpose is to generate shorter output for some
-- backends; if it is omitted, the file may be be longer but should
-- look the same.

-- | An enumeration of backend languages, for the purpose of defining
-- custom drawing commands. Note that several backends (e.g. EPS and
-- PostScript) may share the same language, and therefore they are
-- only represented once in this enumeration.
data Language =
  Language_PS      -- ^ PostScript (including EPS)
  | Language_PDF   -- ^ PDF
  | Language_ASCII -- ^ ASCII (for debugging)
  deriving (Show, Eq, Ord)

-- | The type of custom definitions, to be used with the
-- 'draw_subroutine' command.
data CustomDef = CustomDef Language String
  deriving (Show)

-- | Define a custom PostScript definition.
custom_ps :: String -> CustomDef
custom_ps s = CustomDef Language_PS s

-- | Define a custom PDF definition.
custom_pdf :: String -> CustomDef
custom_pdf s = CustomDef Language_PDF s

-- | Define a custom ASCII definition.
custom_ascii :: String -> CustomDef
custom_ascii s = CustomDef Language_ASCII s

-- | Look up an element in a list of 'CustomDef's.
custom_lookup :: Language -> [CustomDef] -> Maybe String
custom_lookup lang defs = 
  case find (\(CustomDef l _) -> l==lang) defs of
    Nothing -> Nothing
    Just (CustomDef l s) -> Just s

-- ----------------------------------------------------------------------
-- ** Customization interface

-- | A data structure that holds application-specific meta-data and
-- customization information.
data Custom = Custom { 
  creator :: String, -- ^ Name of the software that created the file.
                     -- Example: \"MyApp 1.0\". Note: this is intended
                     -- to hold the name of the software, not the
                     -- human user, that created the document.
  ps_defs :: String  -- ^ Definitions to go in the PostScript
                     -- preamble.
  }
              
-- | An empty customization structure. Customizations should be
-- specified by modifying 'custom', for example:
-- 
-- > custom { creator = "MyApp 1.0" }
custom :: Custom
custom = Custom {
  creator = "",
  ps_defs = ""
  }

-- ----------------------------------------------------------------------
-- * Generic string output

-- ----------------------------------------------------------------------
-- ** The WriterMonad class

-- | A 'WriterMonad' is any monad that one can output strings to.
-- 
-- Minimal complete definition: 'wPutChar' or 'wPutStr'.
class Monad m => WriterMonad m where
  -- | Write a character.
  wPutChar :: Char -> m ()
  wPutChar c = wPutStr [c]
  
  -- | Write a string.
  wPutStr :: String -> m ()
  wPutStr s = sequence_ [ wPutChar c | c <- s ]
  
-- | Like 'wPutStr', but adds a newline character.
wPutStrLn :: (WriterMonad m) => String -> m ()
wPutStrLn s = do
  wPutStr s
  wPutChar '\n'
  
-- | Write a value of any printable type, and add a newline.
wprint :: (WriterMonad m, Show a) => a -> m ()
wprint x = wPutStrLn (show x)
    
instance WriterMonad IO where
  wPutChar = putChar
  wPutStr = putStr

-- ----------------------------------------------------------------------
-- ** The Writer monad

-- | A generic 'WriterMonad'.
data Writer a =
  Writer_Return a                    -- ^ Terminate with a result.
  | Writer_PutChar Char (Writer a)   -- ^ Write a character.
  | Writer_PutStr String (Writer a)  -- ^ Write a string.

instance Monad Writer where
  return a = Writer_Return a
  f >>= g = case f of
    Writer_Return a -> g a
    Writer_PutChar c f' -> Writer_PutChar c (f' >>= g)
    Writer_PutStr s f' -> Writer_PutStr s (f' >>= g) 
    
instance WriterMonad Writer where
  wPutChar c = Writer_PutChar c (Writer_Return ())
  wPutStr s = Writer_PutStr s (Writer_Return ())
  
-- ----------------------------------------------------------------------
-- ** Isomorphism with (String, a)
  
-- | Isomorphically map a 'Writer' computation to a pair of a string
-- and a value.
-- 
-- Important usage note: the 'String' in the output is produced
-- lazily, and before /a/ is produced. To preserve laziness, do not
-- evaluate /a/ before the end of 'String' has been reached.
writer_to_pair :: Writer a -> (String, a)
writer_to_pair (Writer_Return a) = ("", a)
writer_to_pair (Writer_PutChar c cont) = (c:t, a) where
  (t, a) = writer_to_pair cont
writer_to_pair (Writer_PutStr s cont) = (s ++ t, a) where
  (t, a) = writer_to_pair cont

-- | The inverse of 'writer_to_pair'.
pair_to_writer :: (String, a) -> Writer a
pair_to_writer (s, a) = do
  wPutStr s
  return a

-- ----------------------------------------------------------------------
-- ** Run functions

-- | Run a 'Writer' computation in any 'WriterMonad'.
run_writer :: (WriterMonad m) => Writer a -> m a
run_writer (Writer_Return a) = return a
run_writer (Writer_PutChar c cont) = do
  wPutChar c
  run_writer cont
run_writer (Writer_PutStr s cont) = do
  wPutStr s
  run_writer cont

-- | Run a writer in the 'IO' monad by printing to a file.
writer_to_file :: Handle -> Writer a -> IO a
writer_to_file h (Writer_Return a) = return a
writer_to_file h (Writer_PutChar c cont) = do
  hPutChar h c
  writer_to_file h cont
writer_to_file h (Writer_PutStr s cont) = do
  hPutStr h s
  writer_to_file h cont

-- | Run a writer by printing to a string.
writer_to_string :: Writer a -> String
writer_to_string = fst . writer_to_pair

-- ----------------------------------------------------------------------
-- ** Boxed monads

-- | Create an identical \"boxed\" copy of a type constructor. This is
-- used for technical reasons, to allow the 'wprintf' operation to be
-- typed.
newtype Boxed m a = Boxed (m a)

-- | Unbox a boxed item.
unbox :: Boxed m a -> m a
unbox (Boxed x) = x

instance Monad m => Monad (Boxed m) where
  return a = Boxed (return a)
  f >>= g = Boxed (unbox f >>= (unbox . g))

instance WriterMonad m => WriterMonad (Boxed m) where
  wPutChar c = Boxed (wPutChar c)
  wPutStr c = Boxed (wPutStr c)

instance MonadState s m => MonadState s (Boxed m) where
  get = Boxed get
  put s = Boxed (put s)

-- ----------------------------------------------------------------------
-- ** Currying in a boxed monad
  
-- | A class to curry/uncurry functions in any boxed monad. This
-- establishes an isomorphism
-- 
-- > @fun  ≅  args -> Boxed m res,@
-- 
-- where
-- 
-- > fun = a1 -> a2 -> ... -> an -> Boxed m res,
-- > args = (a1, (a2, (..., (an, ())))).
class Boxed_Curry fun args m res | fun -> args res m, args res m -> fun where
  boxed_curry :: (args -> Boxed m res) -> fun
  boxed_uncurry :: fun -> (args -> Boxed m res)

instance Boxed_Curry (Boxed m a) () m a where
  boxed_curry g = g ()
  boxed_uncurry x = const x
  
instance Boxed_Curry fun args m res => Boxed_Curry (a -> fun) (a, args) m res where
  boxed_curry g x = boxed_curry (\xs -> g (x,xs))
  boxed_uncurry f (x,xs) = boxed_uncurry (f x) xs

-- ----------------------------------------------------------------------  
-- ** Formatted printing
  
-- | Print a formatted value in the context of a boxed WriterMonad. Usage:
-- 
-- wprintf "%f %f" x y :: Boxed Writer
wprintf :: (Boxed_Curry fun args m (), WriterMonad m, Curry fun' args String, PrintfType fun') => String -> fun
wprintf fmt = g where
  g = boxed_curry g'
  g' args = wPutStr (f' args)
  f' = muncurry f
  f = printf fmt

-- | In any 'WriterMonad', introduce a block in which 'wprintf' can be
-- used. This has no computational overhead, i.e., is compiled to the
-- identity operation; it exists only to please the type system,
-- due to the fancy typing of 'wprintf'.
with_printf :: (WriterMonad m) => Boxed m a -> m a
with_printf = unbox

-- ----------------------------------------------------------------------
-- ** Filters

-- $ A filter is any function from strings to strings, but it should
-- usually be lazy. Typical examples are compression, encryption,
-- ASCII armoring, character encoding, and their inverses.
-- 
-- We provide a convenient operator for temporarily wrapping a filter
-- around the 'Writer' monad, as well as specific filters.

-- | Wrap a filter around a 'Writer' computation. This introduces a
-- local block within the 'Writer' monad; all text written within the
-- block is encoded through the given filter. Filters can be composed
-- and nested.
with_filter :: (WriterMonad m) => (String -> String) -> Writer a -> m a
with_filter encoding = run_writer . pair_to_writer . (\(x,y) -> (encoding x, y)) . writer_to_pair

-- | A filter for performing \"flate\" (also known as \"zlib\")
-- compression. 
-- 
-- Note: both the input and output strings are regarded as sequences
-- of bytes, not characters. Any characters outside the byte range are
-- truncated to 8 bits.
flate_filter :: String -> String
flate_filter = map chr . map fromIntegral . ByteString.unpack . compress . ByteString.pack . map fromIntegral . map ord

-- ----------------------------------------------------------------------
-- * Backends

-- ----------------------------------------------------------------------
-- ** Auxiliary functions

-- | Ensure that the last line of the string ends in a newline
-- character, adding one if necessary. An empty string is considered to contain zero lines, so no newline character needs to be added. 
ensure_nl :: String -> String
ensure_nl "" = ""
ensure_nl s = 
  if last s == '\n' then s else s++"\n"

-- ----------------------------------------------------------------------
-- * ASCII output

-- | Render draw actions as ASCII.
draw_to_ascii :: Draw a -> Writer a
draw_to_ascii (Draw_Return x) = return x
draw_to_ascii (Draw_Write cmd cont) = do
  command_to_ascii cmd
  draw_to_ascii cont
draw_to_ascii (Draw_Block f) = do
  wPutStrLn "begin"
  cont <- draw_to_ascii f
  wPutStrLn "end"
  draw_to_ascii cont
  
-- | Render drawing commands as ASCII.
command_to_ascii :: DrawCommand -> Writer ()
command_to_ascii (Subroutine draw alt) =
  case custom_lookup Language_ASCII alt of
    Just out -> wPutStr (ensure_nl out)
    Nothing -> draw_to_ascii draw
command_to_ascii cmd =
  wprint cmd

-- | Render a document as ASCII.
document_to_ascii :: Document a -> Writer a
document_to_ascii (Document_Return x) = return x
document_to_ascii (Document_Page x y draw) = do
  wPutStrLn $ "startpage " ++ show x ++ " " ++ show y
  cont <- draw_to_ascii draw
  wPutStrLn "endpage"
  document_to_ascii cont
document_to_ascii (Document_Page_defer draw) = do
  wPutStrLn "startpage (atend)"
  (x, y, cont) <- draw_to_ascii draw
  wPutStrLn $ "endpage " ++ show x ++ " " ++ show y
  document_to_ascii cont
  
-- | Render a document as ASCII. This is for debugging purposes only.
-- The output is a sequence of drawing commands, rather than a
-- graphical representation.
render_ascii :: Document a -> Writer a
render_ascii = document_to_ascii

-- ----------------------------------------------------------------------
-- * PostScript output
  
-- ----------------------------------------------------------------------
-- ** Auxiliary functions

-- | Escape special characters in a string literal.
ps_escape :: String -> String
ps_escape [] = []
ps_escape ('\\' : t) = '\\' : '\\' : ps_escape t
ps_escape ('('  : t) = '\\' : '('  : ps_escape t
ps_escape (')'  : t) = '\\' : ')'  : ps_escape t
ps_escape (h : t)    = h : ps_escape t

-- | Remove newline characters in a string.
remove_nl :: String -> String
remove_nl = map f where
  f '\n' = ' '
  f '\r' = ' '
  f x = x

-- ----------------------------------------------------------------------
-- ** The PSWriter monad

-- $ For convenience, we wrap the 'Writer' monad in a custom state monad;
-- the latter keeps track of the current document bounding box (i.e.,
-- the smallest bounding box containing all pages) and the current
-- number of pages.

-- | The type of page numbers.
type Page = Integer

-- | A state to keep track of a current bounding box and page number.
data PS_State = PS_State !X !Y !Page

-- | The initial 'PS_State'.
ps_state_empty :: PS_State
ps_state_empty = PS_State 0 0 0 

-- | The 'PSWriter' monad. This is just a 'PS_State' wrapped around
-- the 'Writer' monad.
type PSWriter = Boxed (StateT PS_State Writer)

instance WriterMonad (StateT PS_State Writer) where
  wPutChar c = lift (wPutChar c)
  wPutStr s = lift (wPutStr s)

-- | Run function for the 'PSWriter' monad.
pswriter_run :: PSWriter a -> Writer a
pswriter_run f = evalStateT (unbox f) ps_state_empty

-- ----------------------------------------------------------------------
-- *** Access functions for the PSWriter monad

-- | Get the bounding box.
ps_get_bbox :: PSWriter (X, Y)
ps_get_bbox = do
  PS_State x y _ <- get
  return (x, y)
  
-- | Add to the bounding box.
ps_add_bbox :: X -> Y -> PSWriter ()
ps_add_bbox x y = do
  PS_State x' y' p <- get
  put (PS_State (x `max` x') (y `max` y') p)

-- | Get the page count.
ps_get_pagecount :: PSWriter Page
ps_get_pagecount = do
  PS_State _ _ p <- get
  return p
  
-- | Return the next page number.
ps_next_page :: PSWriter Page
ps_next_page = do
  PS_State x y p <- get
  put (PS_State x y (p+1))
  return (p+1)

-- ----------------------------------------------------------------------
-- ** Internal rendering to the PSWriter monad

-- | Render draw actions as PostScript.
draw_to_ps :: Draw a -> PSWriter a
draw_to_ps (Draw_Return x) = return x
draw_to_ps (Draw_Write cmd cont) = do
  command_to_ps cmd
  draw_to_ps cont
draw_to_ps (Draw_Block body) = do
  wPutStrLn "gsave"
  cont <- draw_to_ps body
  wPutStrLn "grestore"
  draw_to_ps cont
  
-- | Set the color.
color_to_ps :: Color -> PSWriter ()
color_to_ps (Color_RGB r g b) = do
  wprintf "%f %f %f setrgbcolor\n" r g b
color_to_ps (Color_Gray v) = do
  wprintf "%f setgray\n" v

-- | Set the font.
font_to_ps :: Font -> PSWriter ()
font_to_ps (Font TimesRoman pt) = do
  wprintf "/Times-Roman findfont %f scalefont setfont\n" pt
font_to_ps (Font Helvetica pt) = do
  wprintf "/Helvetica findfont %f scalefont setfont\n" pt

-- | Draw a single drawing command to PostScript.
command_to_ps :: DrawCommand -> PSWriter ()
command_to_ps (Newpath) = do
  wPutStrLn "newpath"
command_to_ps (Moveto x y) = do
  wprintf "%f %f moveto\n" x y
command_to_ps (Lineto x y) = do
  wprintf "%f %f lineto\n" x y
command_to_ps (Curveto x1 y1 x2 y2 x y) = do
  wprintf "%f %f %f %f %f %f curveto\n" x1 y1 x2 y2 x y
command_to_ps (Closepath) = do
  wPutStrLn "closepath"
command_to_ps (Stroke) = do
  wPutStrLn "stroke"
command_to_ps (Fill color) = do
  wPutStrLn "gsave" 
  color_to_ps color
  wPutStrLn "fill" 
  wPutStrLn "grestore"
  wPutStrLn "newpath"
command_to_ps (FillStroke color) = do
  wPutStrLn "gsave"
  color_to_ps color
  wPutStrLn "fill"
  wPutStrLn "grestore"
  wPutStrLn "stroke"
command_to_ps (TextBox align font color x0 y0 x1 y1 b s) = do
  wPutStrLn "gsave"
  font_to_ps font
  color_to_ps color
  wprintf "(%s) %f %f %f %f %f %f textbox\n" (ps_escape s) x0 y0 x1 y1 align yshift
  wPutStrLn "grestore"
  where
    yshift = -b * nominalsize font
command_to_ps (SetLineWidth x) = do
  wprintf "%f setlinewidth\n" x
command_to_ps (SetColor color) = do
  color_to_ps color
command_to_ps (Translate x y) = do
  wprintf "%f %f translate\n" x y
command_to_ps (Scale x y) = do
  wprintf "%f %f scale\n" x y
command_to_ps (Rotate angle) = do
  wprintf "%f rotate\n" angle
command_to_ps (Comment s) = do
  wprintf "%% %s\n" (remove_nl s)
command_to_ps (Subroutine draw alt) = 
  case custom_lookup Language_PS alt of
    Just out -> wprintf "%s" (ensure_nl out)
    Nothing -> draw_to_ps draw

-- | Render a document as PostScript.
document_to_ps :: Custom -> Document a -> PSWriter a
document_to_ps custom document = do
  -- global header
  wPutStrLn "%!PS-Adobe-3.0"
  wPutStrLn "%%LanguageLevel: 2"
  when (creator custom /= "") $ do
    wprintf "%%%%Creator: %s\n" (creator custom)
  wPutStrLn "%%BoundingBox: (atend)"
  wPutStrLn "%%HiResBoundingBox: (atend)"
  wPutStrLn "%%Pages: (atend)"
  wPutStrLn "%%EndComments"
  wPutStrLn "%%BeginSetup"
  wprintf "%s" global_ps_defs
  when (ps_defs custom /= "") $ do
    wprintf "%s" (ensure_nl $ ps_defs custom)
  wPutStrLn "%%EndSetup"
  a <- pages_to_ps document
  (x, y) <- ps_get_bbox
  pagecount <- ps_get_pagecount
  wPutStrLn "%%Trailer"
  wprintf "%%%%BoundingBox: 0 0 %d %d\n" (int_ceiling x) (int_ceiling y)
  wprintf "%%%%HiResBoundingBox: 0 0 %f %f\n" x y
  wprintf "%%%%Pages: %d\n" pagecount
  wPutStrLn "%%EOF"
  return a

-- | Global PostScript definitions used by the rendering engine.
global_ps_defs :: String
global_ps_defs = "/textbox { /b exch def /align exch def /y1 exch def /x1 exch def /y0 exch def /x0 exch def /dx x1 x0 sub def /dy y1 y0 sub def /d dx dx mul dy dy mul add sqrt def dup stringwidth pop /w exch def /fontscale w d le {d} {w} ifelse def gsave [dx dy dy neg dx x0 y0] concat 1 fontscale div dup scale fontscale w sub align mul b moveto show grestore } bind def\n"
        
-- | Render pages as PostScript.
pages_to_ps :: Document a -> PSWriter a
pages_to_ps (Document_Return a) = return a
pages_to_ps (Document_Page x y draw) = do
  page <- ps_next_page
  ps_add_bbox x y
  wprintf "%%%%Page: %d %d\n" page page
  wprintf "%%%%PageBoundingBox: 0 0 %d %d\n" (int_ceiling x) (int_ceiling y)
  wprintf "%%%%PageHiResBoundingBox: 0 0 %f %f\n" x y
  wPutStrLn "save"
  cont <- draw_to_ps draw
  wPutStrLn "showpage"
  wPutStrLn "restore"
  pages_to_ps cont
pages_to_ps (Document_Page_defer draw) = do
  page <- ps_next_page
  wprintf "%%%%Page: %d %d\n" page page
  wPutStrLn "%%PageBoundingBox: (atend)"
  wPutStrLn "%%PageHiResBoundingBox: (atend)"
  (x, y, cont) <- draw_to_ps draw
  wPutStrLn "showpage"
  wPutStrLn "%%PageTrailer"
  wprintf "%%%%PageBoundingBox: 0 0 %d %d\n" (int_ceiling x) (int_ceiling y)
  wprintf "%%%%PageHiResBoundingBox: 0 0 %f %f\n" x y
  ps_add_bbox x y
  pages_to_ps cont

-- ----------------------------------------------------------------------
-- ** Rendering to the Writer monad

-- | Render document as PostScript. The first argument is a
-- customization data structure.
render_ps_custom :: Custom -> Document a -> Writer a
render_ps_custom custom doc = 
  pswriter_run (document_to_ps custom doc)

-- ----------------------------------------------------------------------
-- * EPS output

-- $ Encapsulated PostScript (EPS) output is slightly different from
-- normal PostScript output. EPS is limited to a single page, and
-- contains no \"showpage\" command. We permit the user to print a
-- single page from a multi-page document, by specifying the page
-- number.

-- | Render a document as EPS. Since EPS only permits a single page of
-- output, the 'Page' parameter is used to specify which page (of a
-- potential multi-page document) should be printed. An error will be
-- thrown if the page number was out of range.
-- 
-- Note: if the return value is not used, the remaining pages are
-- lazily skipped.
document_to_eps :: Custom -> Page -> Document a -> PSWriter a
document_to_eps custom page (Document_Return a) = 
  error "document_to_eps: requested page does not exist"
document_to_eps custom page (Document_Page x y draw)  
  | page == 1 = do
      -- EPS header
      wPutStrLn "%!PS-Adobe-3.0 EPSF-3.0"
      wPutStrLn "%%LanguageLevel: 2"
      when (creator custom /= "") $ do
        wprintf "%%%%Creator: %s\n" (creator custom)
      wprintf "%%%%BoundingBox: 0 0 %d %d\n" (int_ceiling x) (int_ceiling y)
      wprintf "%%%%HiResBoundingBox: 0 0 %f %f\n" x y
      wPutStrLn "%%Pages: 1"
      wPutStrLn "%%EndComments"
      wPutStrLn "%%Page: 1 1"
      wPutStrLn "save"
      wprintf "%s" global_ps_defs
      when (ps_defs custom /= "") $ do
        wprintf "%s" (ensure_nl $ ps_defs custom)
      cont <- draw_to_ps draw
      wPutStrLn "restore"
      wPutStrLn "%%EOF"
      let a = document_skip cont
      return a
  | otherwise = do
      let cont = draw_skip draw
      document_to_eps custom (page-1) cont
document_to_eps custom page (Document_Page_defer draw)  
  | page == 1 = do
      -- EPS header
      wPutStrLn "%!PS-Adobe-3.0 EPSF-3.0"
      wPutStrLn "%%LanguageLevel: 2"
      when (creator custom /= "") $ do
        wprintf "%%%%Creator: %s\n" (creator custom)
      wPutStrLn "%%BoundingBox: (atend)"
      wPutStrLn "%%HiResBoundingBox: (atend)"
      wPutStrLn "%%Pages: 1"
      wPutStrLn "%%EndComments"
      wPutStrLn "%%Page: 1 1"
      wPutStrLn "save"
      wprintf "%s" global_ps_defs
      when (ps_defs custom /= "") $ do
        wprintf "%s" (ensure_nl $ ps_defs custom)
      (x, y, cont) <- draw_to_ps draw
      wPutStrLn "restore"
      wPutStrLn "%%Trailer"
      wprintf "%%%%BoundingBox: 0 0 %d %d\n" (int_ceiling x) (int_ceiling y)
      wprintf "%%%%HiResBoundingBox: 0 0 %f %f\n" x y
      wPutStrLn "%%EOF"
      let a = document_skip cont
      return a
  | otherwise = do
      let (_, _, cont) = draw_skip draw
      document_to_eps custom (page-1) cont
        
-- | Render document as EPS. The first argument is a customization
-- data structure, and the second argument is the number of the page
-- to extract from the document.
render_eps_custom :: Custom -> Page -> Document a -> Writer a
render_eps_custom custom page doc = 
  pswriter_run (document_to_eps custom page doc)

-- ----------------------------------------------------------------------
-- * PDF output

-- ----------------------------------------------------------------------
-- ** Auxiliary functions

-- | Escape special characters in a string literal.
pdf_escape :: String -> String
pdf_escape [] = []
pdf_escape ('\\' : t) = '\\' : '\\' : pdf_escape t
pdf_escape ('('  : t) = '\\' : '('  : pdf_escape t
pdf_escape (')'  : t) = '\\' : ')'  : pdf_escape t
pdf_escape (h : t)    = h : pdf_escape t

-- ----------------------------------------------------------------------
-- ** The PDF state

-- $ Creating PDF files requires some state: we need to keep track of
-- the current file position, page numbering, and object numbering. 

-- | A position in a file. The first byte is 0.
type Filepos = Integer

-- | A PDF object reference.
type Object = Integer

-- | A state to keep track of PDF document structure: current
-- character count, current TOC, current page, etc.
data PDF_State = PDF_State {
  pdf_filepos :: !Filepos,              -- ^ Current position in file.
  pdf_obj :: !Object,                   -- ^ Object count.
  pdf_xref :: !(Map Object Filepos),    -- ^ Cross-reference table.
  pdf_page :: !Page,                    -- ^ Next available page number.
  pdf_pagetable :: !(Map Page Object),  -- ^ Page table.
  pdf_font :: !Integer,                 -- ^ Next available font number.
  pdf_fonttable :: !(Map String String) -- ^ Font table mapping each font's PostScript name to a local name.
  }
                 
-- | The initial 'PDF_State'.
pdf_state_empty :: PDF_State
pdf_state_empty = PDF_State {
  pdf_filepos = 0,
  pdf_obj = 0,
  pdf_xref = Map.empty,
  pdf_page = 0,
  pdf_pagetable = Map.empty,
  pdf_font = 0,
  pdf_fonttable = Map.empty
  }

-- ----------------------------------------------------------------------
-- ** The PDFWriter monad

-- | The 'RawPDFWriter' monad is just a 'PDF_State' wrapped around
-- the 'Writer' monad. Its 'wPutChar' and 'wPutStr' methods
-- automatically keep track of the file position.
type RawPDFWriter = StateT PDF_State Writer

instance WriterMonad RawPDFWriter where
  wPutChar c = do
    lift (wPutChar c)
    pdf_inc_filepos 1
  wPutStr s = do                 
    lift (wPutStr s)
    pdf_inc_filepos (toInteger $ length s)

-- | Boxed version of the 'RawPDFWriter' monad.
type PDFWriter = Boxed RawPDFWriter
  
-- | Run function for the 'PDFWriter' monad.
pdfwriter_run :: PDFWriter a -> Writer a
pdfwriter_run f = do
  evalStateT (unbox f) pdf_state_empty

-- ----------------------------------------------------------------------
-- *** Access functions for the PDFWriter monad

-- | Get the file position.
pdf_get_filepos :: PDFWriter Filepos
pdf_get_filepos = do
  s <- get
  return $ pdf_filepos s

-- | Add to the file position.
pdf_inc_filepos :: Integer -> RawPDFWriter ()
pdf_inc_filepos n = do
  s <- get
  let p = pdf_filepos s
  put s { pdf_filepos = p+n }

-- | Get the number of allocated objects. Note that objects are
-- allocated as 1, 2, ..., /n/; this function returns /n/.
pdf_get_objcount :: PDFWriter Object
pdf_get_objcount = do
  s <- get
  return $ pdf_obj s
  
-- | Allocate an unused object identifier.
pdf_next_object :: PDFWriter Object
pdf_next_object = do
  s <- get
  let o = pdf_obj s
  put s { pdf_obj = o+1 }  
  return $ o+1
  
-- | Add a cross reference to the cross reference table.
pdf_add_xref :: Object -> Filepos -> PDFWriter ()
pdf_add_xref obj pos = do
  s <- get
  let xref = pdf_xref s
  put s { pdf_xref = Map.insert obj pos xref }

-- | Retrieve the cross reference table.
pdf_get_xref :: PDFWriter (Map Object Filepos)
pdf_get_xref = do
  s <- get
  return $ pdf_xref s

-- | Get the page count.
pdf_get_pagecount :: PDFWriter Page
pdf_get_pagecount = do
  s <- get
  return $ pdf_page s
  
-- | Return the next page number.
pdf_next_page :: PDFWriter Page
pdf_next_page = do
  s <- get
  let p = pdf_page s
  put s { pdf_page = p+1 }
  return $ p+1

-- | Add a page to the page table.
pdf_add_pagetable :: Page -> Object -> PDFWriter ()
pdf_add_pagetable page obj = do
  s <- get
  let pagetable = pdf_pagetable s
  put s { pdf_pagetable = Map.insert page obj pagetable }

-- | Retrieve the page table.
pdf_get_pagetable :: PDFWriter (Map Page Object)
pdf_get_pagetable = do
  s <- get
  return $ pdf_pagetable s

-- | Look up the local font identifier for a font.
pdf_find_font :: String -> PDFWriter String  
pdf_find_font font = do
  s <- get
  let t = pdf_fonttable s
  case Map.lookup font t of
    Nothing -> do
      let f = pdf_font s
      let fontname = "F" ++ show f
      put s { pdf_font = f+1, pdf_fonttable = Map.insert font fontname t }
      return fontname
    Just fontname -> return fontname
  
-- | Retrieve the font table.
pdf_get_fonttable :: PDFWriter (Map String String)
pdf_get_fonttable = do
  s <- get
  return $ pdf_fonttable s

-- | Clear the font table.
pdf_clear_fonttable :: PDFWriter ()
pdf_clear_fonttable = do
  s <- get
  put s { pdf_font = 0, pdf_fonttable = Map.empty }

-- ----------------------------------------------------------------------
-- *** Filters
  
-- | A version of 'with_filter' tailored to the 'PDFWriter' monad.
-- 
-- This allows certain global state updates within the local block.
-- Specifically, updates to everything except the file position are
-- propagated from the inner to the outer block. The outer block's
-- file position is updated to reflect the encoded content's
-- length. From the inner block's point of view, the file position
-- starts from 0.
with_filter_pdf :: (String -> String) -> PDFWriter a -> PDFWriter a
with_filter_pdf encoding body = do
  s <- get
  let s' = s { pdf_filepos = 0 } -- pass everything except filepos to the body
  (a, s'') <- with_filter encoding $ do
    runStateT (unbox body) s'
  pos <- pdf_get_filepos
  put s'' { pdf_filepos = pos } -- pass everything except filepos from the body
  return a

-- ----------------------------------------------------------------------
-- *** Higher access functions

-- | Define an indirect PDF object with the given object id, which
-- must have previously been uniquely obtained with 'pdf_next_object'.
-- 
-- This can be used to define objects with forward references: first
-- obtain an object id, then create references to the object, and
-- finally define the object.
-- 
-- It should be used like this:
-- 
-- > obj <- pdf_next_object
-- > ...
-- > pdf_deferred_object obj $ do
-- >   <<object definition>>
pdf_deferred_object :: Object -> PDFWriter a -> PDFWriter a
pdf_deferred_object obj body = do
  pos <- pdf_get_filepos
  pdf_add_xref obj pos
  wprintf "%d 0 obj\n" obj
  a <- body
  wprintf "endobj\n"
  return a

-- | Define an indirect PDF object with a newly generated object id.
-- Return the object id. This essentially combines 'pdf_next_object'
-- and 'pdf_deferred_object' into a single function, and should be
-- used like this:
-- 
-- > obj <- pdf_define_object $ do
-- >   <<object definition>>
pdf_define_object :: PDFWriter a -> PDFWriter Object
pdf_define_object body = do
  obj <- pdf_next_object
  pdf_deferred_object obj body
  return obj

-- | Define a PDF stream object with the given object id, which must
-- have previously been uniquely obtained with 'pdf_next_object'. It
-- should be used like this:
-- 
-- > obj <- pdf_next_object
-- > ...
-- > pdf_deferred_stream obj $ do
-- >   <<stream contents>>
pdf_deferred_stream :: Object -> PDFWriter a -> PDFWriter a
pdf_deferred_stream obj body = do
  length_obj <- pdf_next_object
  (a, len) <- pdf_deferred_object obj $ do
    wprintf "<</Length %s>>\n" (objref length_obj)
    wPutStr "stream\n"
    x0 <- pdf_get_filepos
    a <- body
    x1 <- pdf_get_filepos
    wPutStr "\n"
    wPutStr "endstream\n"
    return (a, x1-x0)
  pdf_deferred_object length_obj $ do
    wprintf "%d\n" len
  return a

-- | Define a PDF stream object with a newly generated object
-- id. Return the object id. This should be used like this:
-- 
-- > obj <- pdf_define_stream $ do
-- >   <<stream contents>>
pdf_define_stream :: PDFWriter a -> PDFWriter Object  
pdf_define_stream body = do
  obj <- pdf_next_object
  pdf_deferred_stream obj body
  return obj

-- | Define a compressed PDF stream object with the given object id,
-- which must have previously been uniquely obtained with
-- 'pdf_next_object'. It should be used like this:
-- 
-- > obj <- pdf_next_object
-- > ...
-- > pdf_deferred_flate_stream obj $ do
-- >   <<stream contents>>
pdf_deferred_flate_stream :: Object -> PDFWriter a -> PDFWriter a
pdf_deferred_flate_stream obj body = do
  length_obj <- pdf_next_object
  (a, len) <- pdf_deferred_object obj $ do
    wprintf "<</Length %s/Filter/FlateDecode>>\n" (objref length_obj)
    wPutStr "stream\n"
    x0 <- pdf_get_filepos
    a <- with_filter_pdf flate_filter body
    x1 <- pdf_get_filepos
    wPutStr "\n"
    wPutStr "endstream\n"
    return (a, x1-x0)
  pdf_deferred_object length_obj $ do
    wprintf "%d\n" len
  return a

-- | Create a direct object from a reference to an indirect object.
objref :: Object -> String
objref n = 
  show n ++ " 0 R"

-- | Write one line in the cross reference table. This must be exactly
-- 20 characters long, including the terminating newline.
wprintf_xref_entry :: Filepos -> Integer -> Char -> PDFWriter ()
wprintf_xref_entry pos gen c =
  wprintf "%010u %05u %c \n" pos gen c

-- | Format the cross reference table. Return the file position of the
-- cross reference table.
wprintf_xref :: PDFWriter Filepos
wprintf_xref = do
  xref <- pdf_get_xref
  n <- pdf_get_objcount
  pos <- pdf_get_filepos
  wprintf "xref\n"
  wprintf "0 %d\n" (n+1)
  wprintf_xref_entry 0 65535 'f'
  sequence_ [ case Map.lookup obj xref of  
                 Nothing -> wprintf_xref_entry 0 0 'f' 
                 Just p -> wprintf_xref_entry p 0 'n' | obj <- [1..n] ]
  return pos

-- ----------------------------------------------------------------------
-- ** Internal rendering to the PDFWriter monad

-- | Set the fill color.
fillcolor_to_pdf :: Color -> PDFWriter ()
fillcolor_to_pdf (Color_RGB r g b) = do
  wprintf "%f %f %f rg\n" r g b
fillcolor_to_pdf (Color_Gray v) = do
  wprintf "%f g\n" v

-- | Set the stroke color.
strokecolor_to_pdf :: Color -> PDFWriter ()
strokecolor_to_pdf (Color_RGB r g b) = do
  wprintf "%f %f %f RG\n" r g b
strokecolor_to_pdf (Color_Gray v) = do
  wprintf "%f G\n" v

-- | Set the font.
font_to_pdf :: Font -> PDFWriter ()
font_to_pdf (Font TimesRoman pt) = do
  fn <- pdf_find_font "Times-Roman"
  wprintf "/%s %f Tf\n" fn pt
font_to_pdf (Font Helvetica pt) = do
  fn <- pdf_find_font "Helvetica"
  wprintf "/%s %f Tf\n" fn pt

-- | Render a drawing command to PDF.
command_to_pdf :: DrawCommand -> PDFWriter ()
command_to_pdf (Newpath) = do
  wPutStr "n\n"
command_to_pdf (Moveto x y) = do
  wprintf "%f %f m\n" x y
command_to_pdf (Lineto x y) = do
  wprintf "%f %f l\n" x y
command_to_pdf (Curveto x1 y1 x2 y2 x y) = do
  wprintf "%f %f %f %f %f %f c\n" x1 y1 x2 y2 x y
command_to_pdf (Closepath) = do
  wPutStr "h\n"
command_to_pdf (Stroke) = do
  wPutStr "S\n"
command_to_pdf (Fill color) = do
  fillcolor_to_pdf color
  wPutStr "f\n"
command_to_pdf (FillStroke color) = do
  fillcolor_to_pdf color
  wPutStr "B\n"
command_to_pdf (TextBox align font color x0 y0 x1 y1 b s) = do
  let w = text_width font s
      dx = x1 - x0
      dy = y1 - y0
      d = sqrt (dx*dx + dy*dy)
      f = max w d
      dxf = if f > 0 then dx/f else 1
      dyf = if f > 0 then dy/f else 1
      xshift = (f-w) * align
      yshift = -b * nominalsize font
  wPutStr "BT\n"
  font_to_pdf font
  wprintf "%f %f %f %f %f %f Tm\n" dxf dyf (-dyf) dxf (x0 + xshift*dxf - yshift*dyf) (y0 + xshift*dyf + yshift*dxf)
  fillcolor_to_pdf color
  wprintf "(%s) Tj\n" (pdf_escape s)
  wPutStr "ET\n"
command_to_pdf (SetLineWidth x) = do
  wprintf "%f w\n" x
command_to_pdf (SetColor color) = do
  strokecolor_to_pdf color
command_to_pdf (Translate x y) = do
  wprintf "1 0 0 1 %f %f cm\n" x y
command_to_pdf (Scale x y) = do
  wprintf "%f 0 0 %f 0 0 cm\n" x y
command_to_pdf (Rotate angle) = do
  wprintf "%f %f %f %f 0 0 cm\n" c s (-s) c where
    c = cos (pi/180 * angle)
    s = sin (pi/180 * angle)
command_to_pdf (Comment s) = do
  wprintf "%% %s\n" (remove_nl s)
command_to_pdf (Subroutine draw alt) = do
  case custom_lookup Language_PDF alt of
    Just out -> wprintf "%s" (ensure_nl out)
    Nothing -> draw_to_pdf draw

-- | Render a draw action to PDF.
draw_to_pdf :: Draw a -> PDFWriter a
draw_to_pdf (Draw_Return x) = return x
draw_to_pdf (Draw_Write cmd cont) = do
  command_to_pdf cmd
  draw_to_pdf cont
draw_to_pdf (Draw_Block body) = do
  wprintf "q\n"
  cont <- draw_to_pdf body
  wprintf "Q\n"
  draw_to_pdf cont

-- | Render pages as PDF. The first argument is a reference to the
-- document's page tree node. 
-- 
-- Note: Acrobat reader cannot handle pages whose bounding box width
-- or height exceed 200 inches (14400 points). Therefore, we
-- automatically scale pages to be no greater than 199 inches.
pages_to_pdf :: Object -> Document a -> PDFWriter a
pages_to_pdf pagetree_obj (Document_Return a) = return a
pages_to_pdf pagetree_obj (Document_Page x y draw) = do
  let sc = 14328 / maximum [x, y, 14328]
  page <- pdf_next_page
  wprintf "%% Page %d\n" page
  pdf_clear_fonttable
  contents_obj <- pdf_next_object
  cont <- pdf_deferred_flate_stream contents_obj $ do
    when (sc /= 1.0) $ do
      draw_to_pdf $ do
        scale sc sc
    draw_to_pdf draw
  fonttable_obj <- pdf_define_object $ do
    fonttable <- pdf_get_fonttable
    wprintf "<<\n"
    sequence_ [ wprintf "/%s<</Type/Font/Subtype/Type1/BaseFont/%s>>\n" x f | (f,x) <- Map.toList fonttable ]
    wprintf ">>\n"
  page_obj <- pdf_define_object $ do
    wprintf "<</Type/Page/Parent %s/Resources<</ProcSet[/PDF]/Font %s>>/MediaBox[0 0 %f %f]/Contents %s>>\n" (objref pagetree_obj) (objref fonttable_obj) (x*sc) (y*sc) (objref contents_obj)
  pdf_add_pagetable page page_obj
  pages_to_pdf pagetree_obj cont
pages_to_pdf pagetree_obj (Document_Page_defer draw) = do
  page <- pdf_next_page
  wprintf "%% Page %d\n" page
  pdf_clear_fonttable
  contents_obj <- pdf_next_object
  (x, y, cont) <- pdf_deferred_stream contents_obj $ do
    draw_to_pdf draw
  fonttable_obj <- pdf_define_object $ do
    fonttable <- pdf_get_fonttable
    wprintf "<<\n"
    sequence_ [ wprintf "/%s<</Type/Font/Subtype/Type1/BaseFont/%s>>\n" x f | (f,x) <- Map.toList fonttable ]
    wprintf ">>\n"
  let sc = 14328 / maximum [x, y, 14328]
  scaled_contents_obj <- 
    if sc == 1.0 then do
      return contents_obj
    else do
      scale_obj <- pdf_define_stream $ do
        draw_to_pdf $ do
          scale sc sc
      obj <- pdf_define_object $ do
        wprintf "[%s %s]\n" (objref scale_obj) (objref contents_obj)
      return obj
  page_obj <- pdf_define_object $ do
    wprintf "<</Type/Page/Parent %s/Resources<</ProcSet[/PDF]/Font %s>>/MediaBox[0 0 %f %f]/Contents %s>>\n" (objref pagetree_obj) (objref fonttable_obj) (x*sc) (y*sc) (objref scaled_contents_obj)
  pdf_add_pagetable page page_obj
  pages_to_pdf pagetree_obj cont
 
-- | Render a document as PDF.
document_to_pdf :: Custom -> Document a -> PDFWriter a
document_to_pdf custom document = do
  -- global header
  wprintf "%%PDF-1.3\n"
  info_obj <- pdf_define_object $ do
    if (creator custom /= "") 
      then wprintf "<</Creator(%s)>>\n" (pdf_escape $ creator custom)
      else wprintf "<<>>\n"
  pagetree_obj <- pdf_next_object
  catalog_obj <- pdf_define_object $ do
    wprintf "<</Type/Catalog/Pages %s>>\n" (objref pagetree_obj)
  a <- pages_to_pdf pagetree_obj document
  pages <- pdf_get_pagecount
  pagetable <- pdf_get_pagetable
  pdf_deferred_object pagetree_obj $ do
    wprintf "<</Type/Pages/Count %d/Kids[\n" pages
    sequence_ [ wprintf "%s\n" (objref o) | o <- Map.elems pagetable ]
    wprintf "]>>\n"
  xref_pos <- wprintf_xref
  wprintf "trailer\n"
  objcount <- pdf_get_objcount
  wprintf "<</Size %d/Root %s/Info %s>>\n" objcount (objref catalog_obj) (objref info_obj)
  wprintf "startxref\n"
  wprintf "%d\n" xref_pos
  wprintf "%%%%EOF\n"
  return a

-- ----------------------------------------------------------------------
-- ** Rendering to the Writer monad

-- | Render document as PDF. The first argument is a
-- customization data structure.
render_pdf_custom :: Custom -> Document a -> Writer a
render_pdf_custom custom doc = pdfwriter_run (document_to_pdf custom doc)

-- ----------------------------------------------------------------------
-- * Generic output functions

-- $BACKENDS 
-- 
-- The following commands can be used to render documents to various
-- available formats. The available formats are PostScript, PDF, EPS,
-- and an ASCII-based debugging format. Output can be written to
-- standard output, to a file, or to a string.
  
-- | Available graphics formats for rendering.
data RenderFormat = 
  Format_PS            -- ^ PostScript.
  | Format_PDF         -- ^ Portable Document Format.
  | Format_EPS Integer -- ^ Encapsulated PostScript. The integer
                       -- argument specifies which single page to
                       -- extract from the document.
  | Format_Debug       -- ^ An ASCII-based debugging format.
 deriving Show

-- | Does the format require raw binary output?
is_binary_format :: RenderFormat -> Bool
is_binary_format Format_PS = False
is_binary_format Format_PDF = True
is_binary_format (Format_EPS page) = False
is_binary_format Format_Debug = False

-- ----------------------------------------------------------------------
-- ** Rendering with custom format

-- $CUSTOMRENDER
-- 
-- The following are versions of the generic rendering functions that
-- also take a customization data structure as an additional
-- parameter.

-- | Render a document to the 'Writer' monad, using the given output
-- format and customization data structure.
render_custom :: RenderFormat -> Custom -> Document a -> Writer a
render_custom Format_PS = render_ps_custom
render_custom Format_PDF = render_pdf_custom
render_custom (Format_EPS page) = (\c -> render_eps_custom c page)
render_custom Format_Debug = \c -> render_ascii

-- | Render a document to a file, using the given output format and
-- customization data structure.
render_custom_file :: Handle -> RenderFormat -> Custom -> Document a -> IO a
render_custom_file h format custom d = do
  when (is_binary_format format) $ do
    hSetBinaryMode h True
  writer_to_file h (render_custom format custom d)

-- | Render a document to standard output, using the given output
-- format and customization data structure.
render_custom_stdout :: RenderFormat -> Custom -> Document a -> IO a
render_custom_stdout = render_custom_file stdout

-- | Render a document to a string, using the given output format and
-- customization data structure.
render_custom_string :: RenderFormat -> Custom -> Document a -> String
render_custom_string format custom d =
  writer_to_string (render_custom format custom d)  

-- ----------------------------------------------------------------------
-- ** Rendering without custom format

-- | Render a document to the 'Writer' monad, using the given output format.
render :: RenderFormat -> Document a -> Writer a
render format doc = render_custom format custom doc

-- | Render a document to a file, using the given output format.
render_file :: Handle -> RenderFormat -> Document a -> IO a
render_file h format doc = render_custom_file h format custom doc

-- | Render a document to standard output, using the given output format.
render_stdout :: RenderFormat -> Document a -> IO a
render_stdout = render_file stdout

-- | Render a document to a string, using the given output format.
render_string :: RenderFormat -> Document a -> String
render_string format doc = render_custom_string format custom doc
