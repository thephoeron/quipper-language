-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverlappingInstances #-}

-- | This module provides some functionality for pretty-printing
-- certain types to LaTeX format.

module Libraries.Synthesis.LaTeX where

import Libraries.Synthesis.CliffordT
import Libraries.Synthesis.MultiQubitSynthesis
import Libraries.Synthesis.Ring
import Libraries.Synthesis.Matrix
import Libraries.Synthesis.SymReal

import Text.Printf
import Data.Ratio

-- | A type class for things that can be printed to LaTeX format. 
-- 
-- Minimal complete definition: 'showlatex' or 'showlatex_p'.

-- This is a bit naive at the moment - to do it properly, one should
-- perhaps also supply context information, for example math mode/text
-- mode.
class ShowLaTeX a where
  -- | Print to LaTeX format.
  showlatex :: a -> String
  showlatex x = showlatex_p 0 x ""
  
  -- | Print to LaTeX format, with precedence. Analogous to 'showsPrec'.
  showlatex_p :: Int -> a -> ShowS
  showlatex_p _ x s = showlatex x ++ s

instance ShowLaTeX TwoLevel where
  showlatex (TL_X i j) = printf "X\\level{%d,%d} " (i+1) (j+1)
  showlatex (TL_H i j) = printf "H\\level{%d,%d} " (i+1) (j+1)
  showlatex (TL_T m i j)
    | m' == 0 = ""
    | m' == 1 = printf "T\\level{%d,%d} " (i+1) (j+1)
    | otherwise = printf "T^%d\\level{%d,%d} " m' (i+1) (j+1)
    where m' = m `mod` 8
  showlatex (TL_omega m i)
    | m' == 0 = ""
    | m' == 1 = printf "\\omega\\level{%d} " (i+1)
    | otherwise = printf "\\omega^%d\\level{%d} " m' (i+1)
    where m' = m `mod` 8
  
instance ShowLaTeX [TwoLevel] where
  showlatex = concat . map showlatex

instance ShowLaTeX Integer where
  showlatex = show

instance ShowLaTeX ZOmega where
  showlatex (Omega a b c d) = format_signed_list list2 where
    list = map signedunit [(a,"\\omega^3"),(b,"\\omega^2"),(c,"\\omega"),(d,"")]
    list2 = filter (\(s,a) -> s /= 0) list
    signedunit (a, u) 
      | u == ""   = (s, showlatex a')
      | a' == 1   = (s, u)
      | otherwise = (s, showlatex a' ++ u)
      where
        (s,a') = tosigned a
    tosigned a 
      | a < 0     = (-1,-a)
      | a == 0    = (0,0)
      | otherwise = (1,a)
    format_signed_list [] = "0"
    format_signed_list ((1,a):t) = a ++ cont t 
    format_signed_list ((_,a):t) = "-" ++ a ++ cont t 
    cont [] = ""
    cont ((1,a):t) = "+" ++ a ++ cont t
    cont ((0,a):t) = cont t
    cont ((_,a):t) = "-" ++ a ++ cont t

instance (ShowLaTeX a, Nat n) => ShowLaTeX (Matrix n m a) where
  showlatex (Matrix a) = "\\zmatrix{" ++ replicate m 'c' ++ "}{" ++ entries ++ "}" where
    m = length (list_of_vector a)
    entries = concat $ list_of_vector $ vector_map showcolumn (vector_transpose a)
    showcolumn :: ShowLaTeX a => Vector m a -> String
    showcolumn Nil = "\\\\"
    showcolumn (h `Cons` Nil) = showlatex h ++ "\\\\"
    showcolumn (h `Cons` t) = showlatex h ++ " & " ++ showcolumn t

instance ShowLaTeX Rational where
  showlatex r = "\\frac{" ++ showlatex num ++ "}{" ++ showlatex denom ++ "}"
    where
      num = numerator r
      denom = numerator r

instance ShowLaTeX Dyadic where
  showlatex = showlatex . toRational

instance (ShowLaTeX a, Eq a, Ring a) => ShowLaTeX (RootTwo a) where
  showlatex_p d (RootTwo a 0) = showlatex_p d a
  showlatex_p d (RootTwo 0 1) = showString "\\sqrt{2}"
  showlatex_p d (RootTwo 0 (-1)) = showParen (d > 5) $ showString "-\\sqrt{2}"
  showlatex_p d (RootTwo 0 b) = showParen (d > 10) $ 
    showlatex_p 11 b . showString " \\sqrt{2}"
  showlatex_p d (RootTwo a b) | signum b == 1 = showParen (d > 6) $
    showlatex_p 7 a . showString " + " . showlatex_p 7 (RootTwo 0 b)
  showlatex_p d (RootTwo a b) | otherwise = showParen (d > 6) $
    showlatex_p 7 a . showString " - " . showlatex_p 7 (RootTwo 0 (-b))
  

instance ShowLaTeX (Omega Z2) where
  showlatex (Omega a b c d) = concat $ map show [a,b,c,d]

instance (ShowLaTeX a, Ring a, Ord a) => ShowLaTeX (Cplx a) where
  showlatex_p d (Cplx a 0) = showlatex_p d a
  showlatex_p d (Cplx 0 1) = showString "i"
  showlatex_p d (Cplx 0 (-1)) = showParen (d > 5) $ showString "-i"
  showlatex_p d (Cplx 0 b) = showParen (d > 10) $
                             showlatex_p 11 b . showString "\\,i"
  showlatex_p d (Cplx a b) | b > 0 = showParen (d > 6) $
    showlatex_p 7 a . showString "+" . showlatex_p 7 (Cplx 0 b)
  showlatex_p d (Cplx a b) | otherwise = showParen (d > 6) $ 
    showlatex_p 7 a . showString "-" . showlatex_p 7 (Cplx 0 (-b))

instance ShowLaTeX Double where
  showlatex x = printf "%0.10f" x

-- This is an overlapping instance
instance Nat n => ShowLaTeX (Matrix n m DOmega) where
  showlatex = showlatex_denomexp

-- This is an overlapping instance
instance Nat n => ShowLaTeX (Matrix n m DComplex) where
  showlatex = showlatex_denomexp

-- | Generic showlatex-like method that factors out a common
-- denominator exponent.
showlatex_denomexp :: (WholePart a b, ShowLaTeX b, DenomExp a) => a -> String
showlatex_denomexp a
  | k == 0 = showlatex b
  | k == 1 = "\\frac{1}{\\sqrt{2}}" ++ showlatex b
  | otherwise = "\\frac{1}{\\sqrt{2}^{" ++ show k ++ "}}" ++ showlatex b
    where (b, k) = denomexp_decompose a

instance ShowLaTeX [Gate] where
  showlatex [] = "\\epsilon"
  showlatex gates = aux 0 gates where
    aux n (W:t) = aux (n+1) t
    aux 0 []    = ""
    aux 1 []    = "{\\omega}"
    aux n []    = "\\omega^" ++ show n
    aux 0 (h:t) = show h ++ aux 0 t
    aux n t     = aux n [] ++ aux 0 t

instance ShowLaTeX SymReal where
  showlatex_p d (Const x)     = showlatex_p d x
  showlatex_p d (Decimal x s) = showString s
  showlatex_p d (Plus x y)    = showParen (d > 6) $ showlatex_p 6 x . showString "+" . showlatex_p 6 y
  showlatex_p d (Minus x y)   = showParen (d > 6) $ showlatex_p 6 x . showString "-" . showlatex_p 7 y
  showlatex_p d (Times x y)   = showParen (d > 7) $ showlatex_p 7 x . showString "\\cdot" . showlatex_p 7 y
  showlatex_p d (Div x y)     = showParen (d > 7) $ showlatex_p 7 x . showString "/" . showlatex_p 8 y
  showlatex_p d (Power x y)   = showParen (d > 11) $ showlatex_p 12 x . showString "^{" . showlatex_p 0 y . showString "}"
  showlatex_p d (Negate x)    = showParen (d > 5) $ showString "-" . showlatex_p 7 x
  showlatex_p d (Abs x)       = showParen (d > 10) $ showString "|" . showlatex_p 11 x . showString "|"
  showlatex_p d (Signum x)    = showParen (d > 10) $ showString "\\signum " . showlatex_p 11 x
  showlatex_p d (Recip x)     = showParen (d > 7) $ showString "1/" . showlatex_p 8 x
  showlatex_p d Pi            = showString "\\pi"
  showlatex_p d Euler         = showString "e"
  showlatex_p d (Exp x)       = showParen (d > 10) $ showString "e^{" . showlatex_p 0 x . showString "}"
  showlatex_p d (Sqrt x)      = showString "\\sqrt{" . showlatex_p 0 x . showString "}"
  showlatex_p d (Log x)       = showParen (d > 10) $ showString "\\log " . showlatex_p 11 x
  showlatex_p d (Sin x)       = showParen (d > 10) $ showString "\\sin " . showlatex_p 11 x
  showlatex_p d (Tan x)       = showParen (d > 10) $ showString "\\tan " . showlatex_p 11 x
  showlatex_p d (Cos x)       = showParen (d > 10) $ showString "\\cos " . showlatex_p 11 x
  showlatex_p d (ASin x)      = showParen (d > 10) $ showString "\\asin " . showlatex_p 11 x
  showlatex_p d (ATan x)      = showParen (d > 10) $ showString "\\atan " . showlatex_p 11 x
  showlatex_p d (ACos x)      = showParen (d > 10) $ showString "\\acos " . showlatex_p 11 x
  showlatex_p d (Sinh x)      = showParen (d > 10) $ showString "\\sinh " . showlatex_p 11 x
  showlatex_p d (Tanh x)      = showParen (d > 10) $ showString "\\tanh " . showlatex_p 11 x
  showlatex_p d (Cosh x)      = showParen (d > 10) $ showString "\\cosh " . showlatex_p 11 x
  showlatex_p d (ASinh x)     = showParen (d > 10) $ showString "\\asinh " . showlatex_p 11 x
  showlatex_p d (ATanh x)     = showParen (d > 10) $ showString "\\atanh " . showlatex_p 11 x
  showlatex_p d (ACosh x)     = showParen (d > 10) $ showString "\\acosh " . showlatex_p 11 x
  showlatex_p d (ArcTan2 y x) = showParen (d > 10) $ showString "\\arctan2 " . showlatex_p 11 y . showString " " . showlatex_p 11 x
