-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}

-- | This module provides a symbolic representation of real number
-- expressions, as well as a type class of things that can be
-- converted to arbitrary precision real numbers.
module Libraries.Synthesis.SymReal where

import Libraries.Synthesis.ArcTan2

import Control.Monad
import Data.Char (isAlpha, isAlphaNum, isDigit)
import Data.Number.FixedPrec
import Text.ParserCombinators.ReadP
import Data.Ratio

-- ----------------------------------------------------------------------
-- * Symbolic real number expressions

-- | A type to represent symbolic expressions for real numbers.
-- 
-- Caution: equality '==' at this type denotes symbolic equality of
-- expressions, not equality of the defined real numbers.
data SymReal =
  Const Integer             -- ^ An integer constant.
  | Decimal Rational String -- ^ A decimal constant. This has a rational value and a string representation.
  | Plus SymReal SymReal    -- ^ /x/ @+@ /y/.
  | Minus SymReal SymReal   -- ^ /x/ @−@ /y/.
  | Times SymReal SymReal   -- ^ /x/ @*@ /y/.
  | Div SymReal SymReal     -- ^ /x/ @\/@ /y/.
  | Negate SymReal          -- ^ \−/x/.
  | Abs SymReal             -- ^ |/x/|.
  | Signum SymReal          -- ^ signum(/x/).
  | Recip SymReal           -- ^ 1\//x/.
  | Pi                      -- ^ π.
  | Euler                   -- ^ /e/.
  | Exp SymReal             -- ^ \[exp /x/].
  | Sqrt SymReal            -- ^ √/x/.
  | Log SymReal             -- ^ log /x/.
  | Power SymReal SymReal   -- ^ /x/[sup /y/].
  | Sin SymReal             -- ^ sin /x/.
  | Tan SymReal             -- ^ cos /x/.
  | Cos SymReal             -- ^ cos /x/.
  | ASin SymReal            -- ^ asin /x/.
  | ATan SymReal            -- ^ atan /x/.
  | ACos SymReal            -- ^ acos /x/.
  | Sinh SymReal            -- ^ sinh /x/.
  | Tanh SymReal            -- ^ tanh /x/.
  | Cosh SymReal            -- ^ cosh /x/.
  | ASinh SymReal           -- ^ asinh /x/.
  | ATanh SymReal           -- ^ atanh /x/.
  | ACosh SymReal           -- ^ acosh /x/.
  | ArcTan2 SymReal SymReal -- ^ arctan2 /x/ /y/.
    deriving (Eq)

instance Show SymReal where
  showsPrec d (Const x)     = showsPrec d x
  showsPrec d (Decimal x s) = showString s
  showsPrec d (Plus x y)    = showParen (d > 6) $ showsPrec 6 x . showString "+" . showsPrec 6 y
  showsPrec d (Minus x y)   = showParen (d > 6) $ showsPrec 6 x . showString "-" . showsPrec 7 y
  showsPrec d (Times x y)   = showParen (d > 7) $ showsPrec 7 x . showString "*" . showsPrec 7 y
  showsPrec d (Div x y)     = showParen (d > 7) $ showsPrec 7 x . showString "/" . showsPrec 8 y
  showsPrec d (Power x y)   = showParen (d > 8) $ showsPrec 9 x . showString "**" . showsPrec 9 y
  showsPrec d (Negate x)    = showParen (d > 5) $ showString "-" . showsPrec 7 x
  showsPrec d (Abs x)       = showParen (d > 10) $ showString "abs " . showsPrec 11 x
  showsPrec d (Signum x)    = showParen (d > 10) $ showString "signum " . showsPrec 11 x
  showsPrec d (Recip x)     = showParen (d > 7) $ showString "1/" . showsPrec 8 x
  showsPrec d Pi            = showString "pi"
  showsPrec d Euler         = showString "e"
  showsPrec d (Exp x)       = showParen (d > 10) $ showString "exp " . showsPrec 11 x
  showsPrec d (Sqrt x)      = showParen (d > 10) $ showString "sqrt " . showsPrec 11 x
  showsPrec d (Log x)       = showParen (d > 10) $ showString "log " . showsPrec 11 x
  showsPrec d (Sin x)       = showParen (d > 10) $ showString "sin " . showsPrec 11 x
  showsPrec d (Tan x)       = showParen (d > 10) $ showString "tan " . showsPrec 11 x
  showsPrec d (Cos x)       = showParen (d > 10) $ showString "cos " . showsPrec 11 x
  showsPrec d (ASin x)      = showParen (d > 10) $ showString "asin " . showsPrec 11 x
  showsPrec d (ATan x)      = showParen (d > 10) $ showString "atan " . showsPrec 11 x
  showsPrec d (ACos x)      = showParen (d > 10) $ showString "acos " . showsPrec 11 x
  showsPrec d (Sinh x)      = showParen (d > 10) $ showString "sinh " . showsPrec 11 x
  showsPrec d (Tanh x)      = showParen (d > 10) $ showString "tanh " . showsPrec 11 x
  showsPrec d (Cosh x)      = showParen (d > 10) $ showString "cosh " . showsPrec 11 x
  showsPrec d (ASinh x)     = showParen (d > 10) $ showString "asinh " . showsPrec 11 x
  showsPrec d (ATanh x)     = showParen (d > 10) $ showString "atanh " . showsPrec 11 x
  showsPrec d (ACosh x)     = showParen (d > 10) $ showString "acosh " . showsPrec 11 x
  showsPrec d (ArcTan2 y x) = showParen (d > 10) $ showString "arctan2 " . showsPrec 11 y . showString " " . showsPrec 11 x

instance Num SymReal where
  (+) = Plus
  (*) = Times
  (-) = Minus
  negate = Negate
  abs = Abs
  signum = Signum
  fromInteger = Const
  
instance Fractional SymReal where
  (/) = Div
  recip = Recip
  fromRational x = Const (numerator x) `Div` Const (denominator x)
  
instance Floating SymReal where
  pi = Pi
  exp = Exp
  sqrt = Sqrt
  log = Log
  (**) = Power
  logBase x y = log y / log x
  sin = Sin
  tan = Tan
  cos = Cos
  asin = ASin
  atan = ATan
  acos = ACos
  sinh = Sinh
  tanh = Tanh
  cosh = Cosh
  asinh = ASinh
  atanh = ATanh
  acosh = ACosh

instance ArcTan2 SymReal where
  arctan2 y x = ArcTan2 y x

-- ----------------------------------------------------------------------
-- * Conversion to real number types

-- | A type class for things that can be converted to a real number at
-- arbitrary precision.
class ToReal a where
  to_real :: (Floating r, ArcTan2 r) => a -> r

instance ToReal SymReal where
  to_real (Const x) = fromInteger x
  to_real (Decimal x s) = fromRational x
  to_real (Plus x y) = to_real x + to_real y
  to_real (Minus x y) = to_real x - to_real y
  to_real (Times x y) = to_real x * to_real y
  to_real (Negate x) = -(to_real x)
  to_real (Abs x) = abs (to_real x)
  to_real (Signum x) = signum (to_real x)
  to_real (Div x y) =  to_real x / to_real y
  to_real (Recip x) = recip (to_real x)
  to_real Pi = pi
  to_real Euler = exp 1
  to_real (Exp x) = exp (to_real x)
  to_real (Sqrt x) = sqrt (to_real x)
  to_real (Log x) = log (to_real x)
  to_real (Power x y) = to_real x ** to_real y
  to_real (Sin x) = sin (to_real x)
  to_real (Tan x) = tan (to_real x)
  to_real (Cos x) = cos (to_real x)
  to_real (ASin x) = asin (to_real x)
  to_real (ATan x) = atan (to_real x)
  to_real (ACos x) = acos (to_real x)
  to_real (Sinh x) = sinh (to_real x)
  to_real (Tanh x) = tanh (to_real x)
  to_real (Cosh x) = cosh (to_real x)
  to_real (ASinh x) = asinh (to_real x)
  to_real (ATanh x) = atanh (to_real x)
  to_real (ACosh x) = acosh (to_real x)
  to_real (ArcTan2 y x) = arctan2 (to_real y) (to_real x)
  
instance ToReal Rational where
  to_real = fromRational
  
instance ToReal Integer where
  to_real = fromInteger
  
instance ToReal Int where
  to_real = fromIntegral
  
instance ToReal Double where
  to_real = fromRational . toRational

instance ToReal Float where
  to_real = fromRational . toRational

instance (Precision e) => ToReal (FixedPrec e) where
  to_real = fromRational . toRational

instance ToReal String where
  to_real x = case parse_SymReal x of
    Just n -> to_real n
    Nothing -> error "ToReal String: string does not parse"

-- ----------------------------------------------------------------------
-- ** Dynamic conversion to FixedPrec

-- | It would be useful to have a function for converting a symbolic
-- real number to a fixed-precision real number with a chosen
-- precision, such that the precision /e/ depends on a parameter /d/:
-- 
-- > to_fixedprec :: (ToReal r) => Integer -> r -> FixedPrec e
-- > to_fixedprec d x = ...
--  
-- However, since /e/ is a type, /d/ is a term, and Haskell is not
-- dependently typed, this cannot be done directly.
-- 
-- The function 'dynamic_fixedprec' is the closest thing we have to a
-- workaround. The call @dynamic_fixedprec@ /d/ /f/ /x/ calls
-- /f/(/x/'), where /x/' is the value /x/ converted to /d/ digits of
-- precision.  In other words, we have
-- 
-- > dynamic_fixedprec d f x = f (to_fixedprec d x),
-- 
-- with the restriction that the precision /e/ cannot occur freely in
-- the result type of /f/.
dynamic_fixedprec :: forall a r.(ToReal r) => Integer -> (forall e.(Precision e) => FixedPrec e -> a) -> r -> a
dynamic_fixedprec d f x = loop d (undefined :: P0)
  where 
    loop :: forall e.(Precision e) => Integer -> e -> a
    loop d e
      | d >= 1000 = loop (d-1000) (undefined :: PPlus1000 e)
      | d >= 100  = loop (d-100)  (undefined :: PPlus100 e)
      | d >= 10   = loop (d-10) (undefined :: PPlus10 e)
      | d > 0     = loop (d-1) (undefined :: PPlus1 e)
      | otherwise = f (to_real x :: FixedPrec e)

-- | Like 'dynamic_fixedprec', but take two real number arguments. In
-- terms of the fictitious function @to_fixedprec@, we have:
-- 
-- > dynamic_fixedprec2 d f x y = f (to_fixedprec d x) (to_fixedprec d y).
dynamic_fixedprec2 :: forall a r s.(ToReal r, ToReal s) => Integer -> (forall e.(Precision e) => FixedPrec e -> FixedPrec e -> a) -> r -> s -> a
dynamic_fixedprec2 d f x y = loop d (undefined :: P0)
  where 
    loop :: forall e.(Precision e) => Integer -> e -> a
    loop d e
      | d >= 1000 = loop (d-1000) (undefined :: PPlus1000 e)
      | d >= 100  = loop (d-100)  (undefined :: PPlus100 e)
      | d >= 10   = loop (d-10) (undefined :: PPlus10 e)
      | d > 0     = loop (d-1) (undefined :: PPlus1 e)
      | otherwise = f (to_real x :: FixedPrec e) (to_real y :: FixedPrec e)

-- ----------------------------------------------------------------------
-- * A parser for real number expressions
  
-- ----------------------------------------------------------------------
-- ** Grammar specification

-- $ Each function in this section corresponds to a production rule
-- for a context-free grammar. The type of each function is 'ReadP'
-- /a/, where /a/ is the type of the semantic value produced by the
-- grammar for that expression.
-- 
-- The parser uses simple precedences. 
-- 
-- * Unary \"+\" and \"−\" have precedence 6. 
-- 
-- * Binary \"+\" and \"−\" have precedence 6 and are left
-- associative.
-- 
-- * Binary \"*\" and \"\/\" have precedence 7 and are left
-- associative.
-- 
-- * Binary \"**\" and \"^\" have precedence 8 and are right
-- associative.
-- 
-- * All unary operators other than \"+\" and \"−\" have precedence
-- 10.
-- 
-- We use /exp6/ to denote an expression whose
-- top-level operator has precedence 6 or higher, /exp7/ to denote an
-- expression whose top-level operator has precedence 7 or higher, and
-- so on.
-- 
-- We also allow whitespace between lexicographic entities. For
-- simplicity, whitespace is not shown in the production rules,
-- although it appears in the code.

-- | /integer/ ::= /digit/ /digit/*.
integer :: ReadP SymReal
integer = do
  s <- munch1 isDigit
  let n = read s
  return (Const (fromInteger n))

-- | /float/ ::= /digit/* \".\" /digit/*.
-- 
-- There must be at least one digit, either before or after the decimal point.
float :: ReadP SymReal
float = do
  (s1, _) <- gather $ do
    munch isDigit
  char '.'
  (s2, _) <- gather $ do
    munch isDigit
  when (length s1 == 0 && length s2 == 0) $ do
    pfail
  let num = read (s1++s2) :: Integer
  let denom = 10^(length s2)
  let s1' = if s1 == [] then "0" else s1
  let s2' = if s2 == [] then "0" else s2
  return (Decimal (num % denom) (s1' ++ "." ++ s2'))

-- | /const_pi/ ::= \"pi\".
const_pi :: ReadP SymReal
const_pi = do
  string "pi"
  return Pi

-- | /const_e/ ::= \"e\".
const_e :: ReadP SymReal
const_e = do
  string "e"
  return Euler

-- | /negative/ ::= \"−\".
negative :: ReadP (SymReal -> SymReal)
negative = do
  string "-"
  skipSpaces
  return Negate

-- | /positive/ ::= \"+\".
positive :: ReadP (SymReal -> SymReal)
positive = do
  string "+"
  skipSpaces
  return id

-- | /plus_term/ ::= \"+\" /exp7/.
plus_term :: ReadP (SymReal -> SymReal)
plus_term = do
  skipSpaces
  string "+"
  skipSpaces
  n2 <- exp7
  return (\n1 -> Plus n1 n2)

-- | /minus_term/ ::= \"−\" /exp7/.
minus_term :: ReadP (SymReal -> SymReal)
minus_term = do
  skipSpaces
  string "-"
  skipSpaces
  n2 <- exp7
  return (\n1 -> Minus n1 n2)

-- | /times_term/ ::= \"*\" /exp8/.
times_term :: ReadP (SymReal -> SymReal)
times_term = do
  skipSpaces
  string "*"
  skipSpaces
  n2 <- exp8
  return (\n1 -> Times n1 n2)

-- | /div_term/ ::= \"\/\" /exp8/.
div_term :: ReadP (SymReal -> SymReal)
div_term = do
  skipSpaces
  string "/"
  skipSpaces
  n2 <- exp8
  return (\n1 -> Div n1 n2)

-- | /power_term/ ::= /exp10/ \"**\" | /exp10/ \"^\".
power_term :: ReadP (SymReal -> SymReal)
power_term = do
  n1 <- exp10
  skipSpaces
  string "**" +++ string "^"
  skipSpaces
  return (\n2 -> Power n1 n2)

-- | /unary_fun/ ::= /unary_op/ /exp10/.
unary_fun :: ReadP SymReal
unary_fun = do
  skipSpaces
  op <- unary_op
  skipSpaces
  n <- exp10
  return (op n)

-- | /unary_op/ ::= \"abs\" | \"signum\" | ...
unary_op :: ReadP (SymReal -> SymReal)
unary_op = 
  choice [ do { string s; return op } | (s, op) <- ops ]
  where 
    ops = [ ("abs", Abs),
            ("signum", Signum),
            ("recip", Recip),
            ("exp", Exp),
            ("sqrt", Sqrt),
            ("log", Log),
            ("sin", Sin),
            ("tan", Tan),
            ("cos", Cos),
            ("asin", ASin),
            ("atan", ATan),
            ("acos", ACos),
            ("sinh", Sinh),
            ("tanh", Tanh),
            ("cosh", Cosh),
            ("asinh", ASinh),
            ("atanh", ATanh),
            ("acosh", ACosh) ]

-- | /binary_fun/ ::= /binary_op/ /exp10/ /exp10/.
binary_fun :: ReadP SymReal
binary_fun = do
  skipSpaces
  op <- binary_op
  skipSpaces
  n <- exp10
  skipSpaces
  m <- exp10
  return (op n m)

-- | /binary_op/ ::= \"abs\" | \"signum\" | ...
binary_op :: ReadP (SymReal -> SymReal -> SymReal)
binary_op = 
  choice [ do { string s; return op } | (s, op) <- ops ]
  where 
    ops = [ ("arctan2", ArcTan2) ]

-- | /exp6/ ::= (/negative/ | /positive/)? /exp7/ ( /plus_term/ | /minus_term/ )*.
-- 
-- An expression whose top-level operator has precedence 6 or
-- above. The operators of precedence 6 are \"+\" and \"−\".
exp6 :: ReadP SymReal
exp6 = do
  sign <- option id (negative +++ positive)
  n1 <- exp7
  ops <- many $ do
    plus_term +++ minus_term
  return (foldl (\x f -> f x) (sign n1) ops)

-- | /exp7/ ::= /exp8/ ( /times_term/ | /div_term/ )*.
-- 
-- An expression whose top-level operator has precedence 7 or
-- above. The operators of precedence 6 are \"*\" and \"\/\".
exp7 :: ReadP SymReal
exp7 = do
  n1 <- exp8
  ops <- many $ do
    times_term +++ div_term
  return (foldl (\x f -> f x) n1 ops)

-- | /exp8/ ::= ( /power_term/ )* /exp10/
-- 
-- An expression whose top-level operator has precedence 8 or
-- above. The operators of precedence 6 are \"**\" and \"^\".
exp8 :: ReadP SymReal
exp8 = do
  ops <- many $ do
    power_term
  n2 <- exp10
  return (foldr (\f x -> f x) n2 ops)

-- | /exp10/ ::= /parenthesized/ | /const_pi/ | /const_e/ | /integer/ | /float/ | /unary_fun/ | /binary_fun/.
-- 
-- An expression whose top-level operator has precedence 10 or
-- above. Such expressions are constants, applications of unary
-- operators (except unary \"−\" and \"+\"), and parenthesized
-- expressions.
exp10 :: ReadP SymReal
exp10 = parenthesized +++ const_pi +++ const_e +++ integer +++ float +++ unary_fun +++ binary_fun

-- | /parenthesized/ ::= \"(\" /exp6/ \")\".
parenthesized :: ReadP SymReal
parenthesized = do
  string "("
  skipSpaces
  n <- exp6
  skipSpaces
  string ")"
  return n

-- | /expression/ ::= /exp6/ /end-of-line/.
--   
-- This is a top-level expression.
expression :: ReadP SymReal
expression = do
  skipSpaces
  s <- exp6
  skipSpaces
  eof
  return s

-- ----------------------------------------------------------------------
-- ** Top-level parser

-- | Parse a symbolic real number expression. Typical strings that can
-- be parsed are @\"1.0\"@, @\"pi\/128\"@, @\"(1+sin(pi\/3))^2\"@, etc. If
-- the expression cannot be parsed, return 'Nothing'.
parse_SymReal :: String -> Maybe SymReal
parse_SymReal s =
  case readP_to_S expression s of
    (h, ""):_ -> Just h
    _ -> Nothing
