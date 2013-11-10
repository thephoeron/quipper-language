-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

-- ----------------------------------------------------------------------
-- | This program reads an execution trace produced by QCL, and turns
-- it into a Quipper circuit.

module Programs.QCLParser.Main where

import Quipper hiding (cnot, Format)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.Traversable as Trav
import Control.Monad.State
import Prelude hiding (not)
import qualified Prelude
import System.IO
import Data.Complex
import Data.Maybe

import Text.ParserCombinators.ReadP hiding (get)
import Data.Char (isAlpha, isAlphaNum, isDigit)

-- ----------------------------------------------------------------------
-- * A monad for a QCL state

-- | In QCL, qubits are identified by integers. We have to map these
-- to Quipper's native qubits. A 'QCLState' holds such a map.
-- Implicitly, it also holds the set of qubits currently defined.
type QCLState = IntMap Qubit

-- | The 'QCLCirc' monad is like the 'Circ' monad, except that it also
-- keeps track of an additional 'QCLState'. The 'lift' function must
-- be used to lift any command for the 'Circ' monad to the 'QCLCirc'
-- monad.
type QCLCirc a = StateT QCLState Circ a

-- ----------------------------------------------------------------------
-- * Auxiliary state functions

-- | Look up the qubit corresponding to a QCL register, or allocate a
-- new qubit if it doesn't already exist.
provide :: Int -> QCLCirc Qubit
provide r = do
  s <- get
  case IntMap.lookup r s of
    Just q -> return q
    Nothing -> do
      q <- lift $ qinit False
      let s' = IntMap.insert r q s
      put s'
      return q

-- ----------------------------------------------------------------------
-- * Implementation of the QCL primitives

-- | Reset all qubits to state 0.
qcl_reset :: QCLCirc ()
qcl_reset = do
  s <- get
  lift $ Trav.mapM qdiscard s
  let s' = IntMap.empty
  put s'
  return ()

-- | Apply a controlled-not operation to the first argument.
qcl_cnot :: Int -> [Int] -> QCLCirc ()
qcl_cnot r ctrls = do
  q <- provide r
  cs <- Trav.mapM provide ctrls
  lift $ qnot_at q `controlled` cs
  return ()

-- | Apply an uncontrolled not operation.
qcl_not :: Int -> QCLCirc ()
qcl_not r = qcl_cnot r []

-- | @'qcl_fanout' ins outs ctrls@: Copy the qubit register /ins/ to
-- the qubit register /outs/ by means of c-not operations, provided
-- that /outs/ was previously 0. The whole operation is controlled by
-- /ctrls/.
qcl_fanout :: [Int] -> [Int] -> [Int] -> QCLCirc ()
qcl_fanout ins outs ctrls = do
  qins <- Trav.mapM provide ins
  qouts <- Trav.mapM provide outs
  qctrls <- Trav.mapM provide ctrls
  lift $ with_controls qctrls $ do
    let zips = zip qins qouts
    Trav.mapM (\(x,y) -> qnot_at y `controlled` x) zips
  return ()

-- | Calculate the square distance between two vectors, which must be
-- of the same length.
sqdist :: [Complex Double] -> [Complex Double] -> Double
sqdist v1 v2 = d2 where
  w = zipWith (-) v1 v2
  w2 = map (\x -> x * x) $ map magnitude w
  d2 = sum w2
      
-- | If the matrix looks like a /W/-gate, return 'True'.
matrix_w :: [Complex Double] -> Bool
matrix_w amps | length amps == 16 =
  let v = sqrt 0.5
      m = [ 1, 0, 0, 0,
            0, v, v, 0,
            0, v, -v, 0,
            0, 0, 0, 1]
  in
   if sqdist amps m <= 0.001 then
     True
   else
     False
matrix_w _ = False

-- | If the matrix looks like a controlled /e/^/tiZ/-gate, return the
-- angle /t/.
matrix_exp :: [Complex Double] -> Maybe Double
matrix_exp amps | length amps == 16 =
  let t = phase ((amps !! 10) + conjugate (amps !! 15))
      u = cis t
      m = [ 1, 0, 0, 0,
            0, 1, 0, 0, 
            0, 0, u, 0,
            0, 0, 0, conjugate u]
  in
   if sqdist amps m <= 0.001 then
     Just t
   else
     Nothing
matrix_exp _ = Nothing

-- | @'qcl_matrix' n amps regs@: Apply the /n/-by-/n/ unitary gate
-- whose matrix is given in /amps/, to the qubit list /regs/.  This
-- function must guess, based on the complex entries of the matrix,
-- what the name of the gate should be. This guessing is crude at the
-- moment, and must be extended to include additional gates as
-- required by each algorithm. If the first argument is 'True', invert
-- the matrix.
qcl_matrix :: Bool -> Int -> [Complex Double] -> [Int] -> QCLCirc ()
qcl_matrix inv n amps [x,y] | matrix_w amps = do
  [q,r] <- Trav.mapM provide [x,y]
  lift $ gate_W_at q r  -- this gate is self-inverse
qcl_matrix inv n amps [x,y] | isJust t = do
  [q,r] <- Trav.mapM provide [x,y]
  lift $ expZt_at (sign * fromJust t) r `controlled` q
    where
      t = matrix_exp amps
      sign = if inv then -1 else 1
qcl_matrix inv n amps regs = do
  qregs <- Trav.mapM provide regs
  lift $ named_gate_at (if inv then "Gate*" else "Gate") qregs
        
-- | The inverse of 'qcl_cnot'.
qcl_cnot_inv = qcl_cnot

-- | The inverse of 'qcl_not'.
qcl_not_inv = qcl_not

-- | The inverse of 'qcl_fanout'.
qcl_fanout_inv = qcl_fanout

-- | A sample circuit to illustrate how to use the primitives.
testcircuit1 :: QCLCirc ()
testcircuit1 = do
  qcl_reset
  qcl_not 5
  qcl_not 0
  qcl_cnot 31 [4]
  qcl_cnot 31 [4,30]
  qcl_cnot 29 [31]
  qcl_cnot_inv 31 [4,30]
  qcl_cnot_inv 31 [4]

-- ----------------------------------------------------------------------
-- * Unpacking QCLCirc

-- | Run function for the 'QCLCirc' monad: execute the actions and
-- produce a circuit.
run :: QCLCirc a -> Circ a
run f = do
  (x,_) <- runStateT f IntMap.empty
  return x

-- ----------------------------------------------------------------------
-- * An abstract syntax for QCL output

-- | A data type to hold a QCL gate.
data QCLGate = 
  Comment
  | Reset
  | Not Int
  | XNot Int
  | CNot Int [Int]
  | XCNot Int [Int]
  | Fanout [Int] [Int] [Int]
  | XFanout [Int] [Int] [Int]
  | Matrix Int [Complex Double] [Int]
  | XMatrix Int [Complex Double] [Int]
  deriving (Show)

-- | Take a gate from the abstract syntax and execute it in the
-- 'QCLCirc' monad.
do_qcl_gate :: QCLGate -> QCLCirc ()
do_qcl_gate Comment = return ()
do_qcl_gate Reset = qcl_reset
do_qcl_gate (Not x) = qcl_not x
do_qcl_gate (XNot x ) = qcl_not_inv x            
do_qcl_gate (CNot x ctrl) = qcl_cnot x ctrl
do_qcl_gate (XCNot x ctrl) = qcl_cnot_inv x ctrl         
do_qcl_gate (Fanout a b c) = qcl_fanout a b c            
do_qcl_gate (XFanout a b c) = qcl_fanout_inv a b c            
do_qcl_gate (Matrix n amps regs) = qcl_matrix False n amps regs
do_qcl_gate (XMatrix n amps regs) = qcl_matrix True n amps regs

-- ----------------------------------------------------------------------
-- * Parsing

-- $ The output of QCL consists of lines of the following forms. Lines
-- not starting with \"\@\" are comments or other non-circuit output.
-- 
-- > @ RESET
-- > @ NOT(qureg q=<5>)  
-- > @ CNOT(qureg q=<31>,quconst c=<4,30>)
-- > @ !CNOT(qureg q=<31>,quconst c=<4,30>)
-- > @ Fanout(quconst a=<47,48,49,50,51,52>,quvoid b=<40,41,42,43,44,45>;cond=<>)
-- > @ !Fanout(quconst a=<47,48,49,50,51,52>,quvoid b=<40,41,42,43,44,45>;cond=<>)
-- > @ Matrix4x4(complex u00=1,complex u01=0,complex u02=0,complex u03=0,complex u10=0,complex u11=1,complex u12=0,complex u13=0,complex u20=0,complex u21=0,complex u22=(0.995004,-0.0998334),complex u23=0,complex u30=0,complex u31=0,complex u32=0,complex u33=(0.995004,0.0998334),qureg q=<12,13>)
-- > @ !Matrix4x4(complex u00=1,complex u01=0,complex u02=0,complex u03=0,complex u10=0,complex u11=0.707107,complex u12=0.707107,complex u13=0,complex u20=0,complex u21=0.707107,complex u22=-0.707107,complex u23=0,complex u30=0,complex u31=0,complex u32=0,complex u33=1,qureg q=<0,6>)  
-- 
-- We use Koen Claessen's parser combinators (see
-- "Text.ParserCombinators.ReadP") to implement the parser.

-- | Parse a QCL identifier, which we take to be a non-empty string of
-- alphanumeric characters, starting with a letter
identifier :: ReadP String
identifier = do
  satisfy isAlpha
  munch isAlphaNum
  
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
      
-- | Parse a comma separated list.
commalist :: ReadP a -> ReadP [a]
commalist elt = sepBy elt (skipSpaces >> char ',' >> skipSpaces)

-- | Parse a QCL quantum register of the form 
-- 
-- > q=<31,32>
-- > c=<4,31>
-- > b=<40,41,42,43,44,45>.
qureg :: ReadP (String, [Int])
qureg = do
  id <- identifier
  skipSpaces
  char '='
  skipSpaces
  rs <- between (char '<' >> skipSpaces) (skipSpaces >> char '>') $ do
    commalist int
  return (id, rs)

-- | Consume an optional \"!\". Return 'True' if consumed, and 'False'
-- otherwise.
inversechar :: ReadP Bool  
inversechar = do
  c <- option '+' (char '!')
  return (c == '!')

-- | Parse a complex number declaration of the format
-- 
-- > complex u00=1
-- 
-- or
-- 
-- > complex u22=(0.995004,-0.0998334).
complex :: ReadP (Complex Double)
complex = do
  string "complex"
  skipSpaces
  identifier
  skipSpaces
  char '='
  skipSpaces
  choice [
    do 
      x <- double
      return (x :+ 0)
    ,
    do
      char '('
      skipSpaces
      x <- double  
      skipSpaces
      char ','
      skipSpaces
      y <- double
      skipSpaces
      char ')'
      return (x :+ y)
    ]

-- | Parse a single line of QCL output into a 'QCLGate'.
qcl_line :: ReadP QCLGate
qcl_line = choice [
  do -- @ RESET
    char '@'
    skipSpaces
    string "RESET"
    return Reset
  ,
  do -- @ NOT(qureg q=<5>)
    char '@'
    skipSpaces
    inv <- inversechar
    skipSpaces
    string "NOT"
    skipSpaces
    char '('
    skipSpaces
    string "qureg"
    skipSpaces
    (_,[r]) <- qureg
    skipSpaces
    char ')'
    return (if inv then XNot r else Not r)
  ,
  do -- @ CNOT(qureg q=<31>,quconst c=<4,30>)
    char '@'
    skipSpaces
    inv <- inversechar
    skipSpaces
    string "CNOT"
    skipSpaces
    char '('
    skipSpaces    
    string "qureg"
    skipSpaces
    (_,[r]) <- qureg
    skipSpaces
    char ','
    skipSpaces
    string "quconst"
    skipSpaces
    (_,ctrls) <- qureg
    skipSpaces
    char ')'
    return (if inv then XCNot r ctrls else CNot r ctrls)
  ,
  do -- @ Fanout(quconst a=<47,48>,quvoid b=<40,41>;cond=<>)
    char '@'
    skipSpaces
    inv <- inversechar
    skipSpaces
    string "Fanout"
    skipSpaces
    char '('
    skipSpaces    
    string "quconst"
    skipSpaces
    (_,ins) <- qureg
    skipSpaces
    char ','
    skipSpaces
    string "quvoid"
    skipSpaces
    (_,outs) <- qureg
    skipSpaces
    char ';'
    skipSpaces
    (_,ctrls) <- qureg
    skipSpaces
    char ')'
    return (if inv then XFanout ins outs ctrls else Fanout ins outs ctrls)
  ,
  do -- @ Matrix4x4(complex u00=1,complex u01=0,complex u02=0,complex u03=0,complex u10=0,complex u11=1,complex u12=0,complex u13=0,complex u20=0,complex u21=0,complex u22=(0.995004,-0.0998334),complex u23=0,complex u30=0,complex u31=0,complex u32=0,complex u33=(0.995004,0.0998334),qureg q=<12,13>)
    char '@'
    skipSpaces
    inv <- inversechar
    skipSpaces
    string "Matrix"
    skipSpaces
    dim1 <- int
    skipSpaces
    char 'x'
    skipSpaces
    dim2 <- int
    skipSpaces
    char '('
    skipSpaces
    amps <- commalist complex
    skipSpaces
    char ','
    skipSpaces
    string "qureg"
    skipSpaces
    (_,r) <- qureg
    skipSpaces
    char ')'
    when (dim1 /= dim2) $ do
      error "Non-square matrix"
    return (if inv then XMatrix dim1 amps r else Matrix dim1 amps r)
  ,    
  do -- any line not starting with '@' is a comment
    satisfy ((/=) '@')
    munch (\x -> True)
    return Comment
  ,
  do -- empty lines are comments
    eof
    return Comment
  ]

-- | String version of 'qcl_line': parse a string and turn it into a
-- 'QCLGate'.
parse_qcl_line :: String -> QCLGate
parse_qcl_line s =
  case readP_to_S readline s of
    (h, _):_ -> h
    _ -> error ("Unrecognized line: " ++ s)
  where
    readline = do
      skipSpaces
      l <- qcl_line
      skipSpaces
      eof
      return l      
      
-- | Monad version of 'parse_qcl_line': parse a string and execute the
-- resulting gate directly in the 'QCLCirc' monad.
run_qcl_line :: String -> QCLCirc ()
run_qcl_line = do_qcl_gate . parse_qcl_line

-- | Parse a stream consisting of many lines of QCL output and execute
-- the parsed gates in the 'QCLCirc' monad.
run_qcl_lines :: String -> QCLCirc ()
run_qcl_lines s =
  mapM_ run_qcl_line (lines s)

-- | A sample circuit to illustrate the parser.
testcircuit2 :: QCLCirc ()
testcircuit2 = do
  run_qcl_line "@ RESET"
  run_qcl_line "@ NOT(qureg q=<5>)"
  run_qcl_line "@ NOT(qureg q=<0>)"
  run_qcl_line "@ CNOT(qureg q=<31>,quconst c=<4>)"

-- ----------------------------------------------------------------------
-- * Main function

-- | Main function: read a circuit in QCL format from 'stdin', and
-- preview the translated Quipper circuit.
main :: IO ()
main = do
  lines <- hGetContents stdin
  print_simple Preview (run (run_qcl_lines lines))

