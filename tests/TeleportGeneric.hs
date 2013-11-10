-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

import Quipper
import QuipperLib.Simulation

import System.Random
import System.Environment
import System.CPUTime

plus_minus :: (QShape a qa ca) => a -> Circ qa
plus_minus a = do 
    qs <- qinit a
    qs <- mapUnary hadamard qs
    return qs

share :: (QShape a qa ca) => qa -> Circ (qa, qa)
share qa = do 
    qb <- qinit (qc_false qa)
    (qb, qa) <- mapBinary controlled_not qb qa
    return (qa, qb)

bell00 :: (QShape a qa ca) => a -> Circ (qa, qa)
bell00 shape = do 
    qa <- plus_minus shape
    (qa, qb) <- share qa
    return (qa, qb)

alice :: (QShape a qa ca) => qa -> qa -> Circ (ca,ca)
alice q a = do 
    (a, q) <- mapBinary controlled_not a q
    q <- mapUnary hadamard q
    (x,y) <- measure (q,a)
    return (x,y)

bob :: (QShape a qa ca) => qa -> (ca,ca) -> Circ qa
bob b (x,y) = do
     (b, y) <- mapBinary_c controlled_X b y
     (b, x) <- mapBinary_c controlled_Z b x
     cdiscard (x,y)
     return b
  where
    controlled_X b x = do
      gate_X b `controlled` x
      return (b,x)
    
    controlled_Z b x = do
      gate_Z b `controlled` x
      return (b,x)
    
teleport :: (QData qa) => qa -> Circ qa
teleport q = do
    (a,b) <- bell00 (qc_false q)
    (x,y) <- alice q a
    b <- bob b (x,y)
    return b

teleport_labeled :: (QData qa) => qa -> Circ qa
teleport_labeled q = do
    comment_with_label "ENTER: teleport_labeled" q "q"
    comment "ENTER: bell00"
    (a,b) <- bell00 (qc_false q)
    comment_with_label "EXIT: bell00" (a,b) ("a","b")
    comment "ENTER: alice"
    (x,y) <- alice q a
    comment_with_label "EXIT: alice" (x,y) ("x","y")
    comment "ENTER: bob"
    b <- bob b (x,y)
    comment_with_label "EXIT: bob" b "b"
    comment "EXIT: teleport_labeled"
    return b

-- | A test that should help see how many qubits we can simulate
test_teleport :: [Bool] -> IO [Bool]
test_teleport = run_clifford_generic teleport

data What = Sim | Circ | Usage deriving Eq

-- | The main method deals with command line arguments, and timing of the simulation
main :: IO ()
main = do
  args <- getArgs
  if (length args /= 2) then usage else do
  let arg1 = head args
  let flag = case arg1 of
              "--sim" -> Sim
              "--circ" -> Circ 
              _ -> Usage
  if (flag == Usage) then usage else do 
   let arg = head (tail args)
   case reads arg of
    [(n,_)] -> do
     if (n < 0) then usage else do
     if (flag == Circ) then print_generic Preview teleport_labeled (replicate n qubit) else do
     input <- randomBools n
     putStrLn ("Input: " ++ show input)
     start <- getCPUTime
     output <- test_teleport input
     end <- getCPUTime
     putStrLn ("Output: " ++ show output)
     let time = end - start
     putStrLn ("Time: (" ++ show time ++ ")")
     show_time time
    _ -> usage

-- | Produce the given number of random boolean values
randomBools :: Int -> IO [Bool]
randomBools 0 = return []
randomBools n = do
  b <- randomIO
  bs <- randomBools (n-1)
  return (b:bs)

-- | Give a usage message if not being run from GHCI
usage :: IO ()
usage = do
  name <- getProgName
  if name == "<interactive>" then prompt else do
  putStrLn ("usage: " ++ name ++ " flag num_qubits")
  putStrLn ("  where flag = --sim or --circ") 

-- | If we're in GHCI then we can prompt for the number of qubits to teleport
prompt :: IO ()
prompt = do
  putStrLn "Enter flag (--sim or --circ): "
  f <- getLine
  putStrLn "Enter number of qubits: "
  n <- getLine
  withArgs [f,n] main      

-- | Display an integer representing pico-seconds in a more readable format
show_time :: Integer -> IO ()
show_time t = case range t of
  Pico -> putStrLn (show t ++ " " ++ show Pico ++ ".")
  r -> do
   putStr (show (div t (ps' r)) ++ " " ++ show r ++ ", ")
   show_time (rem t (ps' r))

-- | Helper data-type for show_time function
data Range = Pico | Nano | Micro | Milli | Seconds | Minutes | Hours | Days
 deriving Eq

instance Show Range where
 show Pico = "picoseconds"
 show Nano = "nanoseconds"
 show Micro = "microseconds"
 show Milli = "milliseconds"
 show Seconds = "seconds"
 show Minutes = "minutes"
 show Hours = "hours"
 show Days = "days"

-- | Helper function for show_time function
ps' :: Range -> Integer
ps' Pico = 1
ps' Nano = 10^3 * ps' Pico
ps' Micro = 10^3 * ps' Nano
ps' Milli = 10^3 * ps' Micro
ps' Seconds = 10^3 * ps' Milli 
ps' Minutes = 60 * ps' Seconds
ps' Hours = 60 * ps' Minutes
ps' Days = 24 * ps' Hours

-- | Helper function for show_time function
range :: Integer -> Range
range t = 
  if (t < 10^3) then Pico else
  if (t < 10^6) then Nano else
  if (t < 10^9) then Micro else
  if (t < 10^12) then Milli else
  if (t < 60*(10^12)) then Seconds else
  if (t < 60*60*(10^12)) then Minutes else
  if (t < 24*60*60*(10^12)) then Hours else Days
