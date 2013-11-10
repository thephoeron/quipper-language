-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | A test file to simulate various decompositions of the simple oracle circuit,
-- from the BWT algorithm.

import Quipper
import QuipperLib.Simulation
import QuipperLib.Decompose

-- import other Quipper stuff
import Algorithms.BWT.Alternative
import Libraries.Auxiliary

-- | Extract the circuit from an oracle.
oracleCircuit :: Oracle -> Int -> Int -> Circ (Qubit,[Qubit])
oracleCircuit oracle color i = do
  input <- qinit (boollist_of_int_bh (m oracle) i)
  output <- qinit (boollist_of_int_bh (m oracle) 0)
  q <- qinit False
  oraclefun oracle color (input,output,q)
  return (q, output)
 			     
-- | Run the simple oracle with a given decomposition, and given inputs.
run_simple' :: GateBase -> Int -> Int -> IO (Bool,Int)
run_simple' gb color i = do (b,bs) <- run_generic_io (undefined :: Double) (decompose_generic gb (oracleCircuit oracle_simple color i))
                            return (b, int_of_boollist_unsigned_bh bs)

-- | Run the simple oracle  with a given decomposition, and given inputs, and print the result in a more readable manner.
run_simple :: GateBase -> Int -> Int -> IO ()
run_simple gb color i = do (b,bs) <- run_simple' gb color i
			   if not b 
			   then putStrLn (show i ++ " --( " ++ show color ++ " )--> " ++ show bs)
			   else return ()

-- | Run the simple oracle with a given decomposition, mapped over all possible inputs.
main_run' :: GateBase -> IO ()
main_run' gb = mapM_ (\(x,y) -> run_simple gb x y) [(x,y) | y <- [0..31], x <- [0..3]]

-- | Run each decomposition of the oracle circuit and print out the resulting edges.
main_run :: IO ()
main_run = do putStrLn "Logical"
	      main_run' Logical
	      putStrLn "Toffoli"
	      main_run' Toffoli
	      putStrLn "Binary"
	      main_run' Binary	

-- | Simumlate the simple oracle with a given decomposition, and given inputs.
sim_simple' :: GateBase -> Int -> Int -> ProbabilityDistribution Double (Bool,Int)
sim_simple' gb color i = do (b,bs) <- sim_generic undefined (decompose_generic gb (oracleCircuit oracle_simple color i))
                            return (b, int_of_boollist_unsigned_bh bs)

-- | Simulate the simple oracle with a given decomposition,
-- and given inputs, and print the result in a more readable manner.
sim_simple :: GateBase -> Int -> Int -> ProbabilityDistribution Double (IO ())
sim_simple gb color i = do (b,bs) <- sim_simple' gb color i
			   if not b 
			   then return $ putStr (show i ++ " --( " ++ show color ++ " )--> " ++ show bs)
			   else Vector [(return (),0.0)]

sequenceP :: ProbabilityDistribution Double (IO ()) -> IO ()
sequenceP (Vector []) = return ()
sequenceP (Vector ((io,prob):ps)) = do if prob /= 0.0 then do io
                                                              putStrLn (" - " ++ show prob)
                                                      else return ()
                                       sequenceP (Vector ps)  

-- | Simulate the simple oracle with a given decomposition, mapped over all possible inputs.
main_sim' :: GateBase -> IO ()
main_sim' gb = mapM_ (\(x,y) -> sequenceP (sim_simple gb x y)) [(x,y) | y <- [0..31], x <- [0..3]]

main_sim'' :: GateBase -> Int -> Int -> IO ()
main_sim'' gb x y = sequenceP (sim_simple gb x y)

-- | Simulate each decomposition of the oracle circuit and print out the resulting edges.
main_sim :: IO ()
main_sim = do putStrLn "Logical"
	      main_sim' Logical
	      putStrLn "Toffoli"
	      main_sim' Toffoli
	      putStrLn "Binary"
	      main_sim' Binary	

main :: IO ()
main = do main_run
	  main_sim

