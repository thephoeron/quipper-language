-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS -fcontext-stack=50 #-}

-- | This module contains the Quipper implementation of the Quantum
-- Linear Systems Algorithm.
-- 
-- The algorithm estimates the radar cross section for a FEM
-- scattering problem by using amplitude estimation to calculate
-- probability amplitudes. 
-- 
-- The notations are based on the paper 
-- 
-- * B. D. Clader, B. C. Jacobs, C. R. Sprouse. Quantum algorithm to
-- calculate electromagnetic scattering cross
-- sections. <http://arxiv.org/abs/1301.2340>.
module Algorithms.QLS.QLS where

import Quipper

import QuipperLib.QFT
import QuipperLib.Arith
import QuipperLib.Decompose

import Data.Complex
import qualified Data.Map as Map

import qualified Algorithms.QLS.TemplateOracle as Template
import Algorithms.QLS.QDouble
import Algorithms.QLS.QSignedInt
import Algorithms.QLS.CircLiftingImport
import Algorithms.QLS.Utils

import Libraries.Auxiliary(boollist_of_int_bh)


-- | The type of 'oracle_A' input arguments during runtime.
type OracleARunTime = Double  -- ^Value resolution.
       -> Int                 -- ^Band.
       -> Bool                -- ^Argflag.
       -> ([Qubit],[Qubit],[Qubit])  -- ^(x=index,y+node,z+value).
       -> Circ ([Qubit],[Qubit],[Qubit])

-- | The type of 'oracle_b' and 'oracle_r' input arguments during runtime.
type OracleBRRunTime = Double  -- ^Magnitude resolution.
        -> Double              -- ^Phase resolution.
        -> ([Qubit],[Qubit],[Qubit]) -- ^(x=index,m+magnitude,p+phase).
        -> Circ ([Qubit],[Qubit],[Qubit])


-- | A type to encapsulate all three oracles.
data Oracle = Oracle {
  oracle_A :: RunTimeParam -> OracleARunTime,
  oracle_b :: RunTimeParam -> OracleBRRunTime,
  oracle_r :: RunTimeParam -> OracleBRRunTime
}


-- | A set of oracles using only blackboxes.
dummy_oracle :: Oracle
dummy_oracle = Oracle {
  oracle_A = \d r i b x -> named_gate "Oracle A" x,
  oracle_b = \d1 d2 r x -> named_gate "Oracle b" x,
  oracle_r = \d1 d2 r x -> named_gate "Oracle r" x
}



-- | A type to hold the runtime parameters.
data RunTimeParam = RT_param {
  k :: Double,       -- ^ Wave number.
  theta :: Double,   -- ^ Incident wave angle.
  phi :: Double,     -- ^ Direction of desired far field radiation pattern.
  e0 :: Double,      -- ^ Incident wave amplitude.
  lambda :: Double,  -- ^ Wavelength.
  xlength :: Double, -- ^ /x/-length of square scattering region.
  ylength :: Double, -- ^ /y/-length of square scattering region.

  scatteringnodes :: [(Int,Int)], -- ^ Metallic region.
  
  nx :: Int,
  ny :: Int,
  lx :: Double,
  ly :: Double,

  kappa :: Double,
  epsilon :: Double,
  t0 :: Double,
  r :: Double,
  b_max :: Double,
  r_max :: Double,
  d  :: Int,
  nb :: Int,
  p2 :: Double,
  n0 :: Int,
  n1 :: Int,
  n2 :: Int,
  n4 :: Int,

  -- argflags for oracle_A
  magnitudeArgflag :: Bool,
  phaseArgflag :: Bool
} deriving (Show)


-- | A convenient set of runtime parameters for testing. 
dummy_RT_param :: RunTimeParam
dummy_RT_param = RT_param {

  k = 2.0*pi*1.0,
  theta = 0.0*pi/4.0,
  phi = 0.0,
  e0 = 1.0,
  lambda = (k dummy_RT_param)/(2.0*pi),
  xlength = 2.0*(lambda dummy_RT_param),
  ylength = 2.0*(lambda dummy_RT_param),
  
  scatteringnodes = 
    let rt = dummy_RT_param in
    let xul = round((fromIntegral $ nx rt)/2)
              - round((xlength rt)/(2.0*(lx rt))) in -- Upper left x index
    let yul = round((fromIntegral $ ny rt)/2)
              - round((ylength rt)/(2.0*(ly rt))) in -- Upper left y index
    let xlr = round((fromIntegral $ nx rt)/2)
              + round((xlength rt)/(2.0*(lx rt))) in  -- Lower right x index
    let ylr = round((fromIntegral $ ny rt)/2)
              + round((ylength rt)/(2.0*(ly rt))) in -- Lower right y in
      [(xul, yul), (xlr, ylr)],

  nx = 12885,
  ny = 12885,
  lx = 0.1,
  ly = 0.1,

  kappa = 1.0,
  epsilon = 1.0,
  t0 = 1.0,
  r = 1.0,
  b_max = 1.0,
  r_max = 1.0,
  d  = 3,
  nb = 2,
  p2 = 3,
  n0 = 3, 
  n1 = 3,
  n2 = 3,
  n4 = 3, 

  -- argflags for oracle_A
  magnitudeArgflag = False,
  phaseArgflag = True
}


-- | A set of larger values, for testing scalability.
large_RT_param :: RunTimeParam
large_RT_param = RT_param {

  k = 2.0*pi*1.0,
  theta = 0.0*pi/4.0,
  phi = 0.0,
  e0 = 1.0,
  lambda = (k large_RT_param)/(2.0*pi),
  xlength = 2.0*(lambda large_RT_param),
  ylength = 2.0*(lambda large_RT_param),
  
  scatteringnodes = 
    let rt = large_RT_param in
    let xul = round((fromIntegral $ nx rt)/2)
              - round((xlength rt)/(2.0*(lx rt))) in -- Upper left x index
    let yul = round((fromIntegral $ ny rt)/2)
              - round((ylength rt)/(2.0*(ly rt))) in -- Upper left y index
    let xlr = round((fromIntegral $ nx rt)/2)
              + round((xlength rt)/(2.0*(lx rt))) in  -- Lower right x index
    let ylr = round((fromIntegral $ ny rt)/2)
              + round((ylength rt)/(2.0*(ly rt))) in -- Lower right y in
      [(xul, yul), (xlr, ylr)],

  nx = 12885,
  ny = 12885,
  lx = 0.1,
  ly = 0.1,

  kappa = 1e4,
  epsilon = 0.01,
  t0 = 7.0e6,
  r = 2.5e12,
  b_max = 5.0,
  r_max = 1.01,
  d  = 7,
  nb = 9,
  p2 = (  1.0 / (4-(4**(1/3)))  ),
  n0 = 14,
  n1 = 24,
  n2 = 30,
  n4 = 65, 

  -- argflags for oracle_A
  magnitudeArgflag = False,
  phaseArgflag = True
}


-- | A set of smaller values, for manageable yet meaningful output.
small_RT_param :: RunTimeParam
small_RT_param = RT_param {

  k = 2.0*pi*1.0,
  theta = 0.0*pi/4.0,
  phi = 0.0,
  e0 = 1.0,
  lambda = (k small_RT_param)/(2.0*pi),
  xlength = 2.0*(lambda small_RT_param),
  ylength = 2.0*(lambda small_RT_param),
  
  scatteringnodes = 
    let xul = 2 in
    let yul = 2 in
    let xlr = 3 in
    let ylr = 3 in
      [(xul, yul), (xlr, ylr)],

  nx = 4,
  ny = 4,
  lx = 0.1,
  ly = 0.1,

  kappa = 1e4,
  epsilon = 0.01,
  t0 = 7.0e6,
  r = 2.5e12,
  b_max = 5.0,
  r_max = 1.01,
  d  = 7,
  nb = 9,
  p2 = (  1.0 / (4-(4**(1/3)))  ),
  n0 = 14,
  n1 = 24,
  n2 = 6,
  n4 = 65, 

  -- argflags for oracle_A
  magnitudeArgflag = False,
  phaseArgflag = True
}



-- | Apply an [exp −/iYt/] gate. The timestep /t/ is a parameter.
expYt :: Timestep -> Qubit -> Circ Qubit
expYt = named_rotation "exp(-i%Y)"


-- | Apply an [exp −/iYt/] gate. The timestep /t/ is a parameter.
expYt_at :: Timestep -> Qubit -> Circ ()
expYt_at = named_rotation_at "exp(-i%Y)"


-- | Read a list of bits and make it into a 'Double', by multiplying
-- its integer value by the provided factor.
dynamic_lift_double :: Double -> [Bit] -> Circ Double
dynamic_lift_double factor cl = do
      cdiscard cl

-- Implementation note: removed dynamic_lift as for now it breaks all
-- output formats except ASCII.

--      bl <- dynamic_lift cl
      let sign = 1 -- if (head $ reverse bl) then 1 else -1
      let unsigned_value = 1 -- integer_of_intm_unsigned $ 
                              -- intm_of_boollist_bh (tail $ reverse bl)
      return (sign * factor * (fromIntegral unsigned_value))


-- | A black box gate to stand in as a replacement for QFT.
qft_for_show :: [Qubit] -> Circ [Qubit]
qft_for_show qs = named_gate "QFT" qs



-- | Main function: for estimating the radar cross section for a FEM
-- scattering problem. The problem can be reduced to the calculation
-- of four angles: φ[sub /b/], φ[sub /bx/], φ[sub /r/1] and φ[sub /r/0].
qlsa_FEM_main :: RunTimeParam -> Oracle -> Circ Double
qlsa_FEM_main param oracle = do
     comment "FEM_main"
     phi_b  <- qlsa_AmpEst_phi_b param oracle
     phi_bx <- qlsa_AmpEst_phi_bx param oracle
     phi_r1 <- qlsa_AmpEst_phi_bxr param oracle True
     phi_r0 <- qlsa_AmpEst_phi_bxr param oracle False
     let sigma = ((((fromIntegral $ nb param) ^ 2) * ((b_max param) ^ 2) * ((r_max param) ^ 2) * ((sin phi_b) ^ 2)) / ( 4 * pi))
     comment "FEM_main"
     return sigma




-- * Amplitude Estimation Functions

-- | Estimates φ[sub /b/], related to the probability of success for the
-- preparation of the known state /b/, using amplitude amplification.
qlsa_AmpEst_phi_b :: RunTimeParam -> Oracle -> Circ Double
qlsa_AmpEst_phi_b param oracle = do
    g <- qinit $ replicate (n0 param) False
    with_ancilla_init (replicate (n2 param) False) $ \x -> do
       label (g,x) ("g","x")
       with_ancilla $ \a -> do
           label (a) ("anc. a")
           with_ancilla $ \b -> do
               label (b) ("anc. b")
               g <- map_hadamard g  
               u_b (x,b)  
               loop g u_g (x,b,a)
               return ()
           return ()
    g' <- qft_big_endian g -- QFT : Is it really big-endian?
    value_bits  <- measure g'
    value_double <- dynamic_lift_double 1.0 value_bits
    return (pi * value_double / (2 ** (fromIntegral $ n0 param)))    
    where
        loop :: [Qubit] -> (a -> Circ ()) -> a -> Circ ()
        loop [] f x = return ()
        loop (h:t) f x = do
            f x `controlled` h
            loop t f' x;
            where
               f' x = do f x; f x 

        u_b :: ([Qubit],Qubit) -> Circ ()
        u_b xb = qlsa_StatePrep param xb (oracle_b oracle param) (1.0/(b_max param))


        u_g :: ([Qubit],Qubit,Qubit) -> Circ ()
        u_g (x,b,a) = do 
            comment "U_g starts"
            gate_Z_at b
            -- For unitrary linear transformation, adjoint == inverse, hence reverse_...
            (reverse_generic_imp u_b) (x,b) 
            qnot_at a `controlled` x .==. (map (\x -> False) x)
            gate_X_at a
            gate_Z_at a
            gate_X_at a
            qnot_at a `controlled` x .==. (map (\x -> False) x)
            u_b (x,b)
            comment "U_g ends"
            return ()

        
            
-- | Testing function for 'qlsa_AmpEst_phi_b'.
test_qlsa_AmpEst_phi_b :: Bool -> IO ()
test_qlsa_AmpEst_phi_b dummyRTParamFlag = do
    let param = if dummyRTParamFlag then dummy_RT_param else large_RT_param 
    print_simple GateCount (qlsa_AmpEst_phi_b param dummy_oracle)
    print_simple Preview (qlsa_AmpEst_phi_b param dummy_oracle)


-- | Estimates φ[sub /bx/], related to the probability of success in
-- computing solution value /x/.
qlsa_AmpEst_phi_bx :: RunTimeParam -> Oracle -> Circ Double
qlsa_AmpEst_phi_bx param oracle  = do
    g <- qinit (take (n0 param) (repeat False))
    with_ancilla_init (take (n2 param) (repeat False)) $ \x -> do
      with_ancilla $ \a -> do 
          with_ancilla $ \b -> do
              with_ancilla $ \s -> do
                  g <- map_hadamard g    
                  u_bx (x,b,s)
                  loop g u_g (x,b,s,a)
                  return ()
              return () 
          return ()
    g' <- qft_big_endian g -- QFT : Is it really big-endian?
    value_bits  <- measure g'
    value_double <- dynamic_lift_double 1.0 value_bits
    return (pi * value_double / (2 ** (fromIntegral $ n0 param)))
    where
        loop :: [Qubit] -> (a -> Circ ()) -> a -> Circ ()
        loop [] f x = return ()
        loop (h:t) f x = do
            f x `controlled` h
            loop t f' x
            where
            f' x = do f x; f x
         
        u_bx :: ([Qubit],Qubit,Qubit) -> Circ ()
        u_bx (x,b,s) = do 
            qlsa_StatePrep param (x,b) (oracle_b oracle param) (1.0/(b_max param)) 
            qlsa_Solve_x param (x,s) oracle
            return ()

        u_g :: ([Qubit],Qubit,Qubit,Qubit) -> Circ ()
        u_g (x,b,s,a) = do --named_gate_at "Ug_phi_bx" (x,b,s,a)
            qnot_at a `controlled` b .&&. s
            gate_Z_at a
            qnot_at a `controlled` b .&&. s
            (reverse_generic_imp u_bx) (x,b,s)
            qnot_at a `controlled` [ q .==. 0 | q <- x ] .&&. b .==. 0 .&&. s .==. 0
            gate_X_at a
            gate_Z_at a
            gate_X_at a
            qnot_at a `controlled` [ q .==. 0 | q <- x ] .&&. b .==. 0 .&&. s .==. 0
            u_bx (x,b,s)
            return ()
        

        
       
-- | Estimates φ[sub /r/0] and φ[sub /r/1] (depending on the boolean
-- parameter), related to the overlap of the solution with the
-- arbitrary state /r/.
qlsa_AmpEst_phi_bxr :: RunTimeParam -> Oracle -> Bool -> Circ Double
qlsa_AmpEst_phi_bxr param oracle target = do
    g <- qinit (take (n0 param) (repeat False))
    with_ancilla_init (take (n2 param) (repeat False)) $ \x -> do
      with_ancilla_init (take (n2 param) (repeat False)) $ \y -> do 
        with_ancilla $ \a -> do 
          with_ancilla $ \b -> do
             with_ancilla $ \s -> do
                with_ancilla $ \r -> do 
                    with_ancilla $ \c -> do
                        g <- map_hadamard g    
                        u_r (x,y,b,s,r,c)
                        loop g u_g (x,y,b,s,r,c,a)
                        return ()
                    return ()
                return ()
             return ()
          return ()   
    g' <- qft_big_endian g -- QFT : Is it really big-endian?
    value_bits  <- measure g'
    value_double <- dynamic_lift_double 1.0 value_bits
    return (pi * value_double / (2 ** (fromIntegral $ n0 param)))
    where
    loop :: [Qubit] -> (a -> Circ ()) -> a -> Circ ()
    loop [] f x = return ()
    loop (h:t) f x = do
       f x `controlled` h
       loop t f' x
       where
         f' x = do f x; f x
         
    u_r :: ([Qubit],[Qubit],Qubit,Qubit,Qubit,Qubit) -> Circ ()
    u_r (x,y,b,s,r,c) = do 
        qlsa_Solve_xr param (x,y,b,s,r,c) oracle
        return ()

    u_g :: ([Qubit],[Qubit],Qubit,Qubit,Qubit,Qubit,Qubit) -> Circ ()
    u_g (x,y,b,s,r,c,a) = do --named_gate_at "Ug_phi_bxr" (x,y,b,s,r,c,a)
         qnot_at a `controlled` (b .==. 1 .&&. s .==. 1 .&&. r .==. 1 .&&. c .==. target)
         gate_Z_at a
         qnot_at a `controlled` (b .==. 1 .&&. s .==. 1 .&&. r .==. 1 .&&. c .==. target)
         (reverse_generic_imp u_r) (x,y,b,s,r,c)
         qnot_at a `controlled` [ q .==. 0 | q <- x ] .&&. [ q .==. 0 | q <- y ] .&&. b .==. 0 .&&. s .==. 0 .&&. r .==. 0 .&&. c .==. 0
         gate_X_at a
         gate_Z_at a
         gate_X_at a
         qnot_at a `controlled` [ q .==. 0 | q <- x ] .&&. [ q .==. 0 | q <- y ] .&&. b .==. 0 .&&. s .==. 0 .&&. r .==. 0 .&&. c .==. 0
         u_r (x,y,b,s,r,c)
         return ()


-- * State Preparation.

-- | Prepares a quantum state /x/, as specified by an oracle function,
-- entangled with a single qubit flag /q/ marking the desired state.
qlsa_StatePrep :: 
    RunTimeParam
    -> ([Qubit], Qubit) -- x & qare handles to wires to be changed by StatePrep 
    -> OracleBRRunTime -- Common type of (oracle_b oracle) and (oracle_r oracle), if oracle is typed Oracle
    -> Double
    -> Circ ()
qlsa_StatePrep param (x, q) oracle phi0 = do
  _ <- (flip $ box ("qlsa_StatePrep_" ++ (show phi0))) (x,q) $ \(x,q) -> do
    -- comment "StatePrep starts"
    label (x,q) ("x", "q")
    with_ancilla_list (n4 param) $ \m -> do
        label (m) ("anc. m")
        with_ancilla_list (n4 param) $ \p -> do
            label (p) ("anc. p")
            x <- map_hadamard x
            (x, m, p) <- oracle phi0 (epsilon param) (x, m, p)
            qlsa_ControlledPhase p (epsilon param) False
            qlsa_ControlledRotation (m, q) phi0 False
            (x, m, p) <- oracle phi0 (epsilon param) (x, m, p)
            return (x,q)
    -- comment "StatePrep ends"
  return ()


-- | Testing function for 'qlsa_StatePrep'.
test_qlsa_StatePrep :: Bool -> IO ()
test_qlsa_StatePrep dummyRTParamFlag = do
          let param = if dummyRTParamFlag then dummy_RT_param else large_RT_param
          let oraclebRunTime = (oracle_b dummy_oracle param)  
          let testCirc = do
              x <- qinit $ replicate (n2 param) False
              q <- qinit False
              qlsa_StatePrep param (x,q) oraclebRunTime 1.0
          print_simple GateCount testCirc
          print_simple Preview testCirc




-- * Linear System Solver Functions

-- | Implements the QLSA procedure to generate the solution state |/x/〉.
qlsa_Solve_x :: RunTimeParam ->([Qubit],Qubit) -> Oracle -> Circ ()   
qlsa_Solve_x param (x,s) oracle = do
  _ <- (flip $ box "qlsa_Solve_x") (x,s) $ \(x,s) -> do
    with_ancilla_list (n1 param) $ \t -> do 
        with_ancilla_list (length t) $ \f -> do 
            let phi0 = 2 * pi  / (2 ** (fromIntegral $ n1 param) - (epsilon param))
            t <- map_hadamard t
            u_hs (t,x)
            t <- qft_big_endian t
            integer_inverse (t,f) 
            qlsa_ControlledRotation (f,s) phi0 False
            integer_inverse (t,f)
            (reverse_generic_endo qft_big_endian) t
            (reverse_generic_imp u_hs) (t,x)
            t <- map_hadamard t
            return()  
        return ()
    return (x,s)
  return ()
    where
        u_hs :: ([Qubit],[Qubit]) -> Circ ()
        u_hs (t,x) = do 
            qlsa_HamiltonianSimulation param (t,x) (oracle_A oracle param)
            return ()
            

-- | Implementation of the integer division. The two registers are
-- supposed to be of the same size and represent little-headian
-- unsigned integers, i.e., the head of the list holds the least
-- significant bit.
integer_inverse :: ([Qubit],[Qubit]) -> Circ ()
integer_inverse (t,f) = do
  _ <- (flip $ box "integer_inverse") (t,f) $ \(t,f) -> do
    -- sanity check
    if (length t /= length f) 
      then error "integer_inverse: registers of distinct sizes" 
      else return ()
    -- initialize an unsigned integer to 2^(length t) - 1
    with_ancilla_init (map (\_ -> True) t) $ \num -> do
      -- perform the division (encapsulated in a subroutine)
      let d = classical_to_reversible $ \(t,num) -> do
                let x = ((qdint_of_qulist_lh num),(qdint_of_qulist_lh t))
                (_,_,f') <- uncurry q_div_unsigned x
                return $ qulist_of_qdint_lh f'
      d ((t,num),f)
      return (t,f)
  return ()




            
-- | Implements the complete QLSA procedure to find the
-- solution state |/x/〉 and then implements the swap protocol
-- required for estimation of 〈/x/|/r/〉.
qlsa_Solve_xr :: RunTimeParam ->([Qubit],[Qubit],Qubit,Qubit,Qubit,Qubit) -> Oracle -> Circ ()      
-- qlsa_Solve_xr param (x,y,b,s,r,c) oracle  = named_gate_at "Solve_xr" (x,y,b,s,r,c)
qlsa_Solve_xr param (x,y,b,s,r,c) oracle = do
  _ <- (flip $ box "qlsa_Solve_xr") (x,y,b,s,r,c) $ \(x,y,b,s,r,c) -> do
    qlsa_StatePrep param (x,b) (oracle_b oracle param) (1.0/(b_max param)) 
    qlsa_Solve_x param (x,s) oracle	
    qlsa_StatePrep param (y,r) (oracle_r oracle param) (1.0/(r_max param)) 
    hadamard_at c
    swap_at y x  `controlled` c
    hadamard_at c
    return (x,y,b,s,r,c)
  return ()
    

-- * Hamiltonian Simulation Functions.

-- | Uses a quantum register |/t/〉 to control the
-- implementation of the Suzuki method for simulating a Hamiltonian
-- specified by an oracle function.
qlsa_HamiltonianSimulation :: 
    RunTimeParam 
    -> ([Qubit], [Qubit])
    -> OracleARunTime 
    -> Circ ()
qlsa_HamiltonianSimulation param (t, x) oracleA = do
  _ <- (flip $ box "qlsa_HamiltonianSimulation") (t,x) $ \(t,x) -> do
    -- Code the first line in a way that depends on the length of t rather 
    -- explicitly on (n1 param) which is supposed to be the length of t
    -- Hence replaced the line below by the line after it.
    -- let denom = 2 * (r param) * (fromIntegral ((n1 param) - 1))
    let denom = 2 * (r param) * ( 2^((length t) - 1) )
    let t1 = (p2 param) * (t0 param) / denom
    let t2 = (1.0 - 4.0 * (p2 param)) * (t0 param) / denom
    (t,x) <- box_loopM  "TrotterLoop" (round $ r param) (t,x) (hs_loop t1 t2)
    return (t,x)
  return ()
    where 
          hs_loop :: Double -> Double -> ([Qubit], [Qubit]) -> Circ ([Qubit], [Qubit])
          hs_loop t1 t2 (t,x) = do 
            u_z_at (t,x) t1
            u_z_at (t,x) t1
            u_z_at (t,x) t2
            u_z_at (t,x) t1
            u_z_at (t,x) t1
            return (t,x)

          u_z_at :: ([Qubit], [Qubit]) -> Double -> Circ ()
          u_z_at (t, x) timeStep = do
              for (nb param) 1 (-1) $ \jj -> do
                  qlsa_HsimKernel param (t, x) jj timeStep oracleA 
                  endfor
              for 1 (nb param) 1 $ \jj -> do
                  qlsa_HsimKernel param (t, x) jj timeStep oracleA 
                  endfor
              return ()

-- | Testing function for 'qlsa_HamiltonianSimulation'.
test_qlsa_HamiltonianSimulation :: Bool -> IO ()
test_qlsa_HamiltonianSimulation dummyRTParamFlag = do
    let param = if dummyRTParamFlag then dummy_RT_param else large_RT_param
    let oracleARunTime = (oracle_A dummy_oracle param) 
    let testCirc = do
              t <- qinit (take (n0 param) (repeat False))
              x <- qinit (take (n4 param) (repeat False))
              label(t,x) ("t", "x")
              qlsa_HamiltonianSimulation param (t,x) oracleARunTime
    print_simple GateCount testCirc
--    print_simple Preview testCirc



-- | Uses an oracle function and timestep control register (/t/) to
-- apply 1-sparse Hamiltonian to the input state |/t/, /x/〉.
qlsa_HsimKernel :: 
    RunTimeParam
    -> ([Qubit], [Qubit]) 
    -> Int 
    -> Double 
    -> OracleARunTime
    -> Circ ()
-- qlsa_HsimKernel param tx band timeStep oracleA = named_gate_at "HsimKernel" tx

qlsa_HsimKernel param (t, x) band timeStep oracleA = do
  _ <- (flip $ box ("qlsa_HsimKernel" ++ (show band) ++ (show timeStep))) (t,x) $ \(t,x) -> do
    let phiP = (epsilon param)
    with_ancilla_list (n2 param) $ \y -> do
       with_ancilla_list (n4 param) $ \m -> do 
           with_ancilla_list (n4 param) $ \p -> do 
               label (y,m,p) ("y","m","p")
               -- phases
               oracleA phiP band (phaseArgflag param) (x,y,p)
               qlsa_ControlledPhase p phiP False
               oracleA phiP band (phaseArgflag param) (x,y,p)
               -- magnitudes
               let phiMag = 2 ** (negate $ fromIntegral $ after_radix_length)
               oracleA phiMag band (magnitudeArgflag param) (x,y,m)
               for 0 ((length t) - 1) 1 $ \ii -> do 
                   let phi_mt = timeStep * phiMag * (2^ii)
                   qlsa_ApplyHmag param (x,y,m) phi_mt `controlled` (t !! ii)
                   endfor
               oracleA phiMag band (magnitudeArgflag param) (x,y,m)
               -- phases again
               oracleA phiP band (phaseArgflag param) (x,y,p)
               qlsa_ControlledPhase p phiP True
               oracleA phiP band (phaseArgflag param) (x,y,p)
               return ()
           return ()
       return () 
    return (t,x)
  return ()

-- | Testing function for 'qlsa_HsimKernel'.
test_qlsa_HsimKernel :: Bool -> IO ()
test_qlsa_HsimKernel dummyRTParamFlag = do
    let param = if dummyRTParamFlag then dummy_RT_param else large_RT_param
    let oracleARunTime = (oracle_A dummy_oracle param) 
    let testCirc = do
              t <- qinit (take (n0 param) (repeat False))
              x <- qinit (take (n4 param) (repeat False))
              label(t,x) ("t", "x")
              qlsa_HsimKernel param (t,x) 1 0.1 oracleARunTime
    print_simple GateCount testCirc
--    print_simple Preview testCirc


-- | Applies the magnitude component of coupling elements in a
-- 1-sparse Hamiltonian.
qlsa_ApplyHmag :: RunTimeParam -> ([Qubit], [Qubit], [Qubit]) -> Double -> Circ ()
qlsa_ApplyHmag param (x,y,m) phi0 = do
  _ <- (flip $ box ("qlsa_ApplyHmag " ++ (show phi0))) (x,y,m) $ \(x,y,m) -> do
    let (onOne, onZero) = (True, False)
    with_ancilla $ \a -> do -- Assume initialized to False (0)
        label (a) ("anc. a")
        if (length x /= length y) 
           then error "qlsa_ApplyHmag: Input registers x and y have different lengths." 
           else return ()
        let length_xy = length x
        for 0 (length_xy - 1) 1 $ \ii -> do
            let (xi, yi) = (x !! ii, y !! ii)
            w (xi, yi)
            qnot_at a `controlled` (xi .==. onOne .&&. yi .==. onZero)
            endfor
        qlsa_ControlledPhase (m ++ [a]) phi0 False
        for (length_xy - 1) 0 (-1) $ \ii -> do
            let (xi, yi) = (x !! ii, y !! ii)
            qnot_at a `controlled` (xi .==. onOne .&&. yi .==. onZero)
            w (xi, yi)
            endfor 
        return ()
    return (x,y,m)
  return ()


-- | Testing function for 'qlsa_ApplyHmag'.
test_qlsa_ApplyHmag :: Bool -> IO ()
test_qlsa_ApplyHmag dummyRTParamFlag = do
    let param = if dummyRTParamFlag then dummy_RT_param else large_RT_param
    let testCirc = do
              x <- qinit (take (n2 param) (repeat False))
              y <- qinit (take (n2 param) (repeat False))
              m <- qinit (take (n4 param) (repeat False))
              label(x,y,m) ("x", "y", "m")
              qlsa_ApplyHmag param (x,y,m) 0.1 
    print_simple GateCount testCirc
    print_simple Preview testCirc





-- | Auxiliary function: the /W/-gate.
w :: (Qubit, Qubit) -> Circ ()
-- w xy = named_gate_at "W" xy
w (xi,yi) = do
  _ <- box "w" (\(xi, yi) -> do
    label (xi,yi) ("x[i]","y[i]")
    gate_X_at xi `controlled` yi
    gate_X_at yi `controlled` xi
    hadamard_at yi `controlled` xi
    gate_X_at yi `controlled` xi
    gate_X_at xi `controlled` yi
    return (xi,yi)) (xi,yi)
  return ()

-- | Testing function for 'w'.
test_w :: IO ()
test_w = do
    let testCirc = do
        xi <- qinit False    
        yi <- qinit False
        w (xi, yi)
    print_simple GateCount testCirc
    print_simple Preview testCirc


-- * Controlled Logic Operations


-- | Applies a phase shift of φ\/2 to the signed input register |φ〉.

-- For c, bit locations are counted starting from 0 (least significant) to (length c - 2) (most significant)
-- last c (or c !! (n-1)) is the sign bit
qlsa_ControlledPhase :: [Qubit] -> Double -> Bool -> Circ ()
-- qlsa_ControlledPhase c phi0 f = named_gate_at "CPhase" c
qlsa_ControlledPhase c phi0 f = do
  _ <- (flip $ box ("qlsa_ControlledPhase " ++ (show phi0) ++ " " ++ (show f))) c $ \c -> do
    with_ancilla $ \a -> do -- ancilla is initialized to False
        if f then (qnot_at a) else return ()
        let signQubit = last c
        qnot_at a `controlled` signQubit
        for 0 (length c - 2) 1 $ \ii -> do 
            let theta = ( (2.0^(ii)) * phi0 / 2.0) -- Note the divide by 2
            -- The following three lines are equivalent
            expZt_at theta a `controlled` (c !! ii)
            -- a <- expZt theta a `controlled` (c !! ii); return ()
            -- qlsa_ControlledU (c !! ii, a) (expZt theta) False    
            endfor
        qnot_at a `controlled` signQubit  
        return c
  return ()


-- | Applies a rotation of φ\/2 to the signed input register |φ〉.
qlsa_ControlledRotation :: ([Qubit], Qubit) -> Double -> Bool -> Circ ()
-- qlsa_ControlledRotation ct phi0 f = named_gate_at "CRotate" ct
qlsa_ControlledRotation (c, t) phi0 f = do
  _ <- (flip $ box ("qlsa_ControlledRotation " ++ (show phi0) ++ " " ++ (show f))) (c,t) $ \(c,t) -> do
    if f then (qnot_at t) else return ()
    let signQubit = last c
    qnot_at t `controlled` signQubit
    for 0 (length c - 2) 1 $ \ii -> do
        let theta = (2.0^(ii)) * phi0 / 2.0
        expYt_at theta t `controlled` (c !! ii)
        endfor
    qnot_at t `controlled` signQubit
    if f then (qnot_at t) else return ()
    return (c,t)
  return ()


----------------------------------------------------------------------
-- * Oracles

-- | Map a 'QDouble' into an integer, understood as being scaled by
-- the given factor. Take the factor and the size of the output
-- register as parameter.
make_factor_rep :: Double -> Int -> QDouble -> Circ [Qubit]
make_factor_rep factor size p = do
     -- number of high bits of p
     let p_int_size = (xdouble_length p) - (xdouble_exponent p)
     -- get the required number of bits for doing the encoding
     let auxsize = max (size - 1) p_int_size
     -- do the operation:
     --    (1) build a QDouble from the factor: need (size-1) bits of integer part
     qfactor <- qinit $ fdouble_of_double (xdouble_exponent p) 
                                          (auxsize + xdouble_exponent p) factor
     --    (2) scale p
     p_large <- qdouble_pad_to_extent (auxsize,- (xdouble_exponent p)) p
     --    (3) divide p by factor
     qreal_multiples <- unpack template_symb_slash_ p_large qfactor
     --    (4) get the floor of the result
     q_floor <- template_floor
     qmultiples <- q_floor qreal_multiples
     --    (5) set them in the right format (it has size elements)
     let (SInt tp bp) = qmultiples
     let new_p = (take (size - 1) $ reverse tp) ++ [bp]
     return new_p



-- | Implements the oracle for the arbitrary state |/r/〉, using the
-- Template Haskell implementation of 'calcRweights'.
inline_oracle_r :: RunTimeParam -> Double -> Double -> ([Qubit],[Qubit],[Qubit]) -> Circ ([Qubit],[Qubit],[Qubit])
inline_oracle_r rt factor_m factor_p =  box ("Or " ++ (show factor_m) ++ " " ++ (show factor_p)) $ decompose_generic Toffoli $ \(x',m',p') ->
    with_ancilla_init (fromIntegral $ nx rt :: FSignedInt) $ \qnx -> 
     with_ancilla_init (fromIntegral $ ny rt :: FSignedInt) $ \qny -> 
      with_ancilla_init (fdouble $ lx rt) $ \qlx ->
       with_ancilla_init (fdouble $ ly rt) $ \qly ->
        with_ancilla_init (fdouble $ k rt) $ \qk ->
         with_ancilla_init (fdouble $ theta rt) $ \qtheta ->
          with_ancilla_init (fdouble $ phi rt) $ \qphi -> 
                -- the x register is smaller than the size of a QSInt,
                -- and x is an unsigned integer: make up a positive
                -- sign and a pad
                
                with_ancilla_init False $ \bx -> do
                  with_ancilla_init (replicate (fixed_int_register_length - (n2 rt)) 
                                               False) $ \pad_x -> do
                    
                    let x = SInt (pad_x ++ (reverse x')) bx
                    let f = classical_to_reversible $ 
                              \(x,nx,ny,lx,ly,k,theta,phi) -> do 
                                 (m,p) <- unpack Template.template_calcRweights 
                                            x nx ny lx ly k theta phi
                                 new_p <- make_factor_rep factor_p (n4 rt) p
                                 new_m <- make_factor_rep factor_m (n4 rt) m
                                 return (new_m, new_p)
                    f ((x,qnx,qny,qlx,qly,qk,qtheta,qphi),(m',p'))
                    return (x',m',p')





-- | Implements the oracle for the known state |/b/〉, using the
-- Template Haskell implementation of 'getKnownWeights'.
inline_oracle_b :: RunTimeParam -> Double -> Double -> ([Qubit],[Qubit],[Qubit]) -> Circ ([Qubit],[Qubit],[Qubit])
inline_oracle_b rt factor_m factor_p = box ("Ob " ++ (show factor_m) ++ " " ++ (show factor_p)) $ decompose_generic Toffoli $ \(x',m',p') -> 
    -- Make ancillas for constant values
    
    with_ancilla_init (listpair_fmap fromIntegral $ scatteringnodes rt :: [(FDouble,FDouble)]) $ \qscatteringnodes ->
     with_ancilla_init (fromIntegral $ ny rt :: FSignedInt) $ \qny -> 
      with_ancilla_init (fdouble $ lx rt) $ \qlx ->
       with_ancilla_init (fdouble $ ly rt) $ \qly ->
        with_ancilla_init (fdouble $ k rt) $ \qk ->
         with_ancilla_init (fdouble $ theta rt) $ \qtheta ->
          with_ancilla_init (fdouble $ e0 rt) $ \qe0 ->
           with_ancilla_init (fromIntegral $ nx rt :: FSignedInt) $ \qnx -> do

                -- the x register is smaller than the size of a QSInt,
                -- and x is an unsigned integer: make up a positive
                -- sign and a pad
                
                with_ancilla_init False $ \bx -> do
                  with_ancilla_init (replicate (fixed_int_register_length - (n2 rt)) 
                                               False) $ \pad_x -> do
                    
                    let x = SInt (pad_x ++ (reverse x')) bx
                    
                    let f = classical_to_reversible $ 
                              \(y,nx,ny,scatteringnodes,lx,ly,k,theta,e0) -> do
                                  -- get some QSInt and QDouble
                                  (m,p) <- unpack Template.template_getKnownWeights 
                                              y nx ny scatteringnodes lx ly k theta e0 7
                                  new_p <- make_factor_rep factor_p (n4 rt) p
                                  new_m <- make_factor_rep factor_m (n4 rt) m
                                  
                                  return (new_m, new_p)
                                  
                    f ((x,qnx,qny,qscatteringnodes,qlx,qly,qk,qtheta,qe0),(m',p'))
                    return (x',m',p')


-- | Implementation of the oracle calculating the matrix /A/
-- corresponding to the discretization of the scattering problem,
-- using the Template Haskell implementation of
-- 'getNodeValuesMoreOutputs'.
inline_oracle_A ::  RunTimeParam -> Double -> Int -> Bool -> ([Qubit],[Qubit],[Qubit]) -> Circ ([Qubit],[Qubit],[Qubit])
inline_oracle_A rt factor band argflag =  box ("OA " ++ (show band) ++ " " ++ (show argflag)) $ decompose_generic Toffoli $ \(x',y',p') -> do

    let argflag' = if argflag then PTrue else PFalse
    
    -- Make ancillas for constant values
    
    with_ancilla_init (listpair_fmap fromIntegral $ scatteringnodes rt :: [(FDouble, FDouble)]) $ \qscatteringnodes -> 
      with_ancilla_init (fromIntegral $ ny rt :: FSignedInt) $ \qny -> 
        with_ancilla_init (fromRational $ toRational $ lx rt) $ \qlx ->
          with_ancilla_init (fromRational $ toRational $ ly rt) $ \qly ->
            with_ancilla_init (fromRational $ toRational $ k rt) $ \qk ->
             with_ancilla_init (fromIntegral $ nx rt :: FSignedInt) $ \qnx -> do

                -- the x register is smaller than the size of a QSInt,
                -- and x is an unsigned integer: make up a positive
                -- sign and a pad
                
                with_ancilla_init False $ \bx -> do
                  with_ancilla_init (replicate (fixed_int_register_length - (n2 rt))
                                               False) $ \pad_x -> do
                    
                    let x = SInt (pad_x ++ (reverse x')) bx
                    
                    let f = classical_to_reversible $ 
                              \(v,nx,ny,scatteringnodes,lx,ly,k) -> do
                               -- get some QSInt and QDouble
                               (y,p) <- unpack Template.template_getNodeValuesMoreOutputs
                                           v band nx ny scatteringnodes lx ly k argflag' 7
                               
                               new_p <- make_factor_rep factor (n4 rt) p 
                               
                               -- set y in the correct format (it has n2 elements)
                               -- we can assume that the sign is positive.
                               -- we also assume that n2 < size of QSInt register
                               let (SInt ty _) = y
                               let new_y = (take (n2 rt) $ reverse ty)
                               
                               -- return the values in the right format.
                               return (new_y,new_p)
                           
                    f ((x,qnx,qny,qscatteringnodes,qlx,qly,qk),(y',p'))
                    
                    return (x',y',p')
    

-- | Encapsulate the inline oracles in Template Haskell into an object
-- of type 'Oracle'.
inline_oracle :: Oracle
inline_oracle = Oracle {
  oracle_A = inline_oracle_A,
  oracle_b = inline_oracle_b,
  oracle_r = inline_oracle_r
}
