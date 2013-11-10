-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module contains functions for reading the GSE one- and
-- two-electron integral data from a file, converting this data from
-- spatial to spin indices, and accessing the data.
-- 
-- The external interface consists of the type 'GSEData' and the
-- function 'load_gse_data'.
-- 
-- The Quipper distribution contains example data files
-- \"@h_1e_ascii@\" and \"@h_2e_ascii@\". These files contain enough
-- data for /M/ = 32 spin orbitals (corresponding to /M/\/2 = 16
-- spatial orbitals). Note that the example data was randomly
-- generated and is only a mock-up. In actual applications, physically
-- meaningful data should be substituted.

module Algorithms.GSE.GSEData where

import Data.Array
import Data.Bits
import Data.Char

-- * Data abstraction
  
-- | A data structure describing the GSE Data - the number
-- of integrals and the functions to access the data by index.
data GSEData = GSEData {
  
  -- | The number of spin orbitals /M/.
  gse_data_M :: Int,
  
  -- | 1-electron integrals /h/[sub p,q] in spin coordinates.
  gse_data_h1 :: (Int,Int) -> Double,
  
  -- | 2-electron integrals /h/[sub p,q,r,s] in spin coordinates.
  -- Follows the physics convention for the ordering of indices.
  gse_data_h2 :: (Int,Int,Int,Int) -> Double
  
  }

instance Show (GSEData) where
    show a = "GSEData { size = " ++ show (gse_data_M a) ++ " }"

-- ----------------------------------------------------------------------
-- * Reading GSE data from files

-- $ This section provides function for reading one- and two-electron
-- GSE data from files. The file formats are as follows. The file for
-- the one-electron data consists of lines of the form:
-- 
-- > ((i, j), h)
-- 
-- where /i/ and /j/ are integer indices in the range from /0/ to
-- /M/−1, and /h/ = /h/[sub i,j] is a real floating point number.
-- Please note that the file contains data for (/i/, /j/) and
-- (/j/, /i/), and that the indices /i/ and /j/ are in /spatial/
-- coordinates. The file data is sorted in order of increasing /i/,
-- then /j/.
-- 
-- The file for the two-electron data consists of lines of the form:
-- 
-- > ((i, j, k, l), h)
-- 
-- where /i/, /j/, /k/, and /l/ are integer indices in the range from
-- /0/ to /M/−1, and /h/ = /h/[sub i,k,l,j] is a real floating point
-- number. Please note that the indices /i/, /j/, /k/, and /l/ are in
-- /spatial/ coordinates, and the ordering of indices in the file
-- follows the /chemists'/ convention. Also, to save storage space,
-- the file only contains data for /i/ ≥ /j/, /k/ ≥ /l/, and either
-- /i/ > /k/, or /i/ = /k/ and /j/ ≥ /l/. The remaining data must be
-- inferred from symmetries. The file data is sorted in order of
-- increasing /i/, then /j/, then /k/, then /l/.
-- 
-- We also note that the data files, and the functions of this module
-- where noted, are the /only/ places where we use Chemists' notation
-- and spatial orbitals. The remainder of our implementation uses
-- physicists' notation and spin orbitals throughout.

-- | Read the 'GSEData' from two files. The first argument is /M/, the
-- number of spin orbitals. The second and third argument are the
-- filenames for the one-electron and two-electron data, respectively.
-- 
-- If the file contains data for more than /M/ spin orbitals, ignore
-- the excess data (this is useful for generating smaller problem
-- sizes for testing). In this case, only the necessary portion of the
-- file is read. If the file contains data for fewer than /M/ spin
-- orbitals, this is silently ignored, but will lead to an
-- \"undefined\" error later.
load_gse_data :: Int -> String -> String -> IO GSEData
load_gse_data size filename1 filename2 = do
  content1 <- readFile filename1
  content2 <- readFile filename2
  let spatial_size = (size + 1) `div` 2
  let spacial_data1 = parsefile1 spatial_size content1
  let spacial_data2 = parsefile2 spatial_size content2
  return (GSEData {
             gse_data_M = size,
             gse_data_h1 = spin1 $ access_1e spacial_data1,
             gse_data_h2 = spin2 $ access_2e spacial_data2
             })

-- ----------------------------------------------------------------------
-- * Low-level access functions

-- | Access 1-electron integral data. The indices are spatial, i.e.,
-- they run from 0 to /M/\/2 − 1.
access_1e :: Array (Int, Int) e -> (Int, Int) -> e
access_1e arr tuple = arr ! tuple

-- | Access 2-electron integral data. The input array is sparse (i.e.,
-- contains only one representative of each equivalence class), and
-- uses chemists' conventions. The output uses physicists'
-- conventions. The indices in both input and output are spatial,
-- i.e., they run from 0 to /M/\/2 − 1. 
access_2e :: Array (Int, Int, Int, Int) e -> (Int, Int, Int, Int) -> e
access_2e arr (i,k,l,j) = 
    -- The indices are not in correct order on purpose.  We 
    -- need to express the fact that h_prsq = h[pq|rs] = h[p,q,r,s] = h[i,j,k,l]
    arr ! (swap_ijkl $ swap_kl $ swap_ij (i,j,k,l))
	
    -- Note that because of symmetries, we have
	--   h2(i,j,k,l) = h2(j,i,k,l)
	--   h2(i,j,k,l) = h2(i,j,l,k)
	--   h2(i,j,k,l) = h2(k,l,i,j)
	-- For this reason, and to save space, the file only contains one 
	-- representative of each equivalence class.
	where
		swap_ij   (i,j,k,l) = if (i < j)                            then (j,i,k,l) else (i,j,k,l)
		swap_kl   (i,j,k,l) = if (k < l)                            then (i,j,l,k) else (i,j,k,l)
		swap_ijkl (i,j,k,l) = if ((i < k) || ((i == k) && (j < l))) then (k,l,i,j) else (i,j,k,l)

-- ----------------------------------------------------------------------
-- * Low-level parsing functions

-- | Decide whether a string is a comment. A comment is a line with
-- only whitespace characters, or where the first non-whitespace
-- character is \'\#\'.
is_comment :: String -> Bool
is_comment [] = True
is_comment ('#':t) = True
is_comment (h:t)
  | isSpace h = is_comment t
  | otherwise = False

-- | Extract an array from the one-electron file data. We do this
-- lazily, i.e., we stop reading as soon as enough data is found.
-- The resulting array uses spatial indices.
parsefile1 :: Int -> String -> Array (Int, Int) Double 
parsefile1 size content = 
  array ((0,0), (n, n)) list3
    where
      n = size-1
      list1 = [ read_line_h1 s | s <- lines content, not (is_comment s) ]
      list2 = takeWhile (\((i,j),h) -> i<size) list1
      list3 = filter in_range list2
      in_range ((i,j),h) = i<size && j<size

      read_line_h1 :: String -> ((Int,Int), Double)
      read_line_h1 s = case reads s of
        [(x, "")] -> x
        _ -> error ("Illegal line: " ++ s ++ " -- expected format ((int, int), double)")

-- | Extract an array from the two-electron file data. We do this
-- lazily, i.e., we stop reading as soon as enough data is found.  The
-- resulting array uses spatial indices in chemists' notation. Also,
-- the output array is sparse; it only contains as much data as the
-- file itself.
parsefile2 :: Int -> String -> Array (Int, Int, Int, Int) Double
parsefile2 size content =
  array ((0,0,0,0), (n,n,n,n)) list3
    where
      n = size-1
      list1 = [ read_line_h2 s | s <- lines content, not (is_comment s) ]
      list2 = takeWhile (\((i,j,k,l),h) -> i<size) list1
      list3 = filter in_range list2
      in_range ((i,j,k,l),h) = i<size && j<size && k<size && l<size

      read_line_h2 :: String -> ((Int,Int,Int,Int), Double)
      read_line_h2 s = case reads s of
        [(x, "")] -> x
        _ -> error ("Illegal line: " ++ s ++ " -- expected format ((int, int, int, int), double)")

-- ----------------------------------------------------------------------
-- * Conversion of spin to spatial indices

-- | In the molecule we have twice as many orbitals (spin orbitals)
-- than data in the integral file (spatial orbitals). This function
-- converts /h[sub 1]/ from spatial-orbitals (/M/\/2 = 104) to spin
-- orbitals (/M/ = 208).
-- 
-- Spin orbitals are indexed by /p/=(/i/, σ/[sub i]/), where /i/ is a spatial
-- index and σ/[sub i]/ is a spin (up or down). For two spin indices
-- /p/=(/i/, σ/[sub i]/) and /q/=(/j/, σ/[sub j]/), the transition integral
-- h[sub pq] is given by the following formula:
-- 
-- \[image spin1.png]
-- 
-- The Hamiltonian vanishes for σ/[sub i]/ ≠ σ/[sub j]/ because we
-- assume that there is no spin orbital coupling.
-- 
-- Given /M/\/2 spatial orbitals, we re-map the spin orbitals to
-- integers from 0 to /M/−1 using the formula /p/ = 2/i/+σ/[sub i]/,
-- where σ[sub i] is 0 or 1.
-- 
-- The function 'spin1' inputs (/h[sub ij]/), the table of 1-electron
-- integrals for /M/\/2 spatial orbitals, and outputs the
-- corresponding table (/h[sub pq]/) for /M/ spin orbitals.

spin1 :: ((Int,Int) -> Double) -> ((Int,Int) -> Double)
spin1 h1 (p,q) =
  if sigma_i == sigma_j
  then h1 (i,j) 
  else 0.0
    where 
      sigma_i = p .&. 1
      i = p `div` 2
      sigma_j = q .&. 1
      j = q `div` 2

-- | Like 'spin1', but for 2-electron integrals. Here, the transition
-- integrals in spin coordinates are given by:
-- 
-- \[image spin2.png]
-- 
-- The Hamiltonian vanishes for σ/[sub i]/ ≠ σ/[sub l]/ or σ/[sub j]/
-- ≠ σ/[sub k]/ because we assume that there is no spin orbital
-- coupling.
-- 
-- The function 'spin2' inputs (/h[sub ijkl]/), the table of
-- 2-electron transition amplitudes for /M/\/2 spatial orbitals, and
-- outputs the corresponding table (/h[sub pqrs]/) for /M/ spin
-- orbitals. Index ordering follows the physicists' convention.

spin2 :: ((Int, Int, Int, Int) -> Double) -> ((Int, Int, Int, Int) -> Double)
spin2 h2 (p,q,r,s) =
  if sigma_i == sigma_l && sigma_j == sigma_k
  then h2 (i,j,k,l)
  else 0.0
    where
      sigma_i = p .&. 1
      i = p `div` 2
      sigma_j = q .&. 1
      j = q `div` 2
      sigma_k = r .&. 1
      k = r `div` 2
      sigma_l = s .&. 1
      l = s `div` 2

-- * Testing

-- | Print the /h/[sub 1] data for 1-electron integrals.
print_1e :: GSEData -> String
print_1e gse_data = unlines $ [ inner_print i j | i <- list, j <- list]
	where list = [0..m-1]
	      inner_print i j = show (i,j) ++ " : " ++ show (h1 (i, j))
              m = gse_data_M gse_data
              h1 = gse_data_h1 gse_data

-- | Print the /h/[sub 2] data for 2-electron integrals.
print_2e :: GSEData -> String
print_2e gse_data = unlines $ [ inner_print i j k l | i <- list, j <- list, k <- list, l <- list]
	where list = [0..m-1]
	      inner_print i j k l = show (i,j,k,l) ++" : " ++ show (h2 (i, j, k, l))
              m = gse_data_M gse_data
              h2 = gse_data_h2 gse_data

-- | A main function to test the GSEData module.
gse_data_test :: Int -> IO ()		
gse_data_test n = do 
	gse_data <- load_gse_data n "h_1e_ascii" "h_2e_ascii"
	putStr $ print_1e gse_data
	putStr $ print_2e gse_data
