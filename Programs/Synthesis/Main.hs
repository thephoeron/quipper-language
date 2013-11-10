-- This file is part of Quipper. Copyright (C) 2011-2013. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides a command line interface to the
-- decomposition library.

module Programs.Synthesis.Main where

import Libraries.Synthesis.Newsynth
import Libraries.Synthesis.SymReal
import Libraries.Synthesis.CliffordT
import Libraries.Synthesis.Ring
import Libraries.Synthesis.Matrix
import Libraries.Synthesis.LaTeX

import Libraries.CommandLine

-- import other stuff
import Control.Monad
import Data.Time
import System.Console.GetOpt
import System.Environment    
import System.Exit
import System.Random
import Text.Printf

-- ----------------------------------------------------------------------
-- * Option processing

-- | A data type to hold values set by command line options.
data Options = Options {
  opt_digits :: Double,       -- ^ Requested precision in digits (default: 10).
  opt_theta :: SymReal,       -- ^ Angle to approximate.
  opt_hex   :: Bool,          -- ^ Output operator in hex coding? (default: ASCII).
  opt_stats :: Bool,          -- ^ Output statistics?
  opt_latex :: Bool,          -- ^ Additional LaTeX output?
  opt_count :: Integer,       -- ^ Repetition count for stats (default: 1).
  opt_rseed :: Maybe StdGen   -- ^ An optional random seed.
} deriving Show

-- | The default options.
defaultOptions :: Options
defaultOptions = Options
  { opt_digits = 10,
    opt_theta = 0.0,
    opt_hex   = False,
    opt_stats = False,
    opt_latex = False,
    opt_count = 1,
    opt_rseed = Nothing
  }

-- | The list of command line options, in the format required by 'getOpt'.
options :: [OptDescr (Options -> IO Options)]
options =
  [ Option ['h'] ["help"]    (NoArg help)           "print usage info and exit",
    Option ['d'] ["digits"]  (ReqArg digits "<n>")  "set precision in decimal digits (default: 10)",
    Option ['b'] ["bits"]    (ReqArg bits "<n>")    "set precision in bits",
    Option ['e'] ["epsilon"] (ReqArg epsilon "<n>") "set precision as epsilon (default: 1e-10)",
    Option ['x'] ["hex"]     (NoArg hex)            "output hexadecimal coding (default: ASCII)",
    Option ['s'] ["stats"]   (NoArg stats)          "output statistics",
    Option ['l'] ["latex"]   (NoArg latex)          "additional output in LaTeX format",
    Option ['c'] ["count"]   (ReqArg count "<n>")   "average statistics over <n> runs (default: 1)",
    Option ['r'] ["rseed"]   (ReqArg rseed "\"<s>\"") "set optional random seed (default: random)"
  ]
    where
      help :: Options -> IO Options
      help o = do
        usage
        exitSuccess

      digits :: String -> Options -> IO Options
      digits string o =
        case parse_double string of
          Just n | n >= 0 -> return o { opt_digits = n }
          Just n -> optfail ("Number of digits must not be negative -- " ++ string ++ "\n")
          _ -> optfail ("Invalid digits -- " ++ string ++ "\n")

      bits :: String -> Options -> IO Options
      bits string o =
        case parse_double string of
          Just n | n >= 0 -> return o { opt_digits = n * logBase 10 2 }
          Just n -> optfail ("Number of bits must not be negative -- " ++ string ++ "\n")
          _ -> optfail ("Invalid bits -- " ++ string ++ "\n")

      epsilon :: String -> Options -> IO Options
      epsilon string o =
        case parse_double string of
          Just eps | eps < 1 && eps > 0 -> return o { opt_digits = -logBase 10 eps }
          Just n -> optfail ("Epsilon must be between 0 and 1 -- " ++ string ++ "\n")
          _ -> optfail ("Invalid epsilon -- " ++ string ++ "\n")

      hex :: Options -> IO Options
      hex o = return o { opt_hex = True }

      stats :: Options -> IO Options
      stats o = return o { opt_stats = True }

      latex :: Options -> IO Options
      latex o = return o { opt_latex = True }

      count :: String -> Options -> IO Options
      count string o =
        case parse_int string of
          Just n | n >= 1 -> return o { opt_count = n }
          Just n -> optfail ("Invalid count, must be positive -- " ++ string ++ "\n")
          _ -> optfail ("Invalid count -- " ++ string ++ "\n")

      rseed :: String -> Options -> IO Options
      rseed string o =
        case reads string of
          [(g, "")] -> return o { opt_rseed = Just g }
          _ -> optfail ("Invalid random seed -- " ++ string ++ "\n")

-- | Process /argv/-style command line options into an 'Options' structure.
dopts :: [String] -> IO Options
dopts argv = do
  let (o, args, errs) = getOpt Permute options argv
  opts <- foldM (flip id) defaultOptions o
  when (errs /= []) $ do
    optfail (concat errs)
  case args of
    [] -> optfail "Missing argument: theta.\n"
    [string] -> do
      case parse_SymReal string of
        Just theta -> return opts { opt_theta = theta }
        _ -> optfail ("Invalid theta -- " ++ string ++ "\n")
    h1:h2:[] -> optfail ("Too many non-option arguments -- " ++ h1 ++ ", " ++ h2 ++ "\n")
    h1:h2:_ -> optfail ("Too many non-option arguments -- " ++ h1 ++ ", " ++ h2 ++ "...\n")

-- | Print usage message to 'stdout'.
usage :: IO ()
usage = do
  putStr (usageInfo header options) 
    where header = 
            "Usage: newsynth [OPTION...] <theta>\n"
            ++ "Arguments:\n"
            ++ " <theta>                   z-rotation angle. May be symbolic, e.g. pi/128\n"
            ++ "Options:"

-- ----------------------------------------------------------------------
-- * The main function

-- | Main function: read options, then execute the appropriate tasks.
main :: IO()
main = do
  -- Read options.
  argv <- getArgs
  options <- dopts argv
  let digits = opt_digits options
  let prec = digits * logBase 2 10
  let theta = opt_theta options
  let count = opt_count options
  let exponent = ceiling digits
  
  -- Set random seed.
  g <- case opt_rseed options of
    Nothing -> newStdGen
    Just g -> return g
  
  -- Expand random seed opt_count times.
  let gs = expand_seed count g

  -- Do it for each element of gs.
  stats <- sequence $ flip map (zip gs [1..]) $ \(g,n) -> do
    
    when (count > 1 && (opt_stats options || opt_latex options)) $ do
      putStrLn ("Solution " ++ show n ++ ":")
    
    -- Payload.
    t0 <- getCurrentTime
    let (m,err,ct) = newsynth_stats prec theta g
        gates = to_gates m
    if opt_hex options then
      printf "%x\n" (convert gates :: Integer)
      else
      putStrLn (if gates == [] then "I" else convert gates)
    t1 <- getCurrentTime

    -- Print optional statistics
    let tcount = length $ filter (==T) gates
    let secs = diffUTCTime t1 t0
  
    when (opt_stats options || opt_latex options) $ do
      putStrLn ("Random seed: " ++ show g)
      putStrLn ("T-count: " ++ show tcount)
    
    when (opt_stats options) $ do
      putStrLn ("Theta: " ++ show theta)
      putStrLn ("Epsilon: " ++ show_exp 10 exponent (Just digits))
      putStrLn ("Matrix: " ++ show m)
      putStrLn ("Actual error: " ++ show_exp 10 exponent err)
      putStrLn ("Runtime: " ++ show secs)
      putStrLn ("Candidates tried: " ++ show ct)
      putStrLn ("Time/candidate: " ++ show (secs / fromInteger ct))

    -- Optional LaTeX output
    when (opt_latex options) $ do
      putStrLn ("LaTeX Gates: " ++ showlatex gates)
      putStrLn ("LaTeX Theta: " ++ showlatex theta)
      putStrLn ("LaTeX Epsilon: " ++ showlatex_exp 5 exponent (Just digits))
      putStrLn ("LaTeX Matrix: " ++ showlatex (convert gates :: U2 DOmega))
      putStrLn ("LaTeX Actual error: " ++ showlatex_exp 5 exponent err)
      putStrLn ("LaTeX Runtime: " ++ show (round_to 2 secs))
      putStrLn ("LaTeX Candidates tried: " ++ show ct)
      putStrLn ("LaTeX Time/candidate: " ++ show (round_to 4 (secs / fromInteger ct)))
      
    when (count > 1 && (opt_stats options || opt_latex options)) $ do
      putStrLn ""

    return (ct, secs)

  -- If count > 1, show summary stats.
  when (count > 1) $ do
    let (cts, secss) = unzip stats
    let ct_total = sum cts
    let secs_total = sum secss
    
    when (opt_stats options || opt_latex options) $ do
      putStrLn "Summary:"
      putStrLn ("Number of runs: " ++ show count)
      putStrLn ("Total runtime: " ++ show secs_total)
    
    when (opt_stats options) $ do
      putStrLn ("Average runtime: " ++ show (secs_total / fromInteger count))
      putStrLn ("Average candidates tried: " ++ show (fromInteger ct_total / fromInteger count :: Double))
      putStrLn ("Average time/candidate: " ++ show (secs_total / fromInteger ct_total))

    when (opt_latex options) $ do
      putStrLn ("LaTeX Average runtime: " ++ show (round_to 2 (secs_total / fromInteger count)))
      putStrLn ("LaTeX Average candidates tried: " ++ show (fromInteger ct_total / fromInteger count :: Double))
      putStrLn ("LaTeX Average time/candidate: " ++ show (round_to 4 (secs_total / fromInteger ct_total)))

-- ----------------------------------------------------------------------
-- * Miscellaneous

-- | Round a 'RealFrac' value to the given number of decimals.                
round_to :: (RealFrac r) => Integer -> r -> r               
round_to n x = fromInteger (round (x * 10^n)) / 10^n

-- | Show the number 10[sup -/x/] in the format 10^(-n) or
-- 1.23*10^(-n), with precision /d/ and exponent -/n/. A value of
-- 'Nothing' is treated as 0.
-- 
-- For example, display @0.316*10^(-13)@ instead of @10^(-13.5)@.
show_exp :: (Show r, RealFrac r, Floating r, PrintfArg r) => Integer -> Integer -> Maybe r -> String
show_exp d n x
  | y == 1    = "10^(" ++ show (-n) ++ ")"
  | otherwise = printf ("%." ++ show d ++ "f") y ++ "*10^(" ++ show (-n) ++ ")"
  where
    y = case x of
      Nothing -> 0
      Just x -> round_to d (10 ** (fromInteger n - x))
  
-- | Show the number 10[sup -/x/] in the format @10^{-n}@ or
-- @1.23\\cdot 10^{-n}@, with precision /d/ and exponent -/n/. A value
-- of 'Nothing' is treated as 0.
showlatex_exp :: (Show r, RealFrac r, Floating r, PrintfArg r) => Integer -> Integer -> Maybe r -> String
showlatex_exp d n x 
  | y == 1    = "10^{" ++ show (-n) ++ "}"
  | otherwise = printf ("%." ++ show d ++ "f") y ++ "\\cdot 10^{" ++ show (-n) ++ "}"
  where
    y = case x of
      Nothing -> 0
      Just x -> round_to d (10 ** (fromInteger n - x))

-- | Expand a random seed /g/ into a list [/g/[sub 1], …, 
-- /g/[sub /n/]] of /n/ random seeds. This is done in such a way that
-- /g/[sub 1] = /g/.
expand_seed :: (RandomGen g) => Integer -> g -> [g]
expand_seed 0 g = []
expand_seed n g = g:expand_seed (n-1) g' where
  (g', _) = split g
