-- This file is part of Quipper. Copyright (C) 2011-2014. Please see the
-- file COPYRIGHT for a list of authors, copyright holders, licensing,
-- and other details. All rights reserved.
-- 
-- ======================================================================

-- | This module provides an enumeration type for gate bases. This is
-- useful, for example, to provide a uniform interface to gate base
-- decomposers, so that they can be selected via command line options
-- or function arguments.

module QuipperLib.Decompose.GateBase where

import Quipper
import Quipper.Internal

import QuipperLib.Synthesis
import QuipperLib.Decompose.Legacy
import QuipperLib.Decompose.CliffordT

import Libraries.RandomSource

import System.Random

-- ----------------------------------------------------------------------
-- * Gate bases

-- | An enumeration type for gate bases. More cases can be added in
-- the future, for example for using gates from a particular physical
-- machine description. 
-- 
-- Some gate bases carry additional parameters; for example, in the
-- case of decomposition into a discrete gate base, one may specify a
-- precision ε, a random seed, or other flags.
-- 
-- If a 'Precision' parameter is present, it specifies the desired
-- precision per gate. If a 'RandomSource' parameter is present, it
-- specifies a source of randomness.
-- 
-- If a 'KeepPhase' parameter is present, it determines whether global
-- phases are respected ('True') or disregarded ('False').
data GateBase =
  Logical   
    -- ^ Use all logical gates, i.e., leave the circuit unchanged.
  | Binary  
    -- ^ Decompose into binary gates.
  | Toffoli 
    -- ^ Decompose into Toffoli and binary gates.
  | CliffordT_old 
    -- ^ Decompose into Clifford+/T/. This is a legacy transformer
    -- that does not handle all gates correctly. For example, it does
    -- not handle /W/-gates, rotations, or phase gates. Use
    -- 'CliffordT' instead.
  | CliffordT KeepPhase Precision RandomSource 
    -- ^ Decompose into Clifford+/T/, specifically: single-qubit
    -- Clifford gates, the controlled-not gate (with positive or
    -- negative controls), and the gates /T/ and /T/[sup †].
  | Standard Precision RandomSource
    -- ^ Decompose into the standard gate set, which we define to be
    -- /X/, /Y/, /Z/, /H/, /S/, /S/[sup †], /T/, /T/[sup †], and
    -- /CNOT/. Suppresses global phases.
  | Strict Precision RandomSource
    -- ^ Decompose into /H/, /S/, /T/, /CNOT/ gates only. Suppresses
    -- global phases.
  | Approximate KeepPhase Precision RandomSource
    -- ^ Decompose rotation and phase gates into Clifford+/T/, using
    -- an approximate synthesis algorithm. Other gates are unchanged.
  | Exact 
    -- ^ Decompose gates that can be exactly represented in the
    -- Clifford+/T/ base into that base, specifically: single-qubit
    -- Clifford gates, the controlled-not gate (with positive or
    -- negative controls), and the gates /T/ and /T/[sup †]. Leave
    -- rotation and phase gates unchanged.
  | TrimControls 
    -- ^ Eliminate excess controls from gates.
  deriving Show

-- | An assignment of gate bases to names. Names are given as
-- lower-case strings.
-- 
-- This can be useful, e.g., in the definition of command line
-- options.
-- 
-- In the future, the syntax should be extended so that users can
-- specify parameters (e.g., the precision, random seed) on the
-- command line as well. For now, we just use the default precision.
gatebase_enum :: [(String, GateBase)]
gatebase_enum = [
  ("logical", Logical),
  ("binary", Binary),
  ("toffoli", Toffoli),
  ("cliffordt_old", CliffordT_old),
  ("cliffordt", CliffordT False (30 * digits) rs),
  ("cliffordt_keepphase", CliffordT True (30 * digits) rs),
  ("standard", Standard (30 * digits) rs),
  ("strict", Strict (30 * digits) rs),
  ("approximate", Approximate False (30 * digits) rs),
  ("approximate_keepphase", Approximate True (30 * digits) rs),
  ("exact", Exact),
  ("trimcontrols", TrimControls)
  ]
  where
    rs = RandomSource (read "1" :: StdGen)

-- ----------------------------------------------------------------------
-- * Generic decomposition

-- | Decompose a circuit into gates from the given 'GateBase'. This
-- can be applied to a circuit-generating function in curried form
-- with /n/ arguments, for any /n/ ≥ 0.
-- 
-- The type of this heavily overloaded function is difficult to
-- read. In more readable form, it has all of the following types:
-- 
-- > decompose_generic :: (QCData qa) => GateBase -> Circ qa -> Circ qa
-- > decompose_generic :: (QCData qa, QCData qb) => GateBase -> (qa -> Circ qb) -> (qa -> Circ qb)
-- > decompose_generic :: (QCData qa, QCData qb, QCData qc) => GateBase -> (qa -> qb -> Circ qc) -> (qa -> qb -> Circ qc)
-- 
-- and so forth.

decompose_generic :: (QCData qa, QCData qb, QCurry qfun qa qb) => GateBase -> qfun -> qfun
decompose_generic Logical = id
decompose_generic Binary = decompose_legacy_generic GB_Binary
decompose_generic Toffoli = decompose_legacy_generic GB_Toffoli
decompose_generic CliffordT_old = decompose_legacy_generic GB_CliffordT
decompose_generic (CliffordT kp prec (RandomSource g)) = exact_ct_generic . approx_ct_generic kp prec g
decompose_generic (Standard prec (RandomSource g)) = standard_generic . exact_ct_generic . approx_ct_generic False prec g
decompose_generic (Strict prec (RandomSource g)) = strict_generic . exact_ct_generic . approx_ct_generic False prec g
decompose_generic (Approximate kp prec (RandomSource g)) = approx_ct_generic kp prec g
decompose_generic Exact = exact_ct_generic
decompose_generic TrimControls = trimcontrols_generic


