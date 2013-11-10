# This file is part of Quipper. Copyright (C) 2011-2013. Please see the
# file COPYRIGHT for a list of authors, copyright holders, licensing,
# and other details. All rights reserved.
# 
# ======================================================================


MODULES = Arith.hs Decompose.hs Decompose/CliffordT.hs			\
          Decompose/GateBase.hs Decompose/Legacy.hs			\
          DynamicLiftings.hs GateDecompositions.hs FPReal.hs QFT.hs	\
          QFTAdd.hs Qram.hs QuipperASCIIParser/Parse.hs			\
          QuipperASCIIParser/CircInfo.hs				\
          QuipperASCIIParser/ASCIICirc.hs QuipperASCIIParser.hs		\
          Qureg.hs Simulation.hs Simulation/ClassicalSimulation.hs	\
          Simulation/CliffordSimulation.hs				\
          Simulation/QuantumSimulation.hs Synthesis.hs			\
          Unboxing.hs                                                   \
          ClassicalOptim/Circuit.hs ClassicalOptim/AlgExp.hs            \
          ClassicalOptim.hs                                             \
          ClassicalOptim/QuipperInterface.hs                            \
          ClassicalOptim/Simplification.hs                              \
          ClassicalOptim/QuickCheck.hs ClassicalOptim/QuickCheckArith.hs
TARGET = $(MODULES:%.hs=%.hi)
SUBPACKAGE = quipperlib
SUBDIR = QuipperLib
BASEDIR = ..
CLEAN_SUBDIRS = Decompose QuipperASCIIParser Simulation ClassicalOptim

include $(BASEDIR)/Makefile.common
