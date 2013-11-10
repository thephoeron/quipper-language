# This file is part of Quipper. Copyright (C) 2011-2013. Please see the
# file COPYRIGHT for a list of authors, copyright holders, licensing,
# and other details. All rights reserved.
# 
# ======================================================================


MODULES = ArcTan2.hs Clifford.hs CliffordT.hs EuclideanDomain.hs	\
  EulerAngles.hs LaTeX.hs Matrix.hs MultiQubitSynthesis.hs		\
  Newsynth.hs Ring.hs Ring/FixedPrec.hs Random/FixedPrec.hs		\
  RotationDecomposition.hs SymReal.hs
TARGET = $(MODULES:%.hs=%.hi)
SUBPACKAGE = synthesis
SUBDIR = Libraries/Synthesis
BASEDIR = ../..
CLEAN_SUBDIRS = Ring Random

include $(BASEDIR)/Makefile.common
