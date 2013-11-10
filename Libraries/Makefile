# This file is part of Quipper. Copyright (C) 2011-2013. Please see the
# file COPYRIGHT for a list of authors, copyright holders, licensing,
# and other details. All rights reserved.
# 
# ======================================================================


MODULES = Auxiliary.hs CommandLine.hs PortableSignals.hs		\
          RandomSource.hs Render.hs Sampling.hs ShowAll.hs		\
          Stabilizers/Pauli.hs Stabilizers/Clifford.hs Template.hs	\
          Template/Auxiliary.hs Template/ErrorMsgQ.hs			\
          Template/Lifting.hs Template/LiftQ.hs Tuple.hs Typeable.hs
TARGET = $(MODULES:%.hs=%.hi)
SUBPACKAGE = libraries
SUBDIR = Libraries
BASEDIR = ..
CLEAN_SUBDIRS = Stabilizers QuipperASCIIParser Template

include $(BASEDIR)/Makefile.common
