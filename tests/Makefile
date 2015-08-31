# This file is part of Quipper. Copyright (C) 2011-2014. Please see the
# file COPYRIGHT for a list of authors, copyright holders, licensing,
# and other details. All rights reserved.
# 
# ======================================================================


MULTIPLE_MAINS = yes
NODOC = yes
TARGET = And_gate And_list And_rev Arith Box BoxExample Classical	\
 Comments CountAccess Decompose_test DynamicLifting ErrorCircuit	\
 Example Example1 Example2 Example3 Example4 GPhase HelloWorld		\
 Infinite NamedGate NBox NoControl OptimTest ParseNodeRoot PhaseTest	\
 QEC QFT QFTAdder QRAM QuantumIfTest Reverse SimpleOracleSimulation	\
 SynthesisTest Teleport TeleportGeneric TemplateTest Test Testing	\
 TimeStep TimeStep-binary TransformerExample WithComputed
MODULES = $(TARGET:%=%.hs)
SUBDIR = tests
SUBPACKAGE = tests
BASEDIR = ..

include $(BASEDIR)/Makefile.common
