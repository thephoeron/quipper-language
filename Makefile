# This file is part of Quipper. Copyright (C) 2011-2013. Please see the
# file COPYRIGHT for a list of authors, copyright holders, licensing,
# and other details. All rights reserved.
# 
# ======================================================================

# TOP-LEVEL MAKEFILE FOR QUIPPER

LIBRARIES:=Libraries Libraries/Synthesis QuipperLib

ALGORITHMS:= Algorithms/BF Algorithms/BWT Algorithms/CL			\
       Algorithms/GSE Algorithms/QLS Algorithms/TF Algorithms/USV

PROGRAMS:=Programs/QCLParser Programs/Synthesis Programs/Tools

TESTS:=tests tests/template

SUBDIRS:=quipper $(LIBRARIES) $(ALGORITHMS) $(PROGRAMS) $(TESTS)

# ----------------------------------------------------------------------
# Default rule

.PHONY: all fast
.PHONY: $(SUBDIRS)

all: 
	$(MAKE) SUBDIR_TARGET=all $(FAST) $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) $(FAST) -C "$@" $(SUBDIR_TARGET)

quipper: Libraries
Libraries/Synthesis: Libraries
QuipperLib: Libraries/Synthesis Libraries quipper
$(ALGORITHMS): quipper $(LIBRARIES)
$(PROGRAMS): quipper $(LIBRARIES)
$(TESTS): quipper $(LIBRARIES) $(ALGORITHMS)


# ----------------------------------------------------------------------
# Faster compilation: "make fast <target>" will skip optimization

FAST := 
fast: 
	$(eval FAST := fast)

# ----------------------------------------------------------------------
# Cleaning

tidy:
	$(MAKE) SUBDIR_TARGET=tidy $(FAST) $(SUBDIRS)

clean:
	$(MAKE) SUBDIR_TARGET=clean $(FAST) $(SUBDIRS)
