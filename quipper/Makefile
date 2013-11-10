# This file is part of Quipper. Copyright (C) 2011-2013. Please see the
# file COPYRIGHT for a list of authors, copyright holders, licensing,
# and other details. All rights reserved.
# 
# ======================================================================


MODULES = Quipper.hs Quipper/CircLifting.hs Quipper/Circuit.hs	\
 Quipper/Classical.hs Quipper/Control.hs Quipper/Generic.hs	\
 Quipper/Internal.hs Quipper/Labels.hs Quipper/Monad.hs		\
 Quipper/Printing.hs Quipper/QClasses.hs Quipper/QData.hs	\
 Quipper/Transformer.hs
TARGET = Quipper.hi
SUBPACKAGE = quipper
SUBDIR = quipper
SUBDIR_ROOT = quipper
SUBDIR_REL = .
BASEDIR = ..
CLEAN_SUBDIRS = Quipper Quipper/Template

SCRIPTS=acroread.bat convert_template.awk convert_template.bat	\
 convert_template.sh epstopdf.bat quipper quipperi quipperdoc	\
 quipperdoc.bat quipper.bat quipperi.bat
EXTRA_DIST=$(SCRIPTS:%=scripts/%)

include $(BASEDIR)/Makefile.common
