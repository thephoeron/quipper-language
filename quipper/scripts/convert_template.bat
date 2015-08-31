@echo off

REM This file is part of Quipper. Copyright (C) 2011-2014. Please see the
REM file COPYRIGHT for a list of authors, copyright holders, licensing,
REM and other details. All rights reserved.
REM 
REM ======================================================================



:: The directory in which this batch file is
set WD=%~dp0

bash.exe %WD%/convert_template.sh %1 %2 %3

