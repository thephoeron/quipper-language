@echo off

REM This file is part of Quipper. Copyright (C) 2011-2014. Please see the
REM file COPYRIGHT for a list of authors, copyright holders, licensing,
REM and other details. All rights reserved.
REM 
REM ======================================================================


:: Get working directory

set SCRIPT_DIR=%~dp0

:: run quipperdoc

bash "%SCRIPT_DIR%\quipperdoc" %*
