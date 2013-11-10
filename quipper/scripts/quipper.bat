@echo off

REM This file is part of Quipper. Copyright (C) 2011-2013. Please see the
REM file COPYRIGHT for a list of authors, copyright holders, licensing,
REM and other details. All rights reserved.
REM 
REM ======================================================================


:: Get working directory

set SCRIPT_DIR=%~dp0

:: run quipper

bash "%SCRIPT_DIR%\quipper" %* 
