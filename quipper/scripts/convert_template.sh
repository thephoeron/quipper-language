#!/bin/sh

# This file is part of Quipper. Copyright (C) 2011-2013. Please see the
# file COPYRIGHT for a list of authors, copyright holders, licensing,
# and other details. All rights reserved.
# 
# ======================================================================


SCRIPT_DIR="$(dirname "$0")"
MYNAME="$(basename "$0")"

usage() {
    echo "$MYNAME: the Quipper preprocessor"
    echo ""
    echo "Usage: $MYNAME <sourcefile> <infile> <outfile>"
    echo "Usage: $MYNAME -f"
    echo "Arguments and options:"
    echo " <sourcefile>  - the name of the original source file"
    echo " <infile>      - the name of the file holding the input"
    echo " <outfile>     - the name of the file to write the output to"
    echo " -f            - act as a filter (for testing)"
}

if test $# -eq 1 -a "$1" = "-f"; then
    SOURCE=/dev/stdin
    INPUT=/dev/stdin
    OUTPUT=/dev/stdout
elif test $# -eq 3; then
    SOURCE="$1"
    INPUT="$2"
    OUTPUT="$3"
    OUTDIR="$(dirname "$OUTPUT")"

    mkdir -p "$OUTDIR"
    touch "$OUTPUT"
else
    usage >& 2
    exit 1
fi

INPUT="$(echo "$INPUT" | sed -e 's/\\/\//g')"   # some windowsary thing
SOURCE="$(echo "$SOURCE" | sed -e 's/\\/\//g')" # some windowsary thing

(
    echo "{-# LANGUAGE TemplateHaskell #-}" 
    echo "{-# LINE 1 \"$SOURCE\" #-}" 
    awk -f "$SCRIPT_DIR/convert_template.awk" \
         -v haskell_filename="\"$SOURCE\""     \
         "$INPUT"
) > "$OUTPUT"
