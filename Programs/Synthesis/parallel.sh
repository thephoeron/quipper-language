#!/bin/bash

# This file is part of Quipper. Copyright (C) 2011-2013. Please see the
# file COPYRIGHT for a list of authors, copyright holders, licensing,
# and other details. All rights reserved.
# 
# ======================================================================


for i in $(seq 0 1 12); do
	echo "Running ./fowler phase_gate $i > phase_gate.$i.txt"
	echo "===== Starting to run at `date`" >> phase_gate.$i.txt
	./fowler phase_gate $i >> phase_gate.$i.txt &
done

read -p  "Hit any key to kill all 'fowler' processes"
killall -s SIGINT fowler

