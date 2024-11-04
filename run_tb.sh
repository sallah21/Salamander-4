#!/bin/bash

rm -f ex1
rm -f ex1.vcd
clear 
iverilog -Wall -g2005-sv -s top_level -o ex1 -f cpu_src.cmd top_level.sv ./verif/TB.sv

if [ $? -eq 1 ]; then
    echo Source compilation failure
    exit 1
fi

vvp -l log.txt ex1

if [ $? -ne 0 ]; then
    echo Running simulation failure
    exit 1
fi

gtkwave ex1.gtkw

if [$? -ne 0]; then
    echo GTKWave failure
    exit 1
fi

