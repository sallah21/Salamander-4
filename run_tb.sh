#!/bin/bash

rm -f ex1
rm -f wave.vcd
clear 

GTKW_FILE=/Users/salsamon/ASIC/Projektowanie_mikroprocesorow/windsurf/Salamander-4/dp.gtkw
echo "Compiling design..."
iverilog -Wall -g2005-sv -s CPU_toplevel_tb -o ex1 -f cpu_src.cmd top_level.sv ./verif/TB.sv

if [ $? -eq 1 ]; then
    echo "Source compilation failure"
    exit 1
fi

echo "Running simulation..."
vvp -n -l log.txt ex1       

if [ $? -ne 0 ]; then
    echo "Running simulation failure"
    cat log.txt
    exit 1
fi

if [ ! -f wave.vcd ]; then
    echo "VCD file was not generated!"
    cat log.txt
    exit 1
fi

echo "Opening waveform viewer..."

gtkwave $GTKW_FILE
if [ $? -ne 0 ]; then
    echo "GTKWave failure"
    gtkwave wave.vcd
fi

if [ $? -ne 0 ]; then
    echo "GTKWave failure"
    exit 1
fi
