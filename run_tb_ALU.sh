#!/bin/bash

VCD_FILE=ALU.vcd
SIM_FILE_LOG=ALU_log.txt
SIM_FILE=ALU
TB_FILE=verif/ALU_TB.sv
RTL_FILE=rtl/ALU.sv
GTKW_FILE=ALU_TB.gtkw

rm -f $SIM_FILE_LOG 
rm -f $SIM_FILE
rm -f $VCD_FILE
clear 


echo "Compiling design..."
iverilog -Wall -g2005-sv -s ALU_TB -o $SIM_FILE $RTL_FILE $TB_FILE rtl/OP_CODES.sv

if [ $? -eq 1 ]; then
    echo "Source compilation failure"
    exit 1
fi

echo "Running simulation..."
vvp -n $SIM_FILE

if [ $? -ne 0 ]; then
    echo "Running simulation failure"
    cat ACU_log.txt
    exit 1
fi

echo "Opening waveform viewer..."

if [ ! -f $GTKW_FILE ]; then
    echo "GTKWave file was not generated!"
    cat ACU_log.txt
    if [ ! -f $VCD_FILE ]; then
        echo "VCD file was not generated!"
        cat ACU_log.txt
        exit 1
    fi
    gtkwave $VCD_FILE
    else
    gtkwave $GTKW_FILE
fi




if [ $? -ne 0 ]; then
    echo "GTKWave failure"
    exit 1
fi
