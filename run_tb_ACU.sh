#!/bin/bash

VCD_FILE=ACU.vcd
SIM_FILE_LOG=ACU_log.txt
SIM_FILE=ACU
TB_FILE=verif/ACU_TB.sv
RTL_FILE=rtl/ACU.sv
GTKW_FILE=ACU_TB.gtkw

rm -f $SIM_FILE_LOG 
rm -f $SIM_FILE
rm -f $VCD_FILE
clear 


echo "Compiling design..."
iverilog -Wall -g2005-sv -s ACU_TB -o $SIM_FILE $RTL_FILE $TB_FILE

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
