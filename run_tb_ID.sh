#!/bin/bash

VCD_FILE=ID.vcd
SIM_FILE_LOG=ID_log.txt
SIM_FILE=ID
TB_FILE=verif/ID_TB.sv
RTL_FILE=rtl/ID.sv
GTKW_FILE=ID_TB.gtkw

rm -f $SIM_FILE_LOG 
rm -f $SIM_FILE
rm -f $VCD_FILE
clear 


echo "Compiling design..."
iverilog -Wall -g2005-sv -s ID_TB -o $SIM_FILE $RTL_FILE $TB_FILE   

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

if [ -f $GTKW_FILE ]; then
    echo "Opening GTKWave..."
    gtkwave $GTKW_FILE
elif [ -f $VCD_FILE ]; then
    echo "Opening VCD viewer..."
    gtkwave $VCD_FILE
else
    echo "Neither GTKWave nor VCD file was generated!"
    cat $SIM_FILE_LOG
    exit 1
fi

if [ $? -ne 0 ]; then
    echo "GTKWave failure"
    exit 1
fi
