#!/bin/bash
clear 
VCD_FILE=DATA_STORE_TEST.vcd
SIM_FILE_LOG=DATA_STORE_TEST_log.txt
SIM_FILE=DATA_STORE_TEST
TB_FILE=DATA_STORE_TB.sv
GTKW_FILE=DATA_STORE_TEST.gtkw

# Directory setup
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
RTL_DIR="$SCRIPT_DIR/../../rtl"

rm -f $SIM_FILE_LOG 
rm -f $SIM_FILE
rm -f $VCD_FILE
clear 

echo "Compiling design..."
iverilog -Wall -g2012 -s DATA_STORE_TB -o $SIM_FILE \
  $RTL_DIR/OP_CODES.sv \
  $RTL_DIR/ALU.sv \
  $RTL_DIR/ID.sv \
  $RTL_DIR/PC.sv \
  $RTL_DIR/ACU.sv \
  $RTL_DIR/REG_FILE.sv \
  $RTL_DIR/PROG_MEM.sv \
  /Users/salsamon/ASIC/Projektowanie_mikroprocesorow/windsurf/Salamander-4/top_level.sv \
  $TB_FILE

if [ $? -eq 1 ]; then
    echo "Source compilation failure"
    exit 1
fi

echo "Running simulation..."
vvp -n $SIM_FILE

if [ $? -ne 0 ]; then
    echo "Running simulation failure"
    cat $SIM_FILE_LOG
    exit 1
fi

echo "Opening waveform viewer..."

if [ ! -f $GTKW_FILE ]; then
    echo "GTKWave file was not generated!"
    cat $SIM_FILE_LOG
    if [ ! -f $VCD_FILE ]; then
        echo "VCD file was not generated!"
        cat $SIM_FILE_LOG
        exit 1
    fi
    gtkwave $VCD_FILE
else
    gtkwave $GTKW_FILE
fi

if [ $? -ne 0 ]; then
    echo "Opening waveform viewer failure"
    cat $SIM_FILE_LOG
    exit 1
fi
