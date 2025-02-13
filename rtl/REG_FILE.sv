`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// REG_FILE (Register File) Module
//
// Description:
// This module implements a small register file containing a variable number of 
// general-purpose registers. It supports synchronous read and write operations 
// with registered output. On reset, registers are initialized with sequential 
// values starting from 2 (i.e., R0=2, R1=3, R2=4, ...).
//
// Features:
// - Variable number of general-purpose registers
// - 8-bit data width
// - Synchronous read/write operations
// - Registered output for better timing
// - Sequential initialization on reset
// - Single-port access
//
// Configuration:
// - Number of Registers: variable (parameterizable)
// - Register Width: 8 bits (fixed)
// - Address Width: variable (dependent on register count)
//
// Ports:
// Inputs:
// - CLK:      System clock, positive edge triggered
// - RSTN:     Asynchronous reset, active low
// - ADDR:     Register address [$clog2(REG_COUNT)-1:0]
// - CE:       Chip enable for write operations
// - DATA_IN:  Data input for write operations [7:0]
//
// Outputs:
// - DATA_OUT: Data output from read operations [7:0]
//
// Operation Modes:
// 1. Reset (RSTN = 0):
//    - All registers initialized sequentially
//    - R0 = 2, R1 = 3, R2 = 4, ...
//
// 2. Write Operation (CE = 1):
//    - On positive clock edge
//    - Data from DATA_IN written to DATA_r[ADDR]
//    - Previous value at address is overwritten
//
// 3. Read Operation:
//    - Synchronous read on every clock edge
//    - Data from DATA_r[ADDR] loaded into DATA_OUT_r
//    - Registered output available on next clock
//
// Note: Read operations are always active, even during writes,
// providing the previous value until the next clock edge
//////////////////////////////////////////////////////////////////////////////////

module REG_FILE #(
    parameter REG_COUNT = 4,            // Number of registers
    parameter DATA_WIDTH = 8            // Width of each register
  ) (
    input logic CLK,                    // System clock
    input logic RSTN,                   // Async reset, active low
    input logic [$clog2(REG_COUNT)-1:0] ADDR,  // Register address
    input logic CE,                     // Write enable
    input logic [DATA_WIDTH-1:0] DATA_IN,  // Write data input
    output logic [DATA_WIDTH-1:0] DATA_OUT // Read data output
  );

  // Register array and output register
  logic [DATA_WIDTH-1:0] data_r [REG_COUNT-1:0];  // Register file array
  logic [DATA_WIDTH-1:0] data_out_r;              // Output register

  // Register file control logic
  always_ff @(posedge CLK or negedge RSTN) begin
    if (!RSTN) begin
      // Initialize registers with sequential values
      for (int i = 0; i < REG_COUNT; i++) begin
        data_r[i] <= i + 2;            // Sequential initialization
      end
      data_out_r <= '0;
    end else begin
      // Synchronous read always active
      data_out_r <= data_r[ADDR];
      
      // Synchronous write when enabled
      if (CE) begin
        data_r[ADDR] <= DATA_IN;
      end
    end
  end

  // Output assignment
  assign DATA_OUT = data_out_r;
endmodule
