`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// REG_FILE (Register File) Module
//
// Description:
// This module implements a small register file containing 4 general-purpose 8-bit
// registers. It supports synchronous read and write operations with registered
// output. On reset, registers are initialized with sequential values starting
// from 2 (i.e., R0=2, R1=3, R2=4, R3=5).
//
// Features:
// - 4 general-purpose registers
// - 8-bit data width
// - Synchronous read/write operations
// - Registered output for better timing
// - Sequential initialization on reset
// - Single-port access
//
// Configuration:
// - Number of Registers: 4 (fixed)
// - Register Width: 8 bits (fixed)
// - Address Width: 2 bits (supports 4 registers)
//
// Ports:
// Inputs:
// - CLK:      System clock, positive edge triggered
// - RSTN:     Asynchronous reset, active low
// - ADDR:     Register address [3:0]
// - CE:       Chip enable for write operations
// - DATA_IN:  Data input for write operations [7:0]
//
// Outputs:
// - DATA_OUT: Data output from read operations [7:0]
//
// Operation Modes:
// 1. Reset (RSTN = 0):
//    - All registers initialized sequentially
//    - R0 = 2, R1 = 3, R2 = 4, R3 = 5
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

module REG_FILE (
    input CLK,                          // System clock
    input RSTN,                         // Async reset, active low
    input [3:0] ADDR,                   // Register address
    input CE,                           // Write enable
    input [7:0] DATA_IN,                // Write data input
    output [7:0] DATA_OUT               // Read data output
  );

  // Register array and output register
  reg [7:0] DATA_r [3:0];               // Register file array
  reg [7:0] DATA_OUT_r;                 // Output register

  // Register file control logic
  always @(posedge CLK or negedge RSTN)
  begin
    if (!RSTN)
      // Initialize registers with sequential values
      for (int i = 0; i < 4; i++)
      begin
        DATA_r[i] <= i + 2;             // R0=2, R1=3, R2=4, R3=5
      end
    else
    begin
      if (CE)
        DATA_r[ADDR] <= DATA_IN;        // Synchronous write
      
      DATA_OUT_r <= DATA_r[ADDR];       // Synchronous read
    end
  end

  // Output assignment
  assign DATA_OUT = DATA_OUT_r;         // Registered output

endmodule
