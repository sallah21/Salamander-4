//////////////////////////////////////////////////////////////////////////////////
// PROG_MEM (Program Memory) Module
//
// Description:
// This module implements the program memory for instruction storage and fetching.
// It provides synchronous read and write operations with registered output.
// The memory is initialized to 'x' on reset to help detect uninitialized memory
// accesses during simulation.
//
// Features:
// - Parameterized data and address widths
// - Synchronous read and write operations
// - Registered output for better timing
// - Initialization to 'x' for simulation safety
// - Single-port access
//
// Parameters:
// - DATA_SIZE: Width of instruction words (default: 16)
// - ADDR_SIZE: Width of address bus (default: 4)
//             Total memory size = 2^ADDR_SIZE instructions
//
// Ports:
// Inputs:
// - clk:     System clock, positive edge triggered
// - rstn:    Asynchronous reset, active low
// - W:       Write enable, active high
// - DATA_WR: Data input for write operations [DATA_SIZE-1:0]
// - ADDR:    Memory address for read/write [ADDR_SIZE-1:0]
//
// Outputs:
// - DATA:    Data output from read operations [DATA_SIZE-1:0]
//
// Operation Modes:
// 1. Reset (rstn = 0):
//    - All memory locations initialized to 'x'
//    - Helps detect uninitialized memory access
//
// 2. Write Operation (W = 1):
//    - On positive clock edge
//    - Data from DATA_WR written to int_mem_r[ADDR]
//    - Previous value at address is overwritten
//
// 3. Read Operation (W = 0):
//    - On positive clock edge
//    - Data from int_mem_r[ADDR] loaded into DATA_reg
//    - Registered output available on next clock
//
// Note: The 'synthesis preserve' attribute ensures the memory array
// maintains its structure during synthesis
//////////////////////////////////////////////////////////////////////////////////

module PROG_MEM #(
    parameter DATA_SIZE = 16,             // Width of instruction words
    parameter ADDR_SIZE = 4               // Width of address bus
  ) (
    input clk,                           // System clock
    input rstn,                          // Async reset, active low
    input W,                             // Write enable
    input  [DATA_SIZE-1:0] DATA_WR,      // Write data input
    input  [ADDR_SIZE-1:0] ADDR,         // Memory address
    output [DATA_SIZE-1:0] DATA          // Read data output
  );

  // Memory array definition
  logic [DATA_SIZE-1:0] int_mem_r [0:2**ADDR_SIZE-1] /* synthesis preserve */;

  // Output register for synchronous reads
  logic [DATA_SIZE-1:0] DATA_reg;

  // Memory control logic
  always @(posedge clk or negedge rstn)
  begin
    if (!rstn)
    begin
      // Initialize all memory locations to 'x'
      for (int i = 0; i < 2**ADDR_SIZE; i++)
      begin
        int_mem_r[i] <= {DATA_SIZE{1'bx}};  // Mark as uninitialized
      end
    end
    else if (W)
    begin
      int_mem_r[ADDR] <= DATA_WR;           // Synchronous write
    end
    else
    begin
      DATA_reg <= int_mem_r[ADDR];          // Synchronous read
    end
  end

  // Output assignment
  assign DATA = DATA_reg;                    // Registered output

endmodule
