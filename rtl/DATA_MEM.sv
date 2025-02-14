//////////////////////////////////////////////////////////////////////////////////
// DATA_MEM (Data Memory) Module
//
// Description:
// This module implements a synchronous read/write memory unit for data storage.
// The memory is initialized with sequential values (0 to MEM_SIZE-1) on reset.
// It supports single-port operations with synchronous writes and asynchronous reads.
//
// Features:
// - Parameterized data and address widths
// - Synchronous write operations
// - Asynchronous read operations
// - Automatic sequential initialization on reset
// - Single-port access
//
// Parameters:
// - DATA_SIZE: Width of data words (default: 8)
// - ADDR_SIZE: Width of address bus (default: 5)
// - MEM_SIZE:  Total memory size (2^ADDR_SIZE words)
//
// Ports:
// Inputs:
// - clk:      System clock, positive edge triggered
// - rstn:     Asynchronous reset, active low
// - w:        Write enable, active high
// - data_wr:  Data input for write operations [DATA_SIZE-1:0]
// - addr:     Memory address for read/write [ADDR_SIZE-1:0]
//
// Outputs:
// - data_rd:  Data output from read operations [DATA_SIZE-1:0]
//
// Operation:
// 1. Reset:
//    - All memory locations initialized to their address value
//    - mem_r[0] = 0, mem_r[1] = 1, ..., mem_r[MEM_SIZE-1] = MEM_SIZE-1
//
// 2. Write Operation (w = 1):
//    - On positive clock edge
//    - Data from data_wr written to mem_r[addr]
//    - Previous value at address is overwritten
//
// 3. Read Operation:
//    - Continuous (asynchronous) read from mem_r[addr]
//    - No clock required for reads
//
// Note: The 'synthesis preserve' attribute ensures the memory array
// maintains its structure during synthesis
//////////////////////////////////////////////////////////////////////////////////

module DATA_MEM #(
    parameter DATA_SIZE = 8,              // Width of data words
    parameter ADDR_SIZE = 5               // Width of address bus
) (
    input logic clk,                      // System clock
    input logic rstn,                     // Async reset, active low
    input logic W,                        // Write enable
    input logic [DATA_SIZE-1:0] DATA_WR,  // Write data input
    input logic [ADDR_SIZE-1:0] ADDR,     // Memory address
    output logic [DATA_SIZE-1:0] DATA_RD  // Read data output
);

    // Memory array definition
    localparam MEM_SIZE = 2**ADDR_SIZE;   // Calculate total memory size
    logic [DATA_SIZE-1:0] mem_r[0:MEM_SIZE-1] /* synthesis preserve */;
    
    // Address validation
    logic addr_valid = (ADDR < MEM_SIZE);

    // Synchronous write with asynchronous reset
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            // Initialize memory with sequential values
            for (int i = 0; i < MEM_SIZE; i++) begin
                mem_r[i] <= i[DATA_SIZE-1:0];  // Truncate to data width
            end
        end else if (W && addr_valid) begin
            mem_r[ADDR] <= DATA_WR;
        end
    end
    
    // Asynchronous read with address validation
    assign DATA_RD = addr_valid ? mem_r[ADDR] : {DATA_SIZE{1'bx}};
endmodule