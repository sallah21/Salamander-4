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
// - W:        Write enable, active high
// - DATA_WR:  Data input for write operations [DATA_SIZE-1:0]
// - ADDR:     Memory address for read/write [ADDR_SIZE-1:0]
//
// Outputs:
// - DATA_RD:  Data output from read operations [DATA_SIZE-1:0]
//
// Operation:
// 1. Reset:
//    - All memory locations initialized to their address value
//    - mem_r[0] = 0, mem_r[1] = 1, ..., mem_r[MEM_SIZE-1] = MEM_SIZE-1
//
// 2. Write Operation (W = 1):
//    - On positive clock edge
//    - Data from DATA_WR written to mem_r[ADDR]
//    - Previous value at address is overwritten
//
// 3. Read Operation:
//    - Continuous (asynchronous) read from mem_r[ADDR]
//    - No clock required for reads
//
// Note: The 'synthesis preserve' attribute ensures the memory array
// maintains its structure during synthesis
//////////////////////////////////////////////////////////////////////////////////

module DATA_MEM #(
    parameter DATA_SIZE = 8,              // Width of data words
    parameter ADDR_SIZE = 5               // Width of address bus
)
(
    input clk,                           // System clock
    input rstn,                          // Async reset, active low
    input W,                             // Write enable
    input [DATA_SIZE-1:0] DATA_WR,       // Write data input
    input [ADDR_SIZE-1:0] ADDR,          // Memory address
    output [DATA_SIZE-1:0] DATA_RD       // Read data output
);

    // Memory array definition
    localparam MEM_SIZE = 2**ADDR_SIZE;  // Calculate total memory size
    reg [DATA_SIZE-1:0] mem_r[0:MEM_SIZE-1] /* synthesis preserve */;  // Memory array

    // Synchronous write with asynchronous reset
    always @(posedge clk)
    begin
        if (!rstn)
        begin
            // Initialize memory with sequential values
            for (int i = 0; i < MEM_SIZE; i++)
            begin
                mem_r[i] <= i;           // Each location gets its address as initial value
            end
        end
        else
        begin
            if (W)
            begin
                mem_r[ADDR] <= DATA_WR;  // Write operation
            end
        end
    end
    
    // Asynchronous read
    assign DATA_RD = mem_r[ADDR];        // Continuous read output

endmodule