//////////////////////////////////////////////////////////////////////////////////
// STACK Module
//
// Description:
// This module implements a parameterized Last-In-First-Out (LIFO) stack with 
// configurable data width and depth. It supports push (write) and pop (read)
// operations with full and empty status flags. The stack pointer automatically
// manages the current position for push/pop operations.
//
// Features:
// - Parameterized data width and stack depth
// - Push (write) and pop (read) operations
// - Stack full and empty status flags
// - Automatic stack pointer management
// - Synchronous operations with async reset
// - Protection against overflow and underflow
//
// Parameters:
// - DATA_SIZE:   Width of each stack entry (default: 4)
// - STACK_SIZE:  Address width of stack (default: 4)
//               Total stack depth = 2^STACK_SIZE entries
//
// Ports:
// Inputs:
// - CLK:      System clock, positive edge triggered
// - RSTN:     Asynchronous reset, active low
// - W:        Write enable (push operation)
// - R:        Read enable (pop operation)
// - DATA_WR:  Data to push onto stack [DATA_SIZE-1:0]
//
// Outputs:
// - DATA_RD:      Data popped from stack [DATA_SIZE-1:0]
// - stack_full:   Flag indicating stack is full
// - stack_empty:  Flag indicating stack is empty
//
// Operation Modes:
// 1. Reset (RSTN = 0):
//    - Stack pointer reset to 0
//    - Output data cleared
//    - Stack marked as empty
//    - Full flag cleared
//
// 2. Push Operation (W = 1):
//    - When stack not full:
//      * Write DATA_WR to current address
//      * Increment stack pointer
//      * Update full/empty flags
//    - When stack full:
//      * Operation ignored
//
// 3. Pop Operation (R = 1):
//    - When stack not empty:
//      * Read data from top of stack
//      * Decrement stack pointer
//      * Update full/empty flags
//    - When stack empty:
//      * Operation ignored
//
// Note: The 'synthesis preserve' attributes ensure critical registers
// maintain their structure during synthesis
//////////////////////////////////////////////////////////////////////////////////

module STACK #(
    parameter DATA_SIZE = 4,              // Width of stack entries
    parameter STACK_SIZE = 4              // Stack address width
)
(
    input CLK,                           // System clock
    input RSTN,                          // Async reset, active low
    input W,                             // Write (push) enable
    input R,                             // Read (pop) enable
    input [DATA_SIZE-1:0] DATA_WR,       // Push data input
    output [DATA_SIZE-1:0] DATA_RD,      // Pop data output
    output stack_full,                   // Stack full flag
    output stack_empty                   // Stack empty flag
);  

// Calculate total stack memory size
localparam STACK_MEM_SIZE = 2**STACK_SIZE;

// Internal registers
reg [DATA_SIZE-1:0] DATA_RD_r;                              // Output data register
reg [STACK_SIZE-1:0] STACK_ADDR_r;                          // Stack pointer
reg [DATA_SIZE-1:0] mem_r [0:STACK_MEM_SIZE-1] /* synthesis preserve */;  // Stack memory
reg stack_full_r /* synthesis preserve */;                   // Full flag register
reg stack_empty_r /* synthesis preserve */;                  // Empty flag register

// Stack control logic
always @(posedge CLK or negedge RSTN)
begin
    if (!RSTN)
    begin
        DATA_RD_r <= '0;                 // Clear output data
        STACK_ADDR_r <= '0;              // Reset stack pointer
        stack_full_r <= 1'b0;            // Clear full flag
        stack_empty_r <= 1'b1;           // Set empty flag
    end      
    else
    begin
        if (W && !stack_full_r)          // Push operation
        begin
            mem_r[STACK_ADDR_r] <= DATA_WR;
            STACK_ADDR_r <= STACK_ADDR_r + 1;
            stack_empty_r <= 1'b0;
            stack_full_r <= (STACK_ADDR_r == STACK_MEM_SIZE-2);
        end
        else if (R && !stack_empty_r)    // Pop operation
        begin
            DATA_RD_r <= mem_r[STACK_ADDR_r-1];
            STACK_ADDR_r <= STACK_ADDR_r - 1;
            stack_full_r <= 1'b0;
            stack_empty_r <= (STACK_ADDR_r == 1);
        end
    end 
end

// Output assignments
assign DATA_RD = DATA_RD_r;              // Stack data output
assign stack_full = stack_full_r;        // Full status
assign stack_empty = stack_empty_r;      // Empty status

endmodule