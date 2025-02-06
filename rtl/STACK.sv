`timescale 1ns / 1ps
/**
    Stack module
*/

module STACK #(
    parameter DATA_SIZE = 4,
    parameter STACK_SIZE = 4
)
(
    input CLK,
    input RSTN,
    input W,
    input R,
    input [DATA_SIZE-1:0] DATA_WR,
    output [DATA_SIZE-1:0] DATA_RD,
    output stack_full,
    output stack_empty
);  

localparam STACK_MEM_SIZE = 2**STACK_SIZE;

reg [DATA_SIZE-1:0] DATA_RD_r;
reg [STACK_SIZE-1:0] STACK_ADDR_r ;
reg [DATA_SIZE-1:0] mem_r [0:STACK_MEM_SIZE-1] /* synthesis preserve */;
reg stack_full_r /* synthesis preserve */;
reg stack_empty_r /* synthesis preserve */;

always @(posedge CLK or negedge RSTN)
begin
    if (!RSTN)
    begin
        DATA_RD_r <= '0;
        STACK_ADDR_r <= '0;
        stack_full_r <= 1'b0;
        stack_empty_r <= 1'b1;  // Stack is empty on reset
    end      
    else
    begin
        if (W && !stack_full_r)  // Only write if not full
        begin
            mem_r[STACK_ADDR_r] <= DATA_WR;
            STACK_ADDR_r <= STACK_ADDR_r + 1;
            stack_empty_r <= 1'b0;
            stack_full_r <= (STACK_ADDR_r == STACK_MEM_SIZE-2);  // Will be full after this write
        end
        else if (R && !stack_empty_r)  // Only read if not empty
        begin
            DATA_RD_r <= mem_r[STACK_ADDR_r-1];
            STACK_ADDR_r <= STACK_ADDR_r - 1;
            stack_full_r <= 1'b0;
            stack_empty_r <= (STACK_ADDR_r == 1);  // Will be empty after this read
        end
    end 
end

assign DATA_RD = DATA_RD_r;
assign stack_full = stack_full_r;
assign stack_empty = stack_empty_r;
endmodule