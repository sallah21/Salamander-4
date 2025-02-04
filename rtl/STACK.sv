`timescale 1ns / 1ps
/**
    Stack module
*/

module STACK #(
    parameter DATA_SIZE = 4,
    parameter STACK_SIZE = 5
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
reg [STACK_SIZE-1:0] STACK_ADDR_r;
reg [DATA_SIZE-1:0] mem_r [STACK_MEM_SIZE-1:0];
reg stack_full_r;
reg stack_empty_r;

always @(posedge CLK or negedge RSTN)
begin
    if (!RSTN)
    begin
        DATA_RD_r <= 0;
        STACK_ADDR_r <= 0;
        stack_full_r <= 1'b0;
        for (int i = 0; i < STACK_MEM_SIZE; i++)
        begin
            mem_r[i] <= 'x;
        end
    end      
    else
    begin
        if (W)
        begin
            if (STACK_ADDR_r == STACK_MEM_SIZE-1)
            begin
                stack_full_r <= 1'b1;
            end 
            else 
            begin
                stack_full_r <= 1'b0;
                mem_r[STACK_ADDR_r] <= DATA_WR;
                STACK_ADDR_r <= STACK_ADDR_r + 1;
            end
        end
        else if (R)
        begin
            if (STACK_ADDR_r == 0) 
            begin 
                DATA_RD_r <= 'x;
                stack_empty_r <= 1'b1;
            end        
            else 
            begin
            stack_empty_r <= 1'b0;
            DATA_RD_r <= mem_r[STACK_ADDR_r-1];
            STACK_ADDR_r <= STACK_ADDR_r - 1;
            end
        end
    end 
end

assign DATA_RD = DATA_RD_r;
assign stack_full = stack_full_r;
assign stack_empty = stack_empty_r;
endmodule