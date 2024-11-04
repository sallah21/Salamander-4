`timescale 1ns / 1ps
/**
    Instruction decoder module
*/

// `include "OP_CODES.sv"

module ID (
    input [5:0] INSTR,
    input       ID_CE,
    output [2:0] OP_CODE,
    output [1:0] ADDR, 
    output [3:0] CE,
    output      ACC_CE
);
/*
 * Instrction content Description:
 * 
 * +--------+---------------------------------------------+
 * | Bit(s) | Description                                 |
 * +--------+---------------------------------------------+
 * | [0-1]  | ADDR - Register file address                |
 * | [2-4]  | OP_CODE - Operation code for ALU            |
 * | [5]    | ACC_CE - Accumulator chip enable            |
 * +--------+---------------------------------------------+
 * 
 */

logic [3:0] CE_w;

 always @(*) begin
    case (INSTR [4:2])
    OP_ST: begin 
        case(INSTR[1:0]) 
            2'b00: begin
                CE_w <= 4'b0001;
            end 
            2'b01: begin
                CE_w<= 4'b0010;
            end 
            2'b10: begin
                CE_w <= 4'b0100;
            end 
            2'b11: begin
                CE_w<= 4'b1000;
            end 
            default: begin
                CE_w<= 4'b0000;
            end 
        endcase 
    end 
    default: begin
        CE_w<= 4'b0000;
    end 
    endcase 
 end 

assign CE = (ID_CE) ? CE_w : 4'b0000;
assign ADDR = (ID_CE) ? INSTR[1:0] : 2'bzz;
assign OP_CODE = (ID_CE) ? INSTR [4:2] : 3'bzzz;
assign ACC_CE = (ID_CE)? INSTR [5] : 1'bz;
    
endmodule