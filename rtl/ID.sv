/**
    Instruction decoder module
*/

module ID (
    input [5:0] INSTR,
    output [2:0] OP_CODE,
    output [1:0] ADDR, 
    output      ACC_CE,
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


assign ADDR = INSTR[1:0];
assign OP_CODE = INSTR [4:2];
assign ACC_CE = INSTR [5];
    
endmodule