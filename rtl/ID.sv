`timescale 1ns / 1ps
/**
    Instruction decoder module
*/

module ID 
(
    input  [15:0] INSTR,
    input        ID_CE,
    output [3:0] OP_CODE,
    output [3:0] MEM_OP,
    output [7:0] OPERAND,
    output [3:0] LEFT_OPERAND, // Destination in MEM OP
    output [3:0] RIGHT_OPERAND // Source in MEM OP
  );

  /*
   * Instrction content Description:
   * 
   * +--------+---------------------------------------------+
   * | Bit(s) | Description                                 |
   * +--------+---------------------------------------------+
   * | [0-3]  | OP_CODE - Operation code for ALU. 4 bit     |
   * | [4-7]  | MEM_OP - Memory operation. 4 bit            |
   * | [8-15] | OPERAND - Accumulator chip enable. 8 bit    |
   * +--------+---------------------------------------------+
   * 
   */


assign OP_CODE = INSTR[15:12];
assign MEM_OP = INSTR[11:8];
assign OPERAND = INSTR[7:0];
assign LEFT_OPERAND = OPERAND[7:4] ;
assign RIGHT_OPERAND = OPERAND[3:0];

endmodule
