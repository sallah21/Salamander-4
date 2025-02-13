`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// ID (Instruction Decoder) Module
//
// Description:
// This module decodes 16-bit instruction words into their constituent fields for
// CPU execution. It breaks down each instruction into operation codes, memory
// operations, and operands. The decoder is purely combinational, providing
// immediate decoding of instruction fields.
//
// Features:
// - 16-bit instruction word decoding
// - Multiple field extraction
// - Combinational logic design
// - Support for ALU and memory operations
//
// Instruction Format (16 bits):
// +--------+--------+--------+--------+--------+
// | 15-12  | 11-8   | 7-4    | 3-0    |
// +--------+--------+--------+--------+--------+
// | OP_CODE| MEM_OP | LEFT   | RIGHT  |
// |        |        | OPERAND| OPERAND|
// +--------+--------+--------+--------+--------+
//
// Field Descriptions:
// - OP_CODE [15:12]:       ALU operation code
//   * Controls arithmetic, logic, and control operations
//   * 4 bits allowing for 16 different operations
//
// - MEM_OP [11:8]:         Memory operation code
//   * Controls memory access and register operations
//   * 4 bits for memory operation types
//
// - OPERAND [7:0]:         Combined operand field
//   * Split into LEFT_OPERAND and RIGHT_OPERAND
//   * Used for register addresses or immediate values
//
// - LEFT_OPERAND [7:4]:    Destination operand
//   * Usually represents destination register
//   * Used in memory and register operations
//
// - RIGHT_OPERAND [3:0]:   Source operand
//   * Usually represents source register
//   * Used in memory and register operations
//
// Ports:
// Inputs:
// - INSTR:         16-bit instruction word
// - ID_CE:         Instruction decoder chip enable
//
// Outputs:
// - OP_CODE:       4-bit ALU operation code
// - MEM_OP:        4-bit memory operation code
// - OPERAND:       8-bit combined operand field
// - LEFT_OPERAND:  4-bit destination operand
// - RIGHT_OPERAND: 4-bit source operand
//
// Note: All outputs are combinational and directly mapped
// from the instruction word bits
//////////////////////////////////////////////////////////////////////////////////

module ID 
(
    input  [15:0] INSTR,          // Instruction word input
    input         ID_CE,          // Chip enable
    output [3:0]  OP_CODE,        // ALU operation code
    output [3:0]  MEM_OP,         // Memory operation code
    output [7:0]  OPERAND,        // Combined operand field
    output [3:0]  LEFT_OPERAND,   // Destination operand
    output [3:0]  RIGHT_OPERAND   // Source operand
);

    // Internal signals
    logic [3:0] OP_CODE_r, MEM_OP_r;
    logic [7:0] OPERAND_r;
    logic [3:0] LEFT_OPERAND_r, RIGHT_OPERAND_r;

    always_comb begin
        if (ID_CE) begin
            OP_CODE_r <= INSTR[15:12];        // Extract operation code
            MEM_OP_r <= INSTR[11:8];          // Extract memory operation
            OPERAND_r <= INSTR[7:0];          // Extract full operand field
        end
    end 

    // Direct bit field assignments
    assign OP_CODE = OP_CODE_r;        // Extract operation code
    assign MEM_OP = MEM_OP_r;          // Extract memory operation
    assign OPERAND = OPERAND_r;          // Extract full operand field
    assign LEFT_OPERAND = OPERAND[7:4];    // Extract destination operand
    assign RIGHT_OPERAND = OPERAND[3:0];   // Extract source operand

endmodule
