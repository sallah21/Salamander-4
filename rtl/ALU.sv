`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// ALU (Arithmetic Logic Unit) Module
//
// Description:
// This module implements a multi-function arithmetic and logic unit that performs
// various operations including arithmetic (ADD, SUB, INC, DEC), logical (AND, OR,
// XOR, NOT), and shift operations (SHL, SHR). It also supports basic data movement
// operations (LD, ST) and control operations (HLT, JMP, RTN, NOP).
//
// Features:
// - Parameterized data width
// - Multiple operation support (16 operations)
// - Carry handling for arithmetic operations
// - Combinational logic design
//
// Parameters:
// - SIZE: Width of operands and result (default: 8)
//
// Ports:
// Inputs:
// - CE:            Chip Enable, active high
// - OP_CODE:       4-bit operation selector [3:0]
// - left_operand:  First input operand [SIZE-1:0]
// - right_operand: Second input operand [SIZE-1:0]
// - carry_in:      Carry input for arithmetic operations
//
// Outputs:
// - zero_flag:     Set when result is zero
// - carry_out:     Carry output from arithmetic operations
// - op_out:        Operation result [SIZE-1:0]
//
// Operations:
// Arithmetic:
// - OP_ADD: out = left + right + carry_in
// - OP_SUB: out = left - right - carry_in
// - OP_INC: out = left + 1
// - OP_DEC: out = left - 1
//
// Logical:
// - OP_AND: out = left & right
// - OP_OR:  out = left | right
// - OP_XOR: out = left ^ right
// - OP_NOT: out = ~left
//
// Shifts:
// - OP_SHL: out = left << 1
// - OP_SHR: out = left >> 1
//
// Data Movement:
// - OP_LD: out = right_operand
// - OP_ST: out = left_operand
//
// Control:
// - OP_HLT: Halt operation (output undefined)
// - OP_JMP: Jump operation (output undefined)
// - OP_RTN: Return operation (output undefined)
// - OP_NOP: No operation (output undefined)
//
// Notes:
// - All operations are combinational
// - Control operations (HLT, JMP, RTN, NOP) set outputs to 'x'
// - Zero flag is updated for arithmetic operations
//////////////////////////////////////////////////////////////////////////////////

module ALU #(
    parameter SIZE = 8                    // Width of operands and result
  ) (
    input CE,                            // Chip enable
    input [3:0] OP_CODE,                 // Operation selector
    input [SIZE-1:0] left_operand,       // First operand
    input [SIZE-1:0] right_operand,      // Second operand
    input carry_in,                      // Carry input
    output zero_flag,                    // Zero result flag
    output carry_out,                    // Carry output
    output [SIZE-1:0] op_out            // Operation result
  );

  // Internal signals
  logic carry_out_w;                     // Internal carry output
  logic [SIZE-1:0] op_out_w;            // Internal operation result


  // Main operation logic
  always @(*)
  begin
    carry_out_w = 0;                     // Default carry out
    op_out_w = 1'b0;                     // Default output

    if (CE)
    begin
      // Operation decoder
      case (OP_CODE)
        // Arithmetic Operations
        OP_ADD:
        begin
          {carry_out_w, op_out_w} <= left_operand + right_operand + carry_in;
        end 
        OP_SUB:
        begin
          {carry_out_w, op_out_w} <= left_operand - right_operand - carry_in;
        end 
        
        // Logical Operations
        OP_AND:
        begin
          op_out_w <= left_operand & right_operand;
        end 
        OP_OR:
        begin
          op_out_w <= left_operand | right_operand;
        end 
        OP_XOR:
        begin
          op_out_w <= left_operand ^ right_operand;
        end 
        OP_NOT:
        begin
          op_out_w <= ~left_operand;
        end 
        
        // Data Movement Operations
        OP_LD:
        begin
          op_out_w <= right_operand;
        end
        OP_ST:
        begin
          op_out_w <= left_operand;
        end
        
        // Increment/Decrement Operations
        OP_INC:
        begin
          op_out_w <= left_operand + {{(SIZE-1){1'b0}}, 1'b1};
        end 
        OP_DEC:
        begin
          op_out_w <= left_operand - {{(SIZE-1){1'b0}}, 1'b1};
        end 
        
        // Shift Operations
        OP_SHL:
        begin
          op_out_w <= left_operand << 1;
        end 
        OP_SHR:
        begin
          op_out_w <= left_operand >> 1;
        end 
        
        // Control Operations (No ALU usage)
        OP_HLT:
        begin
          {carry_out_w, op_out_w} <= 'x;
        end
        OP_JMP:
        begin
          {carry_out_w, op_out_w} <= 'x;
        end
        OP_RTN:
        begin
          {carry_out_w, op_out_w} <= 'x;
        end
        OP_NOP:
        begin
          {carry_out_w, op_out_w} <= 'x;
        end 
        default:
        begin
          {carry_out_w, op_out_w} <= 'x;
        end
      endcase
    end
  end

  // Output assignments
  assign carry_out = carry_out_w;        // Propagate carry
  assign op_out = op_out_w;             // Propagate result


`ifdef FORMAL

  //////////////////////////////////////////////////////////////////////////////////////////
  ///////////// Assertions
  //////////////////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////////////////
  // Asstertion 1: Alu output is stable when CE is low
  //////////////////////////////////////////////////////////////////////////////////////////
  property ALU_stable_when_CE_is_low;
    @($fell(CE))
     until ($rose(CE))
     ($stable(op_out)&& $stable(carry_out));
  endproperty

  assert ALU_stable_when_CE_is_low else
           $display("ALU is not stable when CE is low");

  //////////////////////////////////////////////////////////////////////////////////////////
  // Asstertion 2: Alu output changes when CE is high
  //////////////////////////////////////////////////////////////////////////////////////////
  property output_changes_when_CE_is_high;
    @($rose(CE))
     until ($fell(CE))
     ($changed(op_out));
  endproperty

  assert output_changes_when_CE_is_high else
           $display("ALU output does not change when CE is high");

  //////////////////////////////////////////////////////////////////////////////////////////
  // Asstertion 3: Result lower than MAX_VAL
  //////////////////////////////////////////////////////////////////////////////////////////
  localparam MAX_VAL = 8'b11111111;
  property result_lower_than_MAX_VAL;
    @($rose(CE))
     until ($fell(CE))
     (op_out < MAX_VAL);
  endproperty

  assert result_lower_than_MAX_VAL else
           $display("ALU result is greater than MAX_VAL");

`endif
endmodule
