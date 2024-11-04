/**
    Arithmetical Logical Unit module
*/

// `include "OP_CODES.sv"


// TODO: verify ALU work logic for bugs 
module ALU #(
    parameter SIZE = 8 
) (
    input CE,
    input [2:0] OP_CODE, // 3-bit code for operation
    input [SIZE-1:0] left_operand,
    input [SIZE-1:0] right_operand, 
    input carry_in,
    output carry_out,
    output [SIZE-1:0] op_out
);

    logic carry_out_w;
    logic [SIZE-1:0] op_out_w;

    always_comb begin
        carry_out_w = 0;
        op_out_w = '0;

        if (CE) begin
            case (OP_CODE)
                OP_ADD: {carry_out_w, op_out_w} = left_operand + right_operand + carry_in;
                OP_SUB: {carry_out_w, op_out_w} = left_operand - right_operand + carry_in;
                OP_AND: op_out_w = left_operand & right_operand;
                OP_OR:  op_out_w = left_operand | right_operand;
                OP_XOR: op_out_w = left_operand ^ right_operand;
                OP_NOT: op_out_w = ~left_operand;
                OP_LD:  op_out_w = right_operand;
                OP_ST:  op_out_w = left_operand;
                default: op_out_w = 'z; 
            endcase
        end
    end

    assign carry_out = carry_out_w;
    assign op_out = op_out_w;

endmodule