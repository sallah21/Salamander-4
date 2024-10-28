
typedef enum logic [1:0] {
    IDLE,                 
    FETCH,                
    DECODE,
    EXEC,
    WRITE_BACK
} state_t;

module CPU_toplevel #(
    parameter SIZE = 8
) (
   input clk,
   input rstn,
   
);

state_t curr_state;
state_t next_state;

always_ff @( posedge clk or negedge rstn ) begin 
    if (!rstn) begin
        curr_state <= IDLE;
        next_state <= IDLE;
    end
    else begin
        case (curr_state)
            IDLE: begin 
                
            end 
            default: begin ;
                curr_state <= IDLE;
                next_state <= IDLE;
            end 
        endcase
    end 
end

///////////////////////////////////////////////////////////////////////////////////////
// Instantions
///////////////////////////////////////////////////////////////////////////////////////

logic unused_signals_w;

///////////////////////////////////////////////////////////////////////////////////////
// Program Counter logic
///////////////////////////////////////////////////////////////////////////////////////

localparam PC_SIZE =5;
reg [PC_SIZE-1:0] PC_ADDR_r;
reg max_size_reached_r;

PC  #(
    .SIZE(5)
    )
    PC_inst
(
    .clk(clk),
    .rstn(rstn),
    .inc(unused_signals_w),/// TODO: CONNECT IT 
    .cnt_val(PC_ADDR_r),
    .max_size_reached(max_size_reached_r)
);

///////////////////////////////////////////////////////////////////////////////////////
// Program Memory logic
///////////////////////////////////////////////////////////////////////////////////////

localparam DATA_SIZE = 6;
localparam ADDR_SIZE = 5;

reg [ADDR_SIZE-1:0] PROG_MEM_INSTRUCTION_r;

PROG_MEM #(
    .DATA_SIZE(DATA_SIZE),
    .ADDR_SIZE(ADDR_SIZE)
) PROG_MEM_inst
(
    .clk(clk),
    .rstn(rstn),
    .ADDR(PC_ADDR_r),
    .DATA(PROG_MEM_INSTRUCTION_r)
);

///////////////////////////////////////////////////////////////////////////////////////
// Instruction Decoder logic
///////////////////////////////////////////////////////////////////////////////////////

logic [2:0] OP_CODE_w;
logic [1:0] ADDR_w; 
logic       ACC_CE_w;
    
ID ID_inst
(
    .INSTR(PROG_MEM_INSTRUCTION_r),
    .OP_CODE(OP_CODE_w),
    .ADDR(ADDR_w), 
    .ACC_CE(ACC_CE_w)
);

///////////////////////////////////////////////////////////////////////////////////////
// Arithmetical Logical Unit logic
///////////////////////////////////////////////////////////////////////////////////////

reg carry_out_r;
logic [SIZE-1:0] ALU_op_out_w;

ALU #(
    .SIZE(SIZE)
) ALU_inst 
(
    .CE(ACC_CE_w), // TODO: check if its good or dumb
    .OP_CODE(OP_CODE_w), 
    .left_operand(ALU_out_val_w),
    .right_operand(), // TODO: Create and connect register file 
    .carry_out(carry_out_r), // TODO: Sequential logic for handling carry out and new carry in  
    .op_out(ALU_op_out_w),  
);

//////////////////////////////////////////////////////////////////////////////////////
// Accumulator logic
///////////////////////////////////////////////////////////////////////////////////////
logic ALU_out_val_w;
ACU #(
    .SIZE(SIZE)
) ACU_inst (
    .clk(clk),
    .rstn(rstn),
    .CE(ACC_CE_w), // TODO: Verify usage of this port 
    .in_val(ALU_op_out_w),
    .out_val (ALU_out_val_w)
);
endmodule