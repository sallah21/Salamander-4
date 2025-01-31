`timescale 1ns / 1ps
typedef enum logic [1:0] {
          FETCH,
          DECODE,
          EXEC,
          WRITE_BACK
        } state_t;

module top_level #(
    parameter SIZE = 8,
    parameter DATA_SIZE = 6,
    parameter ADDR_SIZE = 5
  ) (
    input clk,
    input rstn,
    input W,
    input [DATA_SIZE-1:0] DATA_WR,
    input [ADDR_SIZE-1:0] ADDR
  );
  state_t curr_state /* synthesis preserve */;
  state_t next_state /* synthesis preserve */;
  // ===============================================
  // Processor State Descriptions
  // ===============================================
  //
  // FETCH:
  // -----------------------------------------------
  // Description: This state fetches the next instruction from memory.
  //
  // Entry Conditions:
  //   - Triggered after a reset or the completion of the previous instruction.
  //
  // Actions Taken:
  //   - Loads the instruction pointed to by the program counter (PC) into the instruction register (IR).
  //   - Increments the program counter (PC) to point to the next instruction.
  //
  // Exit Conditions:
  //   - Once the instruction is fetched and stored in IR.
  //
  // Next State:
  //   - DECODE
  //
  // Additional Notes:
  //   - This state is critical for keeping the instruction pipeline flowing.
  // ===============================================
  //
  // DECODE:
  // -----------------------------------------------
  // Description: This state decodes the fetched instruction and prepares for execution.
  //
  // Entry Conditions:
  //   - Triggered upon completion of the FETCH state.
  //
  // Actions Taken:
  //   - Decodes the opcode and operands in IR.
  //   - Sets up control signals for the next operation based on the opcode.
  //
  // Exit Conditions:
  //   - Once the instruction is decoded and control signals are prepared.
  //
  // Next State:
  //   - EXEC
  //
  // Additional Notes:
  //   - Control signals set here will guide the ALU or memory access in the EXEC phase.
  // ===============================================

  always @( posedge clk or negedge rstn )
  begin
    if (!rstn)
    begin
      curr_state <= FETCH;
      next_state <= FETCH;
    end
    else
    begin
      curr_state <= next_state;
      case (curr_state)
        FETCH:
        begin
          if (max_size_reached_r != 1'b1)
          begin
            PC_inc_w <= 1'b1;
            ID_CE_w <= 1'b0;
          end
          next_state <= DECODE;
        end

        DECODE:
        begin
          PC_inc_w <= 1'b0;
          ID_CE_w <= 1'b1;
          OP_CODE_latch <= OP_CODE_w;
          ADDR_latch <= ADDR_w;
          ACC_CE_latch <= ACC_CE_w;
          CE_latch <= CE_w;
          next_state <= EXEC;
        end
        EXEC:
        begin
          PC_inc_w <= 1'b0;
          ID_CE_w <= 1'b0;
          next_state <= WRITE_BACK; 
        end
        WRITE_BACK:
        begin
          PC_inc_w <= 1'b0;
          ID_CE_w <= 1'b0;
          next_state <= FETCH;
        end
        default:
        begin
          curr_state <= FETCH;
          next_state <= FETCH;
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

  localparam PC_SIZE = 5;
  reg [PC_SIZE-1:0] PC_ADDR_r;
  reg [PC_SIZE-1:0] PC_inc_valr=5'b00001;
  reg max_size_reached_r;
  logic PC_inc_w;
  PC  #(
        .SIZE(5)
      )
      PC_inst
      (
        .clk(clk),
        .rstn(rstn),
        .inc(PC_inc_w),
        .inc_val(PC_inc_valr),
        .cnt_val(PC_ADDR_r), // Memory address
        .max_size_reached(max_size_reached_r)
      );

  ///////////////////////////////////////////////////////////////////////////////////////
  // Program Memory logic
  ///////////////////////////////////////////////////////////////////////////////////////
  reg [DATA_SIZE-1:0] PROG_MEM_INSTRUCTION_r;
  wire [ADDR_SIZE-1:0] PC_ADDR_w;
  assign PC_ADDR_w = (W) ? ADDR : PC_ADDR_r;
  PROG_MEM #(
             .DATA_SIZE(DATA_SIZE),
             .ADDR_SIZE(ADDR_SIZE)
           ) PROG_MEM_inst
           (
             .clk(clk),
             .rstn(rstn),
             .W(W), // Memory write on high
             .ADDR(PC_ADDR_w), // Input memory address
             .DATA_WR(DATA_WR), // Input instruction data
             .DATA(PROG_MEM_INSTRUCTION_r) // Output instruction data
           );

  ///////////////////////////////////////////////////////////////////////////////////////
  // Instruction Decoder logic
  ///////////////////////////////////////////////////////////////////////////////////////

  logic [2:0] OP_CODE_latch;
  logic [1:0] ADDR_latch;
  logic       ACC_CE_latch;
  logic [3:0] CE_latch;

  logic [2:0] OP_CODE_w;
  logic [1:0] ADDR_w;
  logic       ACC_CE_w;
  logic [3:0] CE_w;
  logic        ID_CE_w ;
  logic [5:0]  INSTR_w;
  ID ID_inst
     (
       .INSTR(INSTR_w),
       .ID_CE(ID_CE_w),
       .OP_CODE(OP_CODE_w),
       .ADDR(ADDR_w),
       .CE(CE_w),
       .ACC_CE(ACC_CE_w)
     );

  ///////////////////////////////////////////////////////////////////////////////////////
  // Arithmetical Logical Unit logic
  ///////////////////////////////////////////////////////////////////////////////////////

  reg carry_out_r;
  logic [SIZE-1:0] ALU_op_out_w;
  wire [7:0] ALU_left_operand_w;
  wire [7:0] ALU_right_operand_w;
  ALU #(
        .SIZE(SIZE)
      ) ALU_inst
      (
        .CE(ACC_CE_w), 
        .OP_CODE(OP_CODE_latch),
        .left_operand(ALU_left_operand_w),
        .right_operand(ALU_right_operand_w),
        .carry_in(carry_out_r), 
        .carry_out(carry_out_r),
        .op_out(ALU_op_out_w)
      );

  assign ALU_left_operand_w = ALU_out_val_w;
  assign ALU_right_operand_w = REG_FILE_DATA_OUT_w;
  
  //////////////////////////////////////////////////////////////////////////////////////
  // Accumulator logic
  ///////////////////////////////////////////////////////////////////////////////////////
  wire [7:0] ALU_out_val_w;
  ACU #(
        .SIZE(SIZE)
      ) ACU_inst (
        .clk(clk),
        .rstn(rstn),
        .CE(ACC_CE_latch), // TODO: Verify usage of this port
        .in_val(ALU_op_out_w),
        .out_val (ALU_out_val_w)
      );


  //////////////////////////////////////////////////////////////////////////////////////
  // Register File  logic
  ///////////////////////////////////////////////////////////////////////////////////////

  wire [7:0] REG_FILE_DATA_OUT_w;
  
  REG_FILE  REG_FILE_inst (
              .CLK(clk),
              .RSTN(rstn),
              .ADDR(ADDR_latch),
              .CE(CE_latch),
              .DATA_IN(ALU_op_out_w),
              .DATA_OUT (REG_FILE_DATA_OUT_w)
            );

endmodule
