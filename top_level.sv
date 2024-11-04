
typedef enum logic [1:0] {
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

  always_ff @( posedge clk or negedge rstn )
  begin
    if (!rstn)
    begin
      curr_state <= FETCH;
      next_state <= FETCH;
    end
    else
        curr_state <= next_state;
    begin
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
          next_state <= FETCH; // ??? There wil be more states or nah ?
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
  reg max_size_reached_r;
  wire PC_inc_w;
  PC  #(
        .SIZE(5)
      )
      PC_inst
      (
        .clk(clk),
        .rstn(rstn),
        .inc(PC_inc_w),
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

  logic [2:0] OP_CODE_latch;
  logic [1:0] ADDR_latch;
  logic       ACC_CE_latch;
  logic [3:0] CE_latch;

  logic [2:0] OP_CODE_w;
  logic [1:0] ADDR_w;
  logic       ACC_CE_w;
  logic [3:0] CE_w;
  wire        ID_CE_w ;
  ID ID_inst
     (
       .INSTR(PROG_MEM_INSTRUCTION_r),
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

  ALU #(
        .SIZE(SIZE)
      ) ALU_inst
      (
        .CE(ACC_CE_w), // TODO: check if its good or dumb
        .OP_CODE(OP_CODE_latch),
        .left_operand(ALU_out_val_w),
        .right_operand(REG_FILE_DATA_OUT_w),
        .carry_in(carry_out_r), // TODO: Check this wiring  
        .carry_out(carry_out_r),
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


  //////////////////////////////////////////////////////////////////////////////////////
  // Register File  logic
  ///////////////////////////////////////////////////////////////////////////////////////

  wire [7:0] REG_FILE_DATA_OUT_w;

  REG_FILE  REG_FILE_inst (
              .CLK(clk),
              .RSTN(rstn),
              .ADDR(ADDR_w),
              .CE(CE_w),
              .DATA_IN(ALU_op_out_w),
              .DATA_OUT (REG_FILE_DATA_OUT_w)
            );

endmodule
