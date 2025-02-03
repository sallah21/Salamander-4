`timescale 1ns / 1ps
typedef enum logic [1:0] {
          FETCH=2'b00,
          DECODE=2'b01,
          EXEC=2'b10,
          WRITE_BACK=2'b11
        } state_t;

module top_level #(
    parameter SIZE = 8,
    parameter DATA_SIZE = 8,
    parameter ADDR_SIZE = 4
  ) (
    input clk,
    input rstn,
    input W,
    input OVERWRITE,
    input [DATA_SIZE-1:0] DATA_WR,
    input [ADDR_SIZE-1:0] ADDR
  );
  state_t curr_state /* synthesis preserve */;
  state_t next_state /* synthesis preserve */;
  logic PC_inc_r;  // Register to control PC increment
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
      PC_inc_r <= 1'b0;
    end
    else
    begin
      if (!W)
      begin
        curr_state <= next_state;
      end
      case (curr_state)
        FETCH:
        begin
          if (max_size_reached_r != 1'b1)
          begin
            PC_inc_r <= 1'b0;
          end
          ID_CE_r <= 1'b1;
          ACC_CE_r <= 1'b0;
          next_state <= DECODE;
        end
        DECODE:
        begin
          PC_inc_r <= 1'b0;
          ID_CE_r <= 1'b0;
          if (MEM_OP_r == NONE)
          begin
            ALU_CE_r <= 1'b0;
            ALU_left_operand_r <= LEFT_OPERAND_r;
            ALU_right_operand_r <= RIGHT_OPERAND_r; 
          end
          else 
          begin
            case (MEM_OP_r)
            REG_TO_REG:
            begin
              // Change addres of register in register file to get data out
              REG_FILE_ADDR_r <= RIGHT_OPERAND_r;
              REG_FILE_CE_r <= 1'b0;
            end
            REG_TO_MEM:
            begin
              // Privide right operand as addres to register disable write on RF  
              REG_FILE_ADDR_r <= RIGHT_OPERAND_r;
              REG_FILE_CE_r <= 1'b0;
              DATA_MEM_ADDR_r <= LEFT_OPERAND_r;
            end
            MEM_TO_REG:
            begin
              DATA_MEM_ADDR_r <= RIGHT_OPERAND_r;
              REG_FILE_ADDR_r <= LEFT_OPERAND_r;
              REG_FILE_CE_r <= 1'b0;
            end
            MEM_TO_MEM:
            begin
              // Provide right operand as addres to data memory
              DATA_MEM_ADDR_r <= RIGHT_OPERAND_r;
              W_data_mem_r <= 1'b0;
            end
            default:
            begin
              ALU_left_operand_r <= ACU_out_val_w;
              ALU_right_operand_r <= REG_FILE_DATA_OUT_r; // TODO: imo not default but stays for now 
            end
            endcase  
          end

          next_state <= EXEC;
        end
        EXEC:
        begin
          if (MEM_OP_r == NONE)
          begin
            ALU_CE_r <= 1'b1;
            ACC_CE_r <= 1'b0;
          end 
          else
          begin
            case (MEM_OP_r)
            REG_TO_REG:
            begin
              // Change addres of register to new register, provide output as input and enable write
              REG_FILE_DATA_IN_r <= REG_FILE_DATA_OUT_r;
              REG_FILE_ADDR_r <= LEFT_OPERAND_r;
              REG_FILE_CE_r <= 1'b1;
            end
            REG_TO_MEM:
            begin
              // Enable write on data memory and provide output of register file  as input to memory
              W_data_mem_r <= 1'b1;
              DATA_MEM_WR_r <= REG_FILE_DATA_OUT_r;
              DATA_MEM_ADDR_r <= LEFT_OPERAND_r;
            end
            MEM_TO_REG:
            begin
              // Enable write on register file and provide output of data memory as input
              W_data_mem_r <= 1'b0;
              REG_FILE_DATA_IN_r <= DATA_MEM_RD_r;
              REG_FILE_CE_r <= 1'b1;
            end
            MEM_TO_MEM:
            begin
              // Take output of data memory and write it to another memory location
              DATA_MEM_WR_r <=DATA_MEM_RD_r;
              DATA_MEM_ADDR_r <= LEFT_OPERAND_r;
              W_data_mem_r <= 1'b1;
            end
            // default:
            // begin
  
            // end
            endcase
          end

          PC_inc_r <= 1'b0;
          next_state <= WRITE_BACK; 
        end
        WRITE_BACK:
        begin
          PC_inc_r <= 1'b1;  
          next_state <= FETCH;
          if (MEM_OP_r == NONE)
          begin
            ALU_CE_r <= 1'b1;
            ACC_CE_r <= 1'b1;
          end
          else
          begin
            case (MEM_OP_r)
            REG_TO_REG:
            begin
              // Disable write 
              REG_FILE_CE_r <= 1'b0;
            end
            REG_TO_MEM:
            begin
              // Disable write on data memory
              W_data_mem_r <= 1'b0;
            end
            MEM_TO_REG:
            begin
              // Disable write on register file
              REG_FILE_CE_r <= 1'b0;
            end
            MEM_TO_MEM:
            begin
              // Disable write on data memory
              W_data_mem_r <= 1'b0;
            end
          endcase
          end 

        end
        default:
        begin
          curr_state <= FETCH;
          next_state <= FETCH;
          PC_inc_r <= 1'b0;
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
  assign PC_inc_w = PC_inc_r && (curr_state == WRITE_BACK);

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
  wire [DATA_SIZE-1:0] PROG_MEM_DATA_w;
  assign PC_ADDR_w = (W) ? ADDR : PC_ADDR_r;
  PROG_MEM #(
             .DATA_SIZE(DATA_SIZE),
             .ADDR_SIZE(ADDR_SIZE)
           ) PROG_MEM_inst
           (
             .clk(clk),
             .rstn(rstn),
             .W(W), // Memory write on high
             .ADDR(PC_ADDR_w), // Use current PC when loading data, // Input memory address
             .DATA_WR(DATA_WR), // Input instruction data
             .DATA(PROG_MEM_DATA_w) // Output instruction data
           );


  ///////////////////////////////////////////////////////////////////////////////////////
  // Data Memory logic
  ///////////////////////////////////////////////////////////////////////////////////////

  reg W_data_mem_r;
  reg [DATA_SIZE-1:0] DATA_MEM_WR_r;
  reg [ADDR_SIZE-1:0] DATA_MEM_ADDR_r;
  reg [DATA_SIZE-1:0] DATA_MEM_RD_r;
DATA_MEM #(
             .DATA_SIZE(DATA_SIZE),
             .ADDR_SIZE(ADDR_SIZE)
           ) DATA_MEM_inst
           (
             .clk(clk),
             .rstn(rstn),
             .W(W_data_mem_r),
             .DATA_WR(DATA_MEM_WR_r),
             .ADDR(DATA_MEM_ADDR_r),
             .DATA_RD(DATA_MEM_RD_r)
);

  ///////////////////////////////////////////////////////////////////////////////////////
  // Instruction Decoder logic
  ///////////////////////////////////////////////////////////////////////////////////////

  logic [15:0] INSTR_r;
  assign INSTR_r = PROG_MEM_DATA_w;
  logic ID_CE_r;
  logic [3:0] OP_CODE_r;
  logic [3:0] MEM_OP_r;
  logic [7:0] OPERAND_r;
  logic [3:0] LEFT_OPERAND_r;
  logic [3:0] RIGHT_OPERAND_r;
  ID  ID_inst
      (
        .INSTR(INSTR_r),
        .ID_CE(ID_CE_r),
        .OP_CODE(OP_CODE_r),
        .MEM_OP(MEM_OP_r),
        .OPERAND(OPERAND_r),
        .LEFT_OPERAND(LEFT_OPERAND_r),
        .RIGHT_OPERAND(RIGHT_OPERAND_r)
      );
    
  ///////////////////////////////////////////////////////////////////////////////////////
  // Arithmetical Logical Unit logic
  ///////////////////////////////////////////////////////////////////////////////////////
  reg carry_out_r;
  reg carry_in = 1'b0;
  reg ALU_CE_r;
  logic [SIZE-1:0] ALU_op_out_w;
  reg [7:0] ALU_left_operand_r;
  reg [7:0] ALU_right_operand_r;
  // assign ALU_left_operand_w = ALU_out_val_w;
  // assign ALU_right_operand_w = REG_FILE_DATA_OUT_r;
  ALU #(
        .SIZE(SIZE)
      ) ALU_inst
      (
        .CE(ALU_CE_r), 
        .OP_CODE(OP_CODE_r),
        .left_operand(ALU_left_operand_r),
        .right_operand(ALU_right_operand_r),
        .carry_in(carry_out_r), 
        .carry_out(carry_out_r),
        .op_out(ALU_op_out_w)
      );


  
  //////////////////////////////////////////////////////////////////////////////////////
  // Accumulator logic
  ///////////////////////////////////////////////////////////////////////////////////////
  wire [7:0] ACU_out_val_w;
  reg  [7:0] ACC_in_val_r;
  assign ACC_in_val_r = ALU_op_out_w;
  reg        ACC_CE_r;
  ACU #(
        .SIZE(SIZE)
      ) ACU_inst (
        .clk(clk),
        .rstn(rstn),
        .CE(ACC_CE_r), 
        .in_val(ACC_in_val_r),
        .out_val (ACU_out_val_w)
      );


  //////////////////////////////////////////////////////////////////////////////////////
  // Register File  logic
  ///////////////////////////////////////////////////////////////////////////////////////

  wire [7:0] REG_FILE_DATA_OUT_r;
  reg  [3:0] REG_FILE_ADDR_r;
  reg  [3:0] REG_FILE_CE_r;
  reg  [7:0] REG_FILE_DATA_IN_r;
  
  REG_FILE  REG_FILE_inst (
              .CLK(clk),
              .RSTN(rstn),
              .ADDR(REG_FILE_ADDR_r),
              .CE(REG_FILE_CE_r),
              .DATA_IN(REG_FILE_DATA_IN_r),
              .DATA_OUT (REG_FILE_DATA_OUT_r)
            );

endmodule
