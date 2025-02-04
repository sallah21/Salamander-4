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
    parameter ADDR_SIZE = 4,
    parameter STACK_SIZE = 8
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
  
  always @( posedge clk or negedge rstn )
  begin
    if (!rstn)
    begin
      curr_state <= FETCH;
      next_state <= FETCH;
      PC_inc_r <= 1'b0;
      cnt_overwrite_r <= 1'b0;
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
          if (OP_CODE_r == OP_JMP)
          begin
            cnt_new_val_r <= LEFT_OPERAND_r ;
            jmp_occur_r <= 1'b1;
          end 
          else if (OP_CODE_r == OP_RTN)
          begin
            cnt_new_val_r <= PC_STACK_ADDR_r + 1; // Move to next instruction 
            rnt_occur_r <= 1'b1;
          end
          else if (MEM_OP_r == NONE)
          begin
            ALU_CE_r <= 1'b0;
            ALU_left_operand_r <= LEFT_OPERAND_r;
            ALU_right_operand_r <= RIGHT_OPERAND_r; 
          end
          else if (OP_CODE_r == OP_ST)
          begin
            case (MEM_OP_r)
            OP_REG:
            begin
              REG_FILE_ADDR_r <= RIGHT_OPERAND_r;
              REG_FILE_CE_r <= 1'b0;
            end 
            OP_MEM:
            begin
              DATA_MEM_ADDR_r <= RIGHT_OPERAND_r;
              W_data_mem_r <= 1'b0;
            end
            default:
            begin
              // Store operand directly to ACU through ALU
              ALU_left_operand_r <= LEFT_OPERAND_r;
              ALU_right_operand_r <= 'x; 
              ACC_CE_r <= 1'b0;
              ALU_CE_r <= 1'b0;
            end
            endcase
          end
          else if (OP_CODE_r == OP_LD)
          begin
            case (MEM_OP_r)
            OP_REG:
            begin
              REG_FILE_ADDR_r <= RIGHT_OPERAND_r;
              REG_FILE_CE_r <= 1'b0;
            end
            OP_MEM:
            begin
              DATA_MEM_ADDR_r <= RIGHT_OPERAND_r;
              W_data_mem_r <= 1'b0;
            end
            endcase
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
              ALU_right_operand_r <= REG_FILE_DATA_OUT_r; 
            end
            endcase  
          end
          next_state <= EXEC;
        end
        EXEC:
        begin
          if (OP_CODE_r == OP_JMP || OP_CODE_r == OP_RTN)
          begin
            cnt_overwrite_r <= 1'b1;
          end
          if (OP_CODE_r == OP_NOP)
          begin
            ALU_CE_r <= 1'b0;
            ACC_CE_r <= 1'b0;
            REG_FILE_CE_r <= 1'b0;
            W_data_mem_r <= 1'b0;
          end 
          else if (MEM_OP_r == NONE)
          begin
            ALU_CE_r <= 1'b1;
            ACC_CE_r <= 1'b0;
          end 
          else if (OP_CODE_r == OP_ST)
          begin
            case (MEM_OP_r)
            OP_REG:
            begin
              REG_FILE_DATA_IN_r <= LEFT_OPERAND_r;
              REG_FILE_CE_r <= 1'b1;
            end 
            OP_MEM:
            begin
              DATA_MEM_WR_r <= LEFT_OPERAND_r;
              W_data_mem_r <= 1'b1;
            end
            default:
            begin
              // Store operand directly to ACU through ALU
              ALU_CE_r <= 1'b1;
              ACC_CE_r <= 1'b1;
            end
            endcase
          end 
          else if (OP_CODE_r == OP_LD)
            begin 
              ALU_CE_r <= 1'b1;
              ACC_CE_r <= 1'b1;
              case (MEM_OP_r)
              OP_REG:
              begin
                ALU_right_operand_r <= REG_FILE_DATA_OUT_r;
              end
              OP_MEM:
              begin
                ALU_right_operand_r <= DATA_MEM_RD_r;
              end
              endcase
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
          next_state <= FETCH;
          if (jmp_occur_r)
          begin
            PC_inc_r <= 1'b0;  
            jmp_occur_r <= 1'b0;
          end
          else if (rnt_occur_r)
          begin
            PC_inc_r <= 1'b0;  
            rnt_occur_r <= 1'b0;
          end
          else begin
            PC_inc_r <= 1'b1;  
          end 
          if (OP_CODE_r == OP_JMP || OP_CODE_r == OP_RTN)
          begin
            cnt_overwrite_r <= 1'b0;
          end
          else if (MEM_OP_r == NONE)
          begin
            ALU_CE_r <= 1'b1;
            ACC_CE_r <= 1'b1;
          end
          else if (OP_CODE_r == OP_ST)
          begin
            case (MEM_OP_r)
            OP_REG:
            begin
              REG_FILE_CE_r <= 1'b0;
            end 
            OP_MEM:
            begin
              W_data_mem_r <= 1'b0;
            end
            default:
            begin
              // Store operand directly to ACU through ALU
              ALU_CE_r <= 1'b0;
              ACC_CE_r <= 1'b0;
            end
            endcase
          end
          else if (OP_CODE_r == OP_LD)
          begin
            ACC_CE_r <= 1'b0;
            ALU_CE_r <= 1'b0;
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
  reg jmp_occur_r = 0; // There was a jump instruction
  reg rnt_occur_r = 0; // There was a return instruction
  ///////////////////////////////////////////////////////////////////////////////////////
  // Program Counter logic
  ///////////////////////////////////////////////////////////////////////////////////////

  localparam PC_SIZE = 5;
  reg [PC_SIZE-1:0] PC_ADDR_r;
  reg max_size_reached_r;
  logic PC_inc_w;
  assign PC_inc_w = PC_inc_r && (curr_state == WRITE_BACK);
  reg [PC_SIZE-1:0] cnt_new_val_r;
  reg cnt_overwrite_r;

  PC  #(
        .SIZE(5)
      )
      PC_inst
      (
        .clk(clk),
        .rstn(rstn),
        .inc(PC_inc_w),
        .cnt_overwrite(cnt_overwrite_r),
        .cnt_new_val(cnt_new_val_r),
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
  //////////////////////////////////////////////////////////////////////////////////////
  // Stack  logic
  ///////////////////////////////////////////////////////////////////////////////////////

  reg [ADDR_SIZE-1:0] PC_STACK_ADDR_r;
  wire PC_STACK_W_w = (curr_state == EXEC && next_state == EXEC && OP_CODE_r == OP_JMP) ? 1'b1 : 1'b0;
  wire PC_STACK_R_w = (curr_state == DECODE && next_state == DECODE && OP_CODE_r == OP_RTN) ? 1'b1 : 1'b0;

  STACK #(
           .DATA_SIZE(DATA_SIZE),
           .STACK_SIZE(STACK_SIZE)
    ) STACK_inst (
           .CLK(clk),
           .RSTN(rstn),
           .W(PC_STACK_W_w),
           .R(PC_STACK_R_w),
           .DATA_WR(PC_ADDR_r),
           .DATA_RD(PC_STACK_ADDR_r)
    );
endmodule
