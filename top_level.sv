`timescale 1ns / 1ps

  //////////////////////////////////////////////////////////////////////////////////////
  // Module Description:
  // This module represents the top-level design of a simple CPU. It integrates various
  // components including:
  // - Program Counter (PC)
  // - Instruction Decoder (ID)
  // - Arithmetic Logic Unit (ALU)
  // - Accumulator (ACU)
  // - Register File
  // - Data Memory
  // - Stack
  //
  // The CPU implements a basic instruction set with operations like ADD, SUB, LD, ST,
  // JMP, and RTN. It uses a simple state machine for instruction fetch, decode, and
  // execute cycles. The design includes a stack for handling subroutine calls and
  // returns.
  //
  // State Machine Description:
  // The CPU operates in a 4-state cycle:
  //
  // 1. FETCH (2'b00):
  //    - Fetches the next instruction from program memory using PC address
  //    - Prepares for instruction decoding
  //    - PC increment is controlled based on max_size condition
  //
  // 2. DECODE (2'b01):
  //    - Decodes the fetched instruction (OP_CODE)
  //    - Sets up operands for execution
  //    - Special handling for JMP instruction:
  //      * Loads jump target address into counter
  //      * Sets jump occurrence flag
  //    - Prepares ALU and memory operations
  //
  // 3. EXECUTE (2'b10):
  //    - Performs the actual operation based on decoded instruction
  //    - ALU operations: arithmetic, logic, shifts
  //    - Memory operations: load/store
  //    - Stack operations: push/pop for subroutine calls
  //    - Updates flags and status registers
  //
  // 4. WRITE_BACK (2'b11):
  //    - Writes results back to destination (register/memory)
  //    - Updates PC for next instruction:
  //      * Normal increment for sequential execution
  //      * Jump target for JMP/RTN instructions
  //    - Handles special cases for JMP and RTN instructions
  //      by updating counter overwrite signal
  //
  // Control Signals:
  // - PC_inc_r: Controls program counter increment
  // - ACC_CE_r: Accumulator clock enable
  // - cnt_overwrite_r: Counter overwrite control for jumps
  // - jmp_occur_r: Jump occurrence flag
  //
  //////////////////////////////////////////////////////////////////////////////////////

// Definition of the state machine states
typedef enum logic [1:0] {
          FETCH=2'b00,
          DECODE=2'b01,
          EXEC=2'b10,
          WRITE_BACK=2'b11
        } state_t;

module top_level #(
    parameter SIZE = 4,
    parameter DATA_SIZE = 8,
    parameter ADDR_SIZE = 4,
    parameter STACK_SIZE = 4
  ) (
    input clk,
    input rstn,
    input W,
    input [DATA_SIZE-1:0] DATA_WR,
    input [ADDR_SIZE-1:0] ADDR,
    // Outputs for monitoring
    output [ADDR_SIZE-1:0] PC_ADDR_out,
    output [DATA_SIZE-1:0] OP_CODE_out,
    output [DATA_SIZE-1:0] OP_MEM_OUT,
    output [DATA_SIZE-1:0] LEFT_OPERAND_out,
    output [DATA_SIZE-1:0] RIGHT_OPERAND_out,
    output [DATA_SIZE-1:0] ACC_OUT,
    output [DATA_SIZE-1:0] ALU_OUT,
    output [DATA_SIZE-1:0] REG_FILE_OUT,
    output [DATA_SIZE-1:0] DATA_MEM_OUT,
    output [1:0] curr_state_out,
    output [1:0] next_state_out,
    output stack_full_out,
    output stack_empty_out
  );
  state_t curr_state /* synthesis preserve */;
  state_t next_state /* synthesis preserve */;
  logic PC_inc_r;  // Register to control PC increment


  ///////////////////////////////////////////////////////////////////////////////////////
  // Instantions
  ///////////////////////////////////////////////////////////////////////////////////////
  reg jmp_occur_r = 0 /* synthesis preserve */; // There was a jump instruction
  reg rnt_occur_r = 0 /* synthesis preserve */; // There was a return instruction
  ///////////////////////////////////////////////////////////////////////////////////////
  // Program Counter (PC) Logic
  //
  // Description:
  // The Program Counter module manages instruction address sequencing and control flow.
  // It provides the address for fetching the next instruction and handles special
  // cases like jumps and maximum program size limits.
  //
  // Parameters:
  // - PC_SIZE: Width of the program counter (4 bits, allows addressing up to 16 instructions)
  //
  // Key Signals:
  // - PC_ADDR_r:         Current program counter value/address (4-bit)
  // - max_size_reached_r: Flag indicating PC has reached maximum allowed value
  // - PC_inc_w:          Wire controlling PC increment, active only during WRITE_BACK state
  // - cnt_new_val_r:     New counter value for jumps/branches
  // - cnt_overwrite_r:   Control signal to overwrite PC with cnt_new_val_r
  //
  // Operation:
  // 1. Normal Operation:
  //    - PC increments when PC_inc_w is high during WRITE_BACK state
  //    - Increment stops when max_size_reached_r is set
  //
  // 2. Jump Operation:
  //    - cnt_new_val_r holds the jump target address
  //    - cnt_overwrite_r triggers loading of new address
  //    - PC updates to jump target on next clock
  //
  // Note: The 'synthesis preserve' attributes are used to prevent optimization
  // of critical control signals during synthesis
  ///////////////////////////////////////////////////////////////////////////////////////

  localparam PC_SIZE = 4;  // 4-bit address space for program memory
  reg [PC_SIZE-1:0] PC_ADDR_r /* synthesis preserve */;      // Current instruction address
  reg max_size_reached_r /* synthesis preserve */;           // Maximum address boundary flag
  logic PC_inc_w /* synthesis preserve */;                   // PC increment control wire
  assign PC_inc_w = PC_inc_r && (curr_state == WRITE_BACK); // Only increment during WRITE_BACK
  reg [PC_SIZE-1:0] cnt_new_val_r /* synthesis preserve */;  // New address for jumps
  reg cnt_overwrite_r /* synthesis preserve */;              // Jump control signal

  // Program Counter instance
  PC  #(
        .SIZE(5)        // 5-bit internal counter size
      )
      PC_inst
      (
        .clk(clk),                          // System clock
        .rstn(rstn),                        // Active-low reset
        .inc(PC_inc_w),                     // Increment control
        .cnt_overwrite(cnt_overwrite_r),    // Jump control
        .cnt_new_val(cnt_new_val_r),        // Jump target address
        .cnt_val(PC_ADDR_r),                // Current program counter value
        .max_size_reached(max_size_reached_r)// Maximum address reached flag
      );

  ///////////////////////////////////////////////////////////////////////////////////////
  // Program Memory (PROG_MEM) Logic
  //
  // Description:
  // The Program Memory module stores the processor's instruction memory. It supports
  // both instruction fetch during normal operation and program loading during
  // initialization. The memory is addressable using ADDR_SIZE bits and stores
  // instructions of DATA_SIZE width.
  //
  // Parameters:
  // - DATA_SIZE: Width of instruction words (default: 8 bits)
  // - ADDR_SIZE: Width of address bus (default: 4 bits, allows up to 16 instructions)
  //
  // Key Signals:
  // - PROG_MEM_INSTRUCTION_r: Register holding current instruction
  // - PC_ADDR_w:             Multiplexed address input (PC_ADDR_r or external ADDR)
  // - PROG_MEM_DATA_w:       Output data from program memory
  //
  // Operation Modes:
  // 1. Program Loading (W = 1):
  //    - Address source: External ADDR input
  //    - DATA_WR contains instruction to be written
  //    - Used during initial program loading
  //
  // 2. Instruction Fetch (W = 0):
  //    - Address source: Program Counter (PC_ADDR_r)
  //    - PROG_MEM_DATA_w provides instruction for execution
  //    - Used during normal program execution
  //
  // Note: The 'synthesis preserve' attributes ensure critical control paths
  // are not optimized away during synthesis
  ///////////////////////////////////////////////////////////////////////////////////////

  // Storage for current instruction
  reg [DATA_SIZE-1:0] PROG_MEM_INSTRUCTION_r /* synthesis preserve */;

  // Address multiplexing logic
  wire [ADDR_SIZE-1:0] PC_ADDR_w /* synthesis preserve */;
  wire [DATA_SIZE-1:0] PROG_MEM_DATA_w /* synthesis preserve */;
  
  // Select between program loading (W=1) and instruction fetch (W=0)
  assign PC_ADDR_w = (W) ? ADDR : PC_ADDR_r /* synthesis preserve */;

  // Program Memory instance
  PROG_MEM #(
             .DATA_SIZE(DATA_SIZE),    // Width of instruction words
             .ADDR_SIZE(ADDR_SIZE)     // Width of address bus
           ) PROG_MEM_inst
           (
             .clk(clk),               // System clock
             .rstn(rstn),             // Active-low reset
             .W(W),                   // Write enable (1: program loading, 0: instruction fetch)
             .ADDR(PC_ADDR_w),        // Memory address (multiplexed PC/external)
             .DATA_WR(DATA_WR),       // Input data for program loading
             .DATA(PROG_MEM_DATA_w)   // Output instruction data
           );
           
  ///////////////////////////////////////////////////////////////////////////////////////
  // Instruction Decoder (ID) Logic
  //
  // Description:
  // The Instruction Decoder module breaks down the 16-bit instruction word into its
  // constituent parts and generates control signals for the CPU. It decodes the
  // operation code, memory operation type, and operands from the instruction.
  //
  // Instruction Format:
  // - 16-bit instruction word (INSTR_r) containing:
  //   * Operation Code (OP_CODE)
  //   * Memory Operation Type (MEM_OP)
  //   * Operands (LEFT_OPERAND, RIGHT_OPERAND)
  //
  // Key Signals:
  // - INSTR_r [15:0]:        Raw instruction from program memory
  // - OP_CODE_r [SIZE-1:0]:  Decoded operation code (ADD, SUB, etc.)
  // - MEM_OP_r [SIZE-1:0]:   Memory operation type (LOAD, STORE, etc.)
  // - OPERAND_r:             Immediate operand or address
  // - LEFT_OPERAND_r:        First source operand
  // - RIGHT_OPERAND_r:       Second source operand
  //
  // Operation:
  // 1. Instruction Fetch:
  //    - INSTR_r receives instruction from PROG_MEM_DATA_w
  //
  // 2. Instruction Decode:
  //    - Extracts operation code and memory operation type
  //    - Identifies source and destination operands
  //    - Sets up control signals for execution phase
  //
  // Note: The 'synthesis preserve' attributes ensure critical decoder
  // signals maintain their functionality after synthesis
  ///////////////////////////////////////////////////////////////////////////////////////

  // Instruction word and its components
  logic [15:0] INSTR_r /* synthesis preserve */;        // Full instruction word
  assign INSTR_r = PROG_MEM_DATA_w;                     // Load from program memory
  
  // Decoded instruction fields
  logic [SIZE-1:0] OP_CODE_r /* synthesis preserve */;      // Operation code
  logic [SIZE-1:0] MEM_OP_r /* synthesis preserve */;       // Memory operation type
  logic [DATA_SIZE-1:0] OPERAND_r /* synthesis preserve */; // Immediate/address field
  logic [SIZE-1:0] LEFT_OPERAND_r /* synthesis preserve */; // First source operand
  logic [SIZE-1:0] RIGHT_OPERAND_r /* synthesis preserve */;// Second source operand

  // Instruction Decoder instance
  ID  ID_inst
      (
        .INSTR(INSTR_r),           // Input instruction word
        .OP_CODE(OP_CODE_r),       // Decoded operation
        .MEM_OP(MEM_OP_r),         // Memory operation type
        .OPERAND(OPERAND_r),       // Immediate/address value
        .LEFT_OPERAND(LEFT_OPERAND_r),  // First operand
        .RIGHT_OPERAND(RIGHT_OPERAND_r) // Second operand
      );
    
  ///////////////////////////////////////////////////////////////////////////////////////
  // Arithmetic Logic Unit (ALU) Logic
  //
  // Description:
  // The ALU performs all arithmetic and logical operations for the CPU. It supports
  // various operations including addition, subtraction, logical operations (AND, OR, 
  // XOR, NOT), and shift operations. The ALU interfaces with the instruction decoder
  // and accumulator to process data according to the current operation code.
  //
  // Parameters:
  // - SIZE: Bit width of operands and result (matches CPU data width)
  //
  // Key Signals:
  // - carry_out_r:          Carry output from arithmetic operations
  // - carry_in:             Carry input for chained operations
  // - ALU_CE_r:            Clock enable for ALU operations
  // - ALU_op_out_w:        Operation result output
  // - ALU_left_operand_r:  First input operand
  // - ALU_right_operand_r: Second input operand
  //
  // Operation:
  // 1. Setup Phase:
  //    - Load operands from registers or memory
  //    - Set operation code from instruction decoder
  //    - Configure carry input for arithmetic operations
  //
  // 2. Execution Phase:
  //    - Perform operation based on OP_CODE_r
  //    - Generate result and carry output
  //    - Update flags based on result
  //
  // Note: The 'synthesis preserve' attributes ensure critical ALU
  // signals maintain their functionality after synthesis
  ///////////////////////////////////////////////////////////////////////////////////////

  // ALU control and status signals
  reg carry_out_r;                                        // Carry output flag
  reg carry_in = 1'b0;                                   // Carry input (default: 0)
  reg ALU_CE_r;                                          // ALU clock enable
  
  // ALU data paths
  logic [SIZE-1:0] ALU_op_out_w /* synthesis preserve */;      // Operation result
  reg [SIZE-1:0] ALU_left_operand_r /* synthesis preserve */;  // First operand
  reg [SIZE-1:0] ALU_right_operand_r /* synthesis preserve */; // Second operand

  // ALU instance
  ALU #(
        .SIZE(SIZE)                   // Set operand and result width
      ) ALU_inst
      (
        .CE(ALU_CE_r),               // Chip enable
        .OP_CODE(OP_CODE_r),         // Operation to perform
        .left_operand(ALU_left_operand_r),   // First input operand
        .right_operand(ALU_right_operand_r), // Second input operand
        .carry_in(carry_out_r),      // Carry input for arithmetic
        .carry_out(carry_out_r),     // Carry output from operation
        .op_out(ALU_op_out_w)        // Operation result
      );
  
  //////////////////////////////////////////////////////////////////////////////////////
  // Accumulator (ACU) Logic
  //
  // Description:
  // The Accumulator is a special-purpose register that stores the results of ALU
  // operations and serves as a primary working register for the CPU. It acts as a
  // temporary storage for intermediate calculation results and provides quick access
  // to operands for subsequent operations.
  //
  // Parameters:
  // - SIZE: Bit width of the accumulator (matches CPU data width)
  //
  // Key Signals:
  // - ACU_out_val_w:  Current value stored in accumulator
  // - ACC_in_val_r:   Input value to be stored (from ALU result)
  // - ACC_CE_r:       Chip enable signal for accumulator updates
  //
  // Operation:
  // 1. Data Input:
  //    - Receives result from ALU operations (ALU_op_out_w)
  //    - Input value latched when ACC_CE_r is active
  //
  // 2. Data Storage:
  //    - Maintains value until next write operation
  //    - Value available continuously on ACU_out_val_w
  //
  // 3. Timing:
  //    - Updates occur on rising clock edge when CE is active
  //    - Reset sets output to 0
  //
  // Note: The 'synthesis preserve' attributes ensure critical accumulator
  // signals maintain their functionality after synthesis
  //////////////////////////////////////////////////////////////////////////////////////

  // Accumulator data paths
  wire [SIZE-1:0] ACU_out_val_w /* synthesis preserve */;  // Accumulator output
  reg  [SIZE-1:0] ACC_in_val_r /* synthesis preserve */;   // Input value register
  assign ACC_in_val_r = ALU_op_out_w;                      // Connect to ALU result

  // Control signal
  reg ACC_CE_r;                                            // Chip enable control

  // Accumulator instance
  ACU #(
        .SIZE(SIZE)                    // Set accumulator width
      ) ACU_inst (
        .clk(clk),                     // System clock
        .rstn(rstn),                   // Active-low reset
        .CE(ACC_CE_r),                 // Chip enable
        .in_val(ACC_in_val_r),         // Input from ALU
        .out_val(ACU_out_val_w)        // Current accumulator value
      );
  //////////////////////////////////////////////////////////////////////////////////////
  // Register File (REG_FILE) Logic
  //
  // Description:
  // The Register File provides a bank of general-purpose registers for temporary
  // data storage during program execution. It supports single-cycle read and write
  // operations, allowing quick access to frequently used data. The register file
  // is essential for storing intermediate results, loop counters, and temporary
  // variables.
  //
  // Parameters:
  // - DATA_SIZE: Width of data stored in registers
  // - SIZE: Address width (determines number of registers, 2^SIZE registers)
  //
  // Key Signals:
  // - REG_FILE_DATA_OUT_r: Data read from selected register
  // - REG_FILE_ADDR_r:     Register address for read/write
  // - REG_FILE_CE_r:       Chip enable for write operations
  // - REG_FILE_DATA_IN_r:  Data to be written to register
  //
  // Operation Modes:
  // 1. Read Operation (CE = 0):
  //    - Address specified by REG_FILE_ADDR_r
  //    - Data available on REG_FILE_DATA_OUT_r in same cycle
  //    - Non-destructive read operation
  //
  // 2. Write Operation (CE = 1):
  //    - Address specified by REG_FILE_ADDR_r
  //    - Data from REG_FILE_DATA_IN_r written on rising clock
  //    - Previous value overwritten
  //
  // Timing:
  // - Reads: Combinational (no clock required)
  // - Writes: Synchronous with rising clock edge when CE is high
  // - Reset: All registers cleared to 0
  //
  // Note: The 'synthesis preserve' attributes ensure critical register file
  // signals maintain their functionality after synthesis
  //////////////////////////////////////////////////////////////////////////////////////

  // Register File data paths
  wire [DATA_SIZE-1:0] REG_FILE_DATA_OUT_r /* synthesis preserve */; // Read data output
  reg  [SIZE-1:0] REG_FILE_ADDR_r /* synthesis preserve */;         // Register address
  reg             REG_FILE_CE_r /* synthesis preserve */;          // Write enable
  reg  [DATA_SIZE-1:0] REG_FILE_DATA_IN_r /* synthesis preserve */; // Write data input
  
  // Register File instance
  REG_FILE  REG_FILE_inst (
              .CLK(clk),              // System clock
              .RSTN(rstn),            // Active-low reset
              .ADDR(REG_FILE_ADDR_r), // Register address
              .CE(REG_FILE_CE_r),     // Write enable
              .DATA_IN(REG_FILE_DATA_IN_r),  // Write data
              .DATA_OUT(REG_FILE_DATA_OUT_r) // Read data
            );
  //////////////////////////////////////////////////////////////////////////////////////
  // Stack Logic
  //
  // Description:
  // The Stack module implements a Last-In-First-Out (LIFO) memory structure used
  // primarily for storing return addresses during subroutine calls. When a JMP
  // instruction is executed, the current PC value is pushed onto the stack. During
  // a RTN instruction, the stored address is popped and used as the return point.
  //
  // Parameters:
  // - DATA_SIZE:  Width of stack data (set to ADDR_SIZE for PC addresses)
  // - STACK_SIZE: Depth of the stack (number of entries it can hold)
  //
  // Key Signals:
  // - PC_STACK_ADDR_r:  Address popped from stack during return
  // - PC_STACK_W_w:     Push enable (active during JMP in EXEC state)
  // - PC_STACK_R_w:     Pop enable (active during RTN in DECODE state)
  // - stack_full_w:     Indicates stack has reached maximum capacity
  // - stack_empty_w:    Indicates stack has no entries
  //
  // Operation Modes:
  // 1. Push Operation (JMP instruction):
  //    - Activated when: curr_state == EXEC && OP_CODE_r == OP_JMP
  //    - PC_ADDR_r value pushed onto stack
  //    - Stack full condition monitored
  //
  // 2. Pop Operation (RTN instruction):
  //    - Activated when: curr_state == DECODE && OP_CODE_r == OP_RTN
  //    - Top value popped to PC_STACK_ADDR_r
  //    - Stack empty condition monitored
  //
  // State Dependencies:
  // - Push occurs during EXEC state of JMP instruction
  // - Pop occurs during DECODE state of RTN instruction
  //
  // Note: Stack overflow (full) and underflow (empty) conditions are
  // monitored to prevent invalid operations
  //////////////////////////////////////////////////////////////////////////////////////

  // Stack control and data signals
  reg [ADDR_SIZE-1:0] PC_STACK_ADDR_r;                   // Popped address register
  
  // Push/Pop control logic
  wire PC_STACK_W_w = (curr_state == EXEC && next_state == EXEC && 
                       OP_CODE_r == OP_JMP) ? 1'b1 : 1'b0;  // Push enable
  
  wire PC_STACK_R_w = (curr_state == DECODE && next_state == DECODE && 
                       OP_CODE_r == OP_RTN) ? 1'b1 : 1'b0;  // Pop enable
  
  // Stack status flags
  wire stack_full_w;    // Stack full indicator
  wire stack_empty_w;   // Stack empty indicator

  // Stack instance
  STACK #(
            .DATA_SIZE(ADDR_SIZE),    // Stack stores PC addresses
            .STACK_SIZE(STACK_SIZE)   // Number of stack entries
    ) STACK_inst (
            .CLK(clk),               // System clock
            .RSTN(rstn),             // Active-low reset
            .W(PC_STACK_W_w),        // Push enable
            .R(PC_STACK_R_w),        // Pop enable
            .DATA_WR(PC_ADDR_r),     // PC value to push
            .DATA_RD(PC_STACK_ADDR_r), // Popped PC value
            .stack_full(stack_full_w),  // Full flag
            .stack_empty(stack_empty_w) // Empty flag

      );

  //////////////////////////////////////////////////////////////////////////////////
  // Data Memory Subsystem
  //
  // Description:
  // This section implements the data memory interface and control logic for the CPU.
  // It provides read/write access to the data memory with parameterized width and depth.
  // The memory operations are synchronized with the CPU clock and controlled by the
  // instruction decoder.
  //
  // Interface Signals:
  // - W_data_mem_r:     Write enable control for data memory
  // - DATA_MEM_WR_r:    Write data bus [DATA_SIZE-1:0]
  // - DATA_MEM_ADDR_r:  Memory address bus [ADDR_SIZE-1:0]
  // - DATA_MEM_RD_r:    Read data bus [DATA_SIZE-1:0]
  //
  // Parameters:
  // - DATA_SIZE: Width of data bus (from top-level parameter)
  // - ADDR_SIZE: Width of address bus (from top-level parameter)
  //
  // Operation:
  // 1. Write Operation (W_data_mem_r = 1):
  //    - DATA_MEM_WR_r value written to DATA_MEM_ADDR_r location
  //    - Operation completes in one clock cycle
  //
  // 2. Read Operation (W_data_mem_r = 0):
  //    - Data from DATA_MEM_ADDR_r location appears on DATA_MEM_RD_r
  //    - Read value available in next clock cycle
  //
  // Note: The 'synthesis preserve' attributes ensure critical control
  // and data registers maintain their structure during synthesis
  //////////////////////////////////////////////////////////////////////////////////

  // Interface registers with synthesis preservation
  reg W_data_mem_r /* synthesis preserve */;              // Write enable control
  reg [DATA_SIZE-1:0] DATA_MEM_WR_r /* synthesis preserve */;    // Write data register
  reg [ADDR_SIZE-1:0] DATA_MEM_ADDR_r /* synthesis preserve */;  // Address register
  reg [DATA_SIZE-1:0] DATA_MEM_RD_r /* synthesis preserve */;    // Read data register

    // Data Memory module instantiation
    DATA_MEM #(
               .DATA_SIZE(DATA_SIZE),     // Data width parameter
               .ADDR_SIZE(ADDR_SIZE)      // Address width parameter
             ) DATA_MEM_inst
             (
               .clk(clk),                // System clock
               .rstn(rstn),              // Async reset, active low
               .W(W_data_mem_r),         // Write enable
               .DATA_WR(DATA_MEM_WR_r),  // Write data input
               .ADDR(DATA_MEM_ADDR_r),   // Memory address
               .DATA_RD(DATA_MEM_RD_r)   // Read data output
     );
  
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
          ACC_CE_r <= 1'b0;
          next_state <= DECODE;
        end
        DECODE:
        begin
          PC_inc_r <= 1'b0;
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


  //////////////////////////////////////////////////////////////////////////////////////
  // Assignments
  ///////////////////////////////////////////////////////////////////////////////////////
  assign PC_ADDR_out = PC_ADDR_r;
  assign OP_CODE_out= OP_CODE_r;
  assign OP_MEM_OUT= MEM_OP_r;
  assign LEFT_OPERAND_out= LEFT_OPERAND_r;
  assign RIGHT_OPERAND_out= RIGHT_OPERAND_r;
  assign ACC_OUT= ACU_out_val_w;
  assign ALU_OUT= ALU_op_out_w;
  assign REG_FILE_OUT= REG_FILE_DATA_OUT_r;
  assign DATA_MEM_OUT= DATA_MEM_RD_r;
  assign curr_state_out = curr_state;
  assign next_state_out = next_state;
  assign stack_full_out = stack_full_w;
  assign stack_empty_out = stack_empty_w;
  endmodule
