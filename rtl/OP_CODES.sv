//////////////////////////////////////////////////////////////////////////////////
// OP_CODES (Operation Codes) Package
//
// Description:
// This package defines the operation codes for the CPU's Arithmetic Logic Unit (ALU)
// and memory operations. It provides two enumerated types: OPERATION_CODE for ALU
// operations and MEMORY_OP_CODE for memory access patterns.
//
// Features:
// - 4-bit operation codes
// - Grouped by operation type
// - Comprehensive instruction set
// - Memory operation patterns
//
// OPERATION_CODE Categories:
// 1. Arithmetic Operations (0xxx):
//    - ADD  (0000): Addition with carry
//    - SUB  (0001): Subtraction with borrow
//    - LD   (0010): Load operation
//    - ST   (0011): Store operation
//    - INC  (0100): Increment by 1
//    - DEC  (0101): Decrement by 1
//
// 2. Logic Operations (0110-1001):
//    - AND  (0110): Bitwise AND
//    - OR   (0111): Bitwise OR
//    - XOR  (1000): Bitwise XOR
//    - NOT  (1001): Bitwise NOT (complement)
//
// 3. Shift Operations (101x):
//    - SHL  (1010): Shift left logical
//    - SHR  (1011): Shift right logical
//
// 4. Control Operations (11xx):
//    - JMP  (1100): Jump to address
//    - RTN  (1101): Return from subroutine
//    - HLT  (1110): Halt execution
//    - NOP  (1111): No operation
//
// MEMORY_OP_CODE Patterns:
// 1. Basic Operations:
//    - NONE       (0000): No memory operation
//    - OP_REG     (0001): Register operation
//    - OP_MEM     (0010): Memory operation
//
// 2. Transfer Operations:
//    - REG_TO_REG (0100): Register to register
//    - REG_TO_MEM (0101): Register to memory
//    - MEM_TO_REG (0110): Memory to register
//    - MEM_TO_MEM (0111): Memory to memory
//
// Usage:
// - ALU operations use OPERATION_CODE
// - Memory transfers use MEMORY_OP_CODE
// - Both types are 4-bit encoded
//////////////////////////////////////////////////////////////////////////////////

// ALU Operation Codes
typedef enum logic [3:0]{  
    // Arithmetic operations
    OP_ADD  = 4'b0000,     // Add with carry
    OP_SUB  = 4'b0001,     // Subtract with borrow
    OP_LD   = 4'b0010,     // Load operation 
    OP_ST   = 4'b0011,     // Store operation
    OP_INC  = 4'b0100,     // Increment by 1
    OP_DEC  = 4'b0101,     // Decrement by 1
    
    // Logic operations
    OP_AND  = 4'b0110,     // Bitwise AND
    OP_OR   = 4'b0111,     // Bitwise OR
    OP_XOR  = 4'b1000,     // Bitwise XOR
    OP_NOT  = 4'b1001,     // Bitwise NOT
    
    // Shift operations
    OP_SHL  = 4'b1010,     // Logical shift left
    OP_SHR  = 4'b1011,     // Logical shift right
    
    // Control operations
    OP_JMP  = 4'b1100,     // Jump to address
    OP_RTN  = 4'b1101,     // Return from subroutine
    OP_HLT  = 4'b1110,     // Halt CPU
    OP_NOP  = 4'b1111      // No operation
} OPERATION_CODE;

// Memory Operation Codes
typedef enum logic [3:0] { 
    NONE       = 4'b0000,  // No memory operation
    OP_REG     = 4'b0001,  // Register operation
    OP_MEM     = 4'b0010,  // Memory operation
    REG_TO_REG = 4'b0100,  // Register to register transfer
    REG_TO_MEM = 4'b0101,  // Register to memory transfer
    MEM_TO_REG = 4'b0110,  // Memory to register transfer
    MEM_TO_MEM = 4'b0111   // Memory to memory transfer
} MEMORY_OP_CODE;