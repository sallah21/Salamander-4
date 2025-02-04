/** 
    Operational codes for Arithmetical Logical Unit (ALU)
*/

// Operation codes for ALU in 5-bit format
typedef enum logic [3:0]{  
    // Arithmetic operations
    OP_ADD  = 4'b0000, // Add operation
    OP_SUB  = 4'b0001, // Subtract operation
    OP_LD   = 4'b0010, // Load operation TODO: Not implemented
    OP_ST   = 4'b0011, // Store operation
    OP_INC  = 4'b0100, // Increment operation
    OP_DEC  = 4'b0101, // Decrement operation
    // Logic operations
    OP_AND  = 4'b0110, // AND operation
    OP_OR   = 4'b0111, // OR operation
    OP_XOR  = 4'b1000, // XOR operation
    OP_NOT  = 4'b1001, // NOT operation
    // Shift operations
    OP_SHL  = 4'b1010, // Shift left operation
    OP_SHR  = 4'b1011, // Shift right operation
    // Jump operations
    OP_JMP   = 4'b1100, // Jump 
    OP_RTN   = 4'b1101, // Return
    // Special operations
    OP_HLT  = 4'b1110, // Halt operation
    OP_NOP  = 4'b1111  // No operation
} OPERATION_CODE;

typedef enum logic [3:0] { 
    NONE       = 4'b0000, // Default value
    OP_REG     = 4'b0001, // Operation on register
    OP_MEM     = 4'b0010, // Operation on memory
    REG_TO_REG = 4'b0100, // R -> R
    REG_TO_MEM = 4'b0101, // R -> M
    MEM_TO_REG = 4'b0110, // M -> R
    MEM_TO_MEM = 4'b0111  // M -> M
 } MEMORY_OP_CODE;