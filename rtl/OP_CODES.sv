/** 
    Operational codes for Arithmetical Logical Unit (ALU)
*/

// Operation codes for ALU in 4-bit format
typedef enum logic [3:0]{  
    // Arithmetic operations
    OP_ADD  = 4'b0000, // Add operation
    OP_SUB  = 4'b0001, // Subtract operation
    OP_LD   = 4'b0010, // Load operation
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
    // Special operations
    OP_NOP  = 4'b1100, // No operation
    OP_HLT  = 4'b1101,  // Halt operation
    // Jump operations
    OP_JZ   = 4'b1110, // Jump if zero
    OP_JNZ  = 4'b1111  // Jump if not zero

} OPERATION_CODE;