/** 
    Operational codes for Arithmetical Logical Unit (ALU)
*/

// Operation codes for ALU in 3-bit format
typedef enum logic [2:0]{  
    OP_ADD  = 3'b000, // Add operation
    OP_SUB  = 3'b001, // Subtract operation
    OP_AND  = 3'b010, // AND operation
    OP_OR   = 3'b011, // OR operation
    OP_XOR  = 3'b100, // XOR operation
    OP_NOT  = 3'b101, // NOT operation
    OP_LD   = 3'b110, // Load operation
    OP_ST   = 3'b111  // Store operation
} OPERATION_CODE;