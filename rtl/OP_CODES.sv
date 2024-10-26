/** 
    Operational codes for Arithmetical Logical Unit (ALU)
*/

typedef enum logic [2:0]{  
    OP_ADD  = 3'b000,
    OP_SUB  = 3'b001,
    OP_AND  = 3'b010,
    OP_OR   = 3'b011,
    OP_XOR  = 3'b100,
    OP_NOT  = 3'b101,
    OP_LD   = 3'b110,
    OP_ST   = 3'b111
} OPERATION_CODE;