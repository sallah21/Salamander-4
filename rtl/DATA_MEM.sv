module DATA_MEM #(
    parameter DATA_SIZE = 8,
    parameter ADDR_SIZE = 5
)
(
    input clk,
    input rstn,
    input W,
    input [DATA_SIZE-1:0] DATA_WR,
    input [ADDR_SIZE-1:0] ADDR,
    output [DATA_SIZE-1:0] DATA_RD
);

    // Internal memory
    localparam MEM_SIZE = 2**ADDR_SIZE;
    reg [DATA_SIZE-1:0] mem_r[MEM_SIZE-1:0];

    always @(posedge clk)
    begin
        if (!rstn)
        begin
            for (int i = 0; i < MEM_SIZE; i++)
            begin
                mem_r[i] <= i;
            end
        end
        else
        begin
            if (W)
            begin
                mem_r[ADDR] <= DATA_WR;
            end
        end
    end
    
    assign DATA_RD = mem_r[ADDR];

endmodule