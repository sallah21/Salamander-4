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
    reg [DATA_SIZE-1:0] mem_r[2**ADDR_SIZE-1:0];

    always @(posedge clk)
    begin
        if (!rstn)
        begin
            mem_r[ADDR] <= 0;
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