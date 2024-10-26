/**
    Memory for instruction fetching 
*/

module MEM #(
    parameter DATA_SIZE = 6,
    parameter ADDR_SIZE = 5
  ) (
    input clk,
    input rstn,
    input ADDR,
    output DATA
  );

  logic [DATA_SIZE-1:0] int_mem_r [2**ADDR_SIZE-1:0];
  always_ff @(posedge clk or negedge rstn)
  begin
    if (!rstn)
    begin
      for (int i = 0; i < 2**ADDR_SIZE; i++)
      begin
        int_mem_r[i] <= '0;
      end
    end
  end
  assign DATA = int_mem_r [ADDR];
endmodule
