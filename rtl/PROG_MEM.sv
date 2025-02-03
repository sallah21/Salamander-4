`timescale 1ns / 1ps
/**
    Memory for instruction fetching 
*/

module PROG_MEM #(
    parameter DATA_SIZE = 16,
    parameter ADDR_SIZE = 4
  ) (
    input clk,
    input rstn,
    input W,
    input  [DATA_SIZE-1:0] DATA_WR,
    input  [ADDR_SIZE-1:0] ADDR,
    output [DATA_SIZE-1:0] DATA
  );

  logic [DATA_SIZE-1:0] int_mem_r [2**ADDR_SIZE-1:0];

  logic [DATA_SIZE-1:0] DATA_reg;
  always @(posedge clk or negedge rstn)
  begin
    if (!rstn)
    begin
      for (int i = 0; i < 2**ADDR_SIZE; i++)
      begin
        int_mem_r[i] <= {DATA_SIZE{1'b0}};
      end
    end
    else if (W)
    begin
      int_mem_r [ADDR] <= DATA_WR; // Write operation
    end
    else
    begin
      DATA_reg <= int_mem_r [ADDR]; // Read operation
    end
  end
  assign DATA = DATA_reg;
endmodule
