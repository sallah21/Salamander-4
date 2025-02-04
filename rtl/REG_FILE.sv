`timescale 1ns / 1ps
/**
    Register File module
*/

module REG_FILE (
    input CLK,
    input RSTN,
    input [3:0] ADDR,
    input CE,
    input [7:0] DATA_IN,
    output [7:0] DATA_OUT
  );
  reg [7:0] DATA_r [3:0] ;
  reg [7:0] DATA_OUT_r;
  always @( posedge CLK or negedge RSTN )
  begin
    if (!RSTN)
      for (int i = 0; i < 4; i++)
      begin
        DATA_r[i] <= i+2; 
      end
    else
    begin
      if (CE)
        DATA_r[ADDR] <= DATA_IN;
      end
      DATA_OUT_r <= DATA_r[ADDR];
    end

  assign DATA_OUT = DATA_OUT_r;
endmodule
