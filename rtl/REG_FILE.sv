`timescale 1ns / 1ps
/**
    Register File module
*/

module REG_FILE (
    input CLK,
    input RSTN,
    input [1:0] ADDR,
    input [3:0] CE,
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
        DATA_r[i] <= 8'b0; 
      end
    else
    begin
      for (int i = 0; i < 4; i++)
      begin
        if (CE[i])
        begin
          DATA_r[i] <= DATA_IN;
        end
      end
      DATA_OUT_r <= DATA_r[ADDR];
    end

  end
  assign DATA_OUT = DATA_OUT_r;
endmodule
