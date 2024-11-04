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
  reg [7:0] DATA_r [1:0] ;
  reg [7:0] DATA_OUT_r;

  always_ff @( posedge CLK or negedge RSTN )
  begin
    if (!RSTN)
    begin
      for ( int i  = 0 ; i <4 ; i++ )
      begin
        DATA_r [i] <= 8'bz;
      end
    end
    else
    begin
      case (ADDR)
        2'b00: begin 
            if (CE[0]) begin
                DATA_r [ADDR] <= DATA_IN;
            end 
            DATA_OUT_r <= DATA_r [ADDR]; // NOTE: Should take one cycle if both CE[x] is enabled and register is read 
        end 
        2'b01: begin 
            if (CE[1]) begin
                DATA_r [ADDR] <= DATA_IN;
            end 
            DATA_OUT_r <= DATA_r [ADDR]; // NOTE: Should take one cycle if both CE[x] is enabled and register is read 
        end 
        2'b10: begin 
            if (CE[2]) begin
                DATA_r [ADDR] <= DATA_IN;
            end 
            DATA_OUT_r <= DATA_r [ADDR]; // NOTE: Should take one cycle if both CE[x] is enabled and register is read 
        end 
        2'b11: begin 
            if (CE[3]) begin
                DATA_r [ADDR] <= DATA_IN;
            end 
            DATA_OUT_r <= DATA_r [ADDR]; // NOTE: Should take one cycle if both CE[x] is enabled and register is read 
        end 

      endcase
    end

  end
assign DATA_OUT = DATA_OUT_r;
endmodule
