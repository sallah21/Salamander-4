/**
    Accumulator module 
*/

module ACU
   #(
     parameter SIZE = 8 // Corrected parameter declaration
   )
   (
     input clk,
     input rstn,
     input CE,
     input [SIZE-1:0] in_val,
     output [SIZE-1:0] out_val // Removed extra comma
   );

  // Internal value register
  reg [SIZE-1:0] int_val_r;

  always @(posedge clk or negedge rstn) // Corrected 'always_ff' to 'always'
  begin
    if (!rstn)
    begin
      int_val_r <= {SIZE{1'b0}}; // Corrected zero-fill syntax
    end
    else
    begin
      if (CE)
      begin
        int_val_r <= in_val;
      end
    end
  end

  assign out_val = int_val_r;
endmodule