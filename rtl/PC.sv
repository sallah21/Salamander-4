
/**
    Program counter module 
*/

module PC
   #(
     parameter SIZE = 5 // Corrected parameter declaration
   )
   (
     input clk,
     input inc,
     input rstn,
     output [SIZE-1:0] cnt_val
   );
  // Internal counter value
  reg [SIZE-1:0] cnt;
  localparam SIZEMINONE = SIZE - 1;

  always @(posedge clk or negedge rstn)
  begin
    if (!rstn)
    begin
      cnt <= 0;
    end
    else
    begin
      if (inc)
      begin
        cnt <= cnt + 1; // Corrected increment operation
      end
    end
  end

  assign cnt_val = cnt;
endmodule