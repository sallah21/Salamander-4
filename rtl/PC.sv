
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
     output [SIZE-1:0] cnt_val,
     output max_size_reached
   );
  // Internal counter value
  reg [SIZE-1:0] cnt_r;
  reg max_size_reached_r;
  localparam SIZEMINONE = SIZE - 1;
  localparam [SIZE-1:0] MAX_VAL = (2**SIZE) -1; 

  always @(posedge clk or negedge rstn)
  begin
    if (!rstn)
    begin
      cnt_r <= {SIZE{1'b0}};
      max_size_reached_r <= 1'b0;
    end
    else
    begin
      if (inc)
      begin
        if (cnt_r <= MAX_VAL) begin
            cnt_r <= cnt_r + 5'b1; 
        end
        else begin
            max_size_reached_r <= 1'b1;
         end 

      end
    end
  end

  assign cnt_val = cnt_r;
  assign max_size_reached = max_size_reached_r;
endmodule