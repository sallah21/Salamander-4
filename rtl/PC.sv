`timescale 1ns / 1ps
/**
    Program counter module 
*/

module PC
  #(
     parameter SIZE = 5
   )
   (
     input clk,
     input inc,
     input rstn,
     input [SIZE-1:0] inc_val,
     output [SIZE-1:0] cnt_val,
     output max_size_reached
   );
  // Internal counter value
  reg [SIZE-1:0] cnt_r;
  reg max_size_reached_r;
  reg [SIZE-1:0] inc_val_r;

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
        if (cnt_r < MAX_VAL)
        begin
          cnt_r <= cnt_r + inc_val_r;
        end
        else
        begin
          cnt_r <= {SIZE{1'b0}};
          max_size_reached_r <= 1'b1;
        end

      end
    end
  end

  assign cnt_val = cnt_r;
  assign max_size_reached = max_size_reached_r;

  `ifdef FORMAL
  //////////////////////////////////////////////////////////////////////////////////////////
  ///////////// Assertions
  //////////////////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////////////////
  // Asstertion 1: Counter value should not exceed MAX_VAL
  //////////////////////////////////////////////////////////////////////////////////////////

  property cnt_val_does_not_exceed_max_val;
    @ (posedge clk or negedge rstn)
      $stable(cnt_val <= MAX_VAL);
  endproperty

  assert cnt_val_does_not_exceed_max_val else
           $display("Counter value exceeded MAX_VAL at %0t ns", $time);


  //////////////////////////////////////////////////////////////////////////////////////////
  // Asstertion 2: Max size reached asserted correctly
  //////////////////////////////////////////////////////////////////////////////////////////
  property max_size_reached_asserted_correctly;
    @ (posedge clk or negedge rstn)
      $stable(max_size_reached == (cnt_val == MAX_VAL));
  endproperty

  assert max_size_reached_asserted_correctly else
           $display("Max size reached not asserted correctly at %0t ns", $time);

  `endif // FORMAL
endmodule
