`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// PC (Program Counter) Module
//
// Description:
// This module implements a configurable-width program counter that manages the
// instruction fetch sequence. It supports normal sequential counting, value
// overwriting (for jumps), and maximum value detection. The counter wraps around
// to zero when reaching its maximum value.
//
// Features:
// - Parameterized counter width
// - Synchronous operation with async reset
// - Counter increment control
// - Value overwrite capability
// - Maximum value detection
//
// Parameters:
// - SIZE: Width of the counter in bits (default: 5)
//         Total addressable space = 2^SIZE locations
//
// Ports:
// Inputs:
// - clk:            System clock, positive edge triggered
// - rstn:           Asynchronous reset, active low
// - inc:            Increment enable, active high
// - cnt_overwrite:  Counter overwrite enable for jumps
// - cnt_new_val:    New counter value for overwrites [SIZE-1:0]
//
// Outputs:
// - cnt_val:          Current counter value [SIZE-1:0]
// - max_size_reached: Flag indicating counter reached maximum
//
// Operation Modes:
// 1. Reset (rstn = 0):
//    - Counter cleared to 0
//    - max_size_reached flag cleared
//
// 2. Normal Counting (inc = 1):
//    - Counter increments by 1 each clock if below MAX_VAL
//    - Wraps to 0 when reaching MAX_VAL
//    - Sets max_size_reached flag on wrap
//
// 3. Jump Operation (cnt_overwrite = 1):
//    - Counter loaded with cnt_new_val if < MAX_VAL
//    - max_size_reached flag cleared
//
// Constants:
// - MAX_VAL: Maximum counter value (2^SIZE - 1)
// - SIZEMINONE: Used in internal calculations (SIZE - 1)
//
// Note: Counter value overwrite takes precedence over increment
//////////////////////////////////////////////////////////////////////////////////

module PC
  #(
     parameter SIZE = 5                   // Counter width in bits
   )
   (
     input clk,                          // System clock
     input inc,                          // Increment enable
     input rstn,                         // Async reset, active low
     input cnt_overwrite,                // Jump enable
     input [SIZE-1:0] cnt_new_val,       // Jump target address
     output [SIZE-1:0] cnt_val,          // Current PC value
     output max_size_reached             // Maximum value flag
   );

  // Internal registers
  reg [SIZE-1:0] cnt_r;                  // Counter register
  reg max_size_reached_r;                // Maximum value flag register

  // Local parameters
  localparam SIZEMINONE = SIZE - 1;                // For internal calculations
  localparam [SIZE-1:0] MAX_VAL = (2**SIZE) - 1;   // Maximum counter value

  // Counter logic with async reset
  always @(posedge clk or negedge rstn)
  begin
    if (!rstn)
    begin
      cnt_r <= {SIZE{1'b0}};             // Clear counter
      max_size_reached_r <= 1'b0;        // Clear max flag
    end
    else
    begin
      // Jump operation
      if (cnt_overwrite && (cnt_new_val < MAX_VAL))
      begin
        cnt_r <= cnt_new_val;            // Load jump address
        max_size_reached_r <= 1'b0;      // Clear max flag
      end
      // Normal counting
      if (inc)
      begin
        if (cnt_r < MAX_VAL)
        begin
          cnt_r <= cnt_r + 1'b1;         // Increment counter
        end
        else
        begin
          cnt_r <= {SIZE{1'b0}};         // Wrap to zero
          max_size_reached_r <= 1'b1;    // Set max flag
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

  // Verify counter value never exceeds maximum
  property counter_value_should_not_exceed_max_size;
    @ (posedge clk)
    cnt_r <= MAX_VAL;
  endproperty

  // Verify overwrite value is within bounds
  property counter_overwrite_value_should_not_exceed_max_size;
    @ (posedge clk or negedge rstn)
    $changed(cnt_overwrite) |-> (cnt_new_val < MAX_VAL);
  endproperty

  // Verify max reached flag is set correctly
  property max_size_reached_flag_set_correctly;
    @ (posedge clk)
    (cnt_r == MAX_VAL && inc) |-> ##1 max_size_reached_r;
  endproperty

  // Assert all properties
  assert property (counter_value_should_not_exceed_max_size)
    else $error("Counter value exceeded maximum size!");
    
  assert property (counter_overwrite_value_should_not_exceed_max_size)
    else $error("Counter overwrite value exceeded maximum size!");
    
  assert property (max_size_reached_flag_set_correctly)
    else $error("Max size reached flag not set correctly!");

  `endif // FORMAL
endmodule
