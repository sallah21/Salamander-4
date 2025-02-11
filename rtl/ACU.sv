`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// ACU (Accumulator) Module
//
// Description:
// This module implements a configurable-width accumulator register that serves as
// the primary working register for arithmetic and logical operations in the CPU.
// The accumulator can be written to when the Chip Enable (CE) signal is active,
// and its value is continuously available on the output.
//
// Features:
// - Parameterized data width
// - Synchronous write operation
// - Asynchronous active-low reset
// - Single-cycle write latency
//
// Parameters:
// - SIZE: Width of the accumulator register in bits (default: 8)
//
// Ports:
// Inputs:
// - clk:     System clock, positive edge triggered
// - rstn:    Asynchronous reset, active low
// - CE:      Chip Enable, active high. Controls write operations
// - in_val:  Input value to be written to accumulator [SIZE-1:0]
//
// Outputs:
// - out_val: Current value of accumulator [SIZE-1:0]
//
// Timing:
// - Reset:   Asynchronous, sets register to 0
// - Write:   Occurs on positive clock edge when CE is high
// - Read:    Continuous (combinational) output
//
// Usage:
// - Assert CE high to write in_val to accumulator
// - Read current value from out_val at any time
// - Reset accumulator by asserting rstn low
//////////////////////////////////////////////////////////////////////////////////

module ACU
  #(
     parameter SIZE = 8  // Width of accumulator register
   )
   (
     input logic clk,                    // System clock
     input logic rstn,                   // Async reset, active low
     input logic CE,                     // Chip enable for writes
     input logic [SIZE-1:0] in_val,     // Input data
     output logic [SIZE-1:0] out_val    // Output data
   );

  // Internal accumulator register
  logic [SIZE-1:0] int_val_r;

  // Synchronous write with asynchronous reset
  always @(posedge clk or negedge rstn)
  begin
    if (!rstn)
    begin
      int_val_r <= {SIZE{1'b0}};        // Clear register on reset
    end
    else
    begin
      if (CE)
      begin
          int_val_r <= in_val;          // Write new value when CE is high
      end
    end
  end

  // Continuous output assignment
  assign out_val = int_val_r;

`ifdef FORMAL
  property data_stable_during_ce_low;
    @(posedge clk)
    disable iff (!rstn)
    (!CE && $fell(CE)) |=> $stable(out_val);
  endproperty

  assert property (data_stable_during_ce_low) 
    else $error("Data changed while CE was low!");

`endif
endmodule
