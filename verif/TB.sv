`timescale 1ns / 1ps

module CPU_toplevel_tb;

   // Parameters
   localparam SIZE = 8;
   localparam CLK_PERIOD = 10;

   // Signals
   reg clk;
   reg rstn;

   // Instantiate the DUT
   top_level #(.SIZE(SIZE)) DUT (
       .clk(clk),
       .rstn(rstn)
   );

   // Clock Generation
   initial
   begin
     clk = 0;
     forever
       #(CLK_PERIOD / 2) clk = ~clk;
   end

   // Reset Process
   initial
   begin
     rstn = 0;
     #20 rstn = 1;  // Apply reset and hold for 20 ns, then release
   end

   // Testbench Main Control
   initial
   begin
     // Wait a few clock cycles to observe behavior
     #100;

     // Finish Simulation
     $display("Testbench completed. Check waveforms or signals.");
     $finish;
   end

endmodule