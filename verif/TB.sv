`timescale 1ns / 1ps

module CPU_toplevel_tb;

   // Parameters
   localparam SIZE = 8;
   localparam CLK_PERIOD = 10;

   // Signals
   reg clk;
   reg rstn;
   
   // For monitoring
   integer file_handle;
   
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
     // Initialize waveform dump
     $dumpfile("wave.vcd");  // Create VCD file
     $dumpvars(0, CPU_toplevel_tb);  // Dump all variables
     
     // Open log file
     file_handle = $fopen("simulation.log", "w");
     if (!file_handle) begin
       $display("Error: Could not open log file");
       $finish;
     end
     
     // Initial message
     $display("Starting CPU testbench simulation");
     $fwrite(file_handle, "Starting CPU testbench simulation\n");

     // Apply reset
     rstn = 0;
     #20 rstn = 1;  // Apply reset and hold for 20 ns, then release

     
     $display("Reset released at %0t ns", $time);
     $fwrite(file_handle, "Reset released at %0t ns\n", $time);
   end

   // Monitor for checking clock transitions
   always @(posedge clk)
   begin
     if (file_handle) begin
       $fwrite(file_handle, "Clock positive edge at %0t ns\n", $time);
     end
   end

   // Testbench Main Control
   initial
   begin
     // Wait for reset to complete
     @(posedge rstn);
     
     // Wait a few clock cycles to ensure stable state
     repeat(5) @(posedge clk);
     $display("System stabilized after reset at %0t ns", $time);
     
     // Test Phase 1: Initial Operation Check
     $display("Starting Test Phase 1: Initial Operation Check");
     repeat(10) @(posedge clk);
     
     // Test Phase 2: Extended Operation
     $display("Starting Test Phase 2: Extended Operation");
     repeat(20) @(posedge clk);
     
     // Add delay for observation
     #100;

     // Finish Simulation
     $display("Testbench completed at %0t ns", $time);
     if (file_handle) begin
       $fwrite(file_handle, "Testbench completed at %0t ns\n", $time);
       $fclose(file_handle);
       file_handle = 0;
     end
     
     $finish;
   end

endmodule