`timescale 1ns / 1ps

#include "../top_level.sv"
 module CPU_toplevel_tb;

   // Parameters
   localparam SIZE = 8;
   localparam CLK_PERIOD = 10;

   // Signals
   reg clk;
   reg rstn;

   // DUT (Device Under Test) Signals
   wire [4:0] PC_ADDR;
   wire [5:0] PROG_MEM_INSTRUCTION;
   wire [2:0] OP_CODE;
   wire [1:0] ADDR;
   wire ACC_CE;
   wire [3:0] CE;

   // Instantiate the DUT
   CPU_toplevel #(.SIZE(SIZE)) DUT (
                  .clk(clk),
                  .rstn(rstn)
                );

   // Clock Generation
   initial
   begin
     clk = 0;
     forever
       #(CLK_PERIOD/2) clk = ~clk;
   end

   // Reset Process
   initial
   begin
     rstn = 0;
     #20 rstn = 1;  // Apply reset and hold for 20 ns, then release
   end

   // Testbench Control Variables
   reg [1:0] expected_state;
   integer errors;

   // Monitor Signals and Check Transitions
   initial
   begin
     errors = 0;

     // Wait for reset release
     wait (rstn == 1);

     // State transition tests
     #CLK_PERIOD;
     expected_state = 2'b00; // FETCH
     check_state(expected_state, "FETCH");

     #CLK_PERIOD;
     expected_state = 2'b01; // DECODE
     check_state(expected_state, "DECODE");

     #CLK_PERIOD;
     expected_state = 2'b10; // EXEC
     check_state(expected_state, "EXEC");

     #CLK_PERIOD;
     expected_state = 2'b11; // WRITE_BACK (if implemented)
     check_state(expected_state, "WRITE_BACK");

     // Final Report
     if (errors == 0)
       $display("All tests passed!");
     else
       $display("%d tests failed.", errors);

     // Finish Simulation
     $finish;
   end

   // State Checking Task
   task check_state(input [1:0] expected, input string state_name);
     if (DUT.curr_state !== expected)
     begin
       $display("Error: Expected state %s but found %0d at time %0t", state_name, DUT.curr_state, $time);
       errors = errors + 1;
     end
     else
     begin
       $display("State %s verified successfully at time %0t", state_name, $time);
     end
   endtask

 endmodule
