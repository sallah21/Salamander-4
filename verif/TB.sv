`timescale 1ns / 1ps

module CPU_toplevel_tb;

   // Parameters
   localparam SIZE = 8;
   localparam DATA_SIZE = 16;
   localparam ADDR_SIZE = 5;
   localparam CLK_PERIOD = 10;

   // Signals
   reg clk;
   reg rstn;
   reg W;
   reg OVERWRITE=0;
   reg [DATA_SIZE-1:0] DATA_WR;
   reg [ADDR_SIZE-1:0] ADDR;
   
   // For monitoring
   integer file_handle;
   
   // Instantiate the DUT
   top_level #(.SIZE(SIZE),
              .DATA_SIZE(DATA_SIZE),
              .ADDR_SIZE(ADDR_SIZE)) DUT (
       .clk(clk),
       .rstn(rstn),
       .W(W),
       .OVERWRITE(OVERWRITE),
       .ADDR(ADDR),
       .DATA_WR(DATA_WR)
   );

   // Clock Generation
   initial
   begin
     clk = 0;
     forever
       #(CLK_PERIOD / 2) clk = ~clk;
   end

   // Generate memory content
   function [DATA_SIZE-1:0] generate_memory_content ([3:0] right_operand, [3:0] left_operand, [3:0] mem_op, [3:0] op_code);
    begin
      logic [DATA_SIZE-1:0] mem_content;
      mem_content = {
        op_code,
        mem_op,
        left_operand,
        right_operand
      };
      return mem_content;
    end 
   endfunction

   // Initialize memory
   task initialize_memory;
     integer i;  
     begin
       i = 0;    
       @(posedge clk);
       W = 1'b1;
       @(posedge clk);
       OVERWRITE = 1'b1;
       $display("Initializing memory");
       ADDR = i;
       DATA_WR = generate_memory_content(4'h2, 4'h1, 4'b0000, OP_INC);
       @(posedge clk);
       i=i+1;
       ADDR = i;
       @(posedge clk);
       DATA_WR = generate_memory_content(4'h3, 4'h2, 4'b0000, OP_ADD);
       @(posedge clk);
       i=i+1;
       ADDR = i;
       @(posedge clk);
       DATA_WR = generate_memory_content(4'd0, 4'h1, REG_TO_REG, OP_ST);
       @(posedge clk);
       W = 1'b0;
       OVERWRITE = 1'b0;
       $display("Memory initialization completed");
     end
   endtask

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
     initialize_memory();
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

    $display("Test Phase 2 completed at %0t ns", $time);
    

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