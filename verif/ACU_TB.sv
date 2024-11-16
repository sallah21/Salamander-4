`timescale 1ns / 1ps

module ACU_TB;

  // Parameters
  localparam SIZE = 8;
  localparam CLK_PERIOD = 10;

  // Signals
  reg clk;
  reg rstn;
  reg CE;
  reg [SIZE-1:0] in_val;
  reg [SIZE-1:0] out_val;
  // For monitoring
  integer file_handle;

  // Instantiate the DUT
  ACU #(.SIZE(SIZE)) DUT (
        .clk(clk),
        .rstn(rstn),
        .CE(CE),
        .in_val(in_val),
        .out_val(out_val)
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
    $dumpfile("ACU.vcd");  // Create VCD file
    $dumpvars(0, ACU_TB);  // Dump all variables

    // Open log file
    file_handle = $fopen("simulation.log", "w");
    if (!file_handle)
    begin
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
    if (file_handle)
    begin
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
    CE = 1'b0;
    in_val = 8'bzzzzzzz;
    $display("System stabilized after reset at %0t ns", $time);

    // Test Phase 1: Change input value but not CE
    $display("Starting Test Phase 1: Change input value but not CE");
    repeat(10) @(posedge clk);
    in_val = 8'b10101010;
    repeat(10) @(posedge clk);
    in_val = 8'b11111111;
    repeat(10) @(posedge clk);
    in_val = 8'b00000000;

    // Add delay for observation
    #100;

    // Test Phase 2: Provide initial value
    $display("Starting Test Phase 2: Provide initial value");
    repeat(10) @(posedge clk);
    in_val = 8'b10101010;
    repeat(10) @(posedge clk);
    CE = 1'b1;
    repeat(10) @(posedge clk);
    CE = 1'b0;

    // Add delay for observation
    #100;

    // Test Phase 3: Change input value and CE
    $display("Starting Test Phase 3: Change input value and CE");
    repeat(10) @(posedge clk);
    in_val = 8'b10101010;
    repeat(10) @(posedge clk);
    CE = 1'b1;
    repeat(10) @(posedge clk);
    CE = 1'b0;
    repeat(10) @(posedge clk);
    in_val = 8'b11111111;
    repeat(10) @(posedge clk);
    in_val = 8'b00000000;
    CE = 1'b1;
    repeat(10) @(posedge clk);
    in_val = 8'bxxxxxxxx;
    repeat(10) @(posedge clk);
    CE = 1'b0;

    // Add delay for observation
    #100;

    // Test Phase 4: Rapid change of CE
    $display("Starting Test Phase 4: Rapid change of CE");
    repeat(10) @(posedge clk);
    in_val = 8'b11111111;
    repeat(10) @(posedge clk);
    CE = 1'b1;
    repeat(10) @(posedge clk);
    CE = 1'b0;
    repeat(10) @(posedge clk);
    CE = 1'b1;
    repeat(10) @(posedge clk);
    CE = 1'b0;
    repeat(10) @(posedge clk);
    CE = 1'b1;
    repeat(10) @(posedge clk);
    CE = 1'b0;

    // Add delay for observation
    #100;

    // Test Phase 5: Asynchronous change of reset
    $display("Starting Test Phase 5: Asynchronous change of reset");
    repeat(10) @(posedge clk);
    in_val = 8'b11111111;
    repeat(10) @(posedge clk);
    CE = 1'b1;
    repeat(10) @(posedge clk);
    rstn = 1'b0;
    #123;
    rstn = 1'b1;
    repeat(10) @(posedge clk);
    CE = 1'b0;
    // Finish Simulation
    $display("Testbench completed at %0t ns", $time);
    if (file_handle)
    begin
      $fwrite(file_handle, "Testbench completed at %0t ns\n", $time);
      $fclose(file_handle);
      file_handle = 0;
    end

    $finish;
  end

endmodule
