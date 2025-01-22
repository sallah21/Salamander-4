`timescale 1ns / 1ps

module ID_TB;

  // Parameters
  localparam SIZE = 8;
  localparam CLK_PERIOD = 10;

  // Signals
  reg clk;
  reg rstn;
  reg ID_CE;
  reg [5:0] INSTR;
  wire [2:0] OP_CODE;
  wire [1:0] ADDR;
  wire [3:0] CE;
  wire ACC_CE;

  // Instantiate the DUT
  ID DUT (
       .INSTR(INSTR),
       .ID_CE(ID_CE),
       .OP_CODE(OP_CODE),
       .ADDR(ADDR),
       .CE(CE),
       .ACC_CE(ACC_CE)
     );

  // Clock generation
  initial
  begin
    clk = 0;
    forever
      #5 clk = ~clk;
  end


  /*
  * Instrction content Description:
  * 
  * +--------+---------------------------------------------+
  * | Bit(s) | Description                                 |
  * +--------+---------------------------------------------+
  * | [0-1]  | ADDR - Register file address                |
  * | [2-4]  | OP_CODE - Operation code for ALU            |
  * | [5]    | ACC_CE - Accumulator chip enable            |
  * +--------+---------------------------------------------+
  * 
  */
  // Testbench logic
  initial
  begin
    // Initialize waveform dump
    $dumpfile("ID.vcd");  // Create VCD file
    $dumpvars(0, ID_TB);  // Dump all variables

    // Apply reset
    rstn = 0;
    #20 rstn = 1;

    // Test Phase 1: ADD Operation
    $display("Starting Test Phase 1: ADD Operation");
    ID_CE = 1;
    INSTR = 6'b000000; // ADD Operation
    repeat(10) @(posedge clk);

    // Test Phase 2: SUB Operation
    $display("Starting Test Phase 2: SUB Operation");
    ID_CE = 1;
    INSTR = 6'b000001;
    repeat(10) @(posedge clk);

    // Test Phase 3: LD Operation
    $display("Starting Test Phase 3: LD Operation");
    ID_CE = 1;
    INSTR = 6'b000010;
    repeat(10) @(posedge clk);

    // Test Phase 4: ST Operation
    $display("Starting Test Phase 4: ST Operation");
    ID_CE = 1;
    INSTR = 6'b000011;
    repeat(10) @(posedge clk);

    // Test Phase 5: XOR Operation
    $display("Starting Test Phase 5: XOR Operation");
    ID_CE = 1;
    INSTR = 6'b000100;
    repeat(10) @(posedge clk);

    // Test Phase 6: NOT Operation
    $display("Starting Test Phase 6: NOT Operation");
    ID_CE = 1;
    INSTR = 6'b000101;
    repeat(10) @(posedge clk);

    // Test Phase 7: LD Operation
    $display("Starting Test Phase 7: LD Operation");
    ID_CE = 1;
    INSTR = 6'b000110;
    repeat(10) @(posedge clk);

    // Test Phase 8: ST Operation
    $display("Starting Test Phase 8: ST Operation");
    ID_CE = 1;
    INSTR = 6'b000111;
    repeat(10) @(posedge clk);

    // Finish Simulation
    $display("Testbench completed at %0t ns", $time);
    $finish;
  end

endmodule
