`timescale 1ns / 1ps

module ALU_TB;

// Parameters
localparam SIZE = 8;
localparam CLK_PERIOD = 10;

// Signals
reg clk;
reg rstn;
reg CE;
reg [2:0] OP_CODE;
reg [SIZE-1:0] left_operand;
reg [SIZE-1:0] right_operand;
reg carry_in;
wire carry_out;
wire [SIZE-1:0] op_out;

// Open log file
integer file_handle;

// Instantiate the DUT
ALU #(.SIZE(SIZE)) DUT (
    .CE(CE),
    .OP_CODE(OP_CODE),
    .left_operand(left_operand),
    .right_operand(right_operand),
    .carry_in(carry_in),
    .carry_out(carry_out),
    .op_out(op_out)
);

// Clock Generation
initial begin
    clk = 0;
    forever #(CLK_PERIOD / 2) clk = ~clk;
end

// Reset Process
initial begin
    // Initialize waveform dump
    $dumpfile("ALU.vcd");  // Create VCD file
    $dumpvars(0, ALU_TB);  // Dump all variables


    file_handle = $fopen("simulation.log", "w");
    if (!file_handle) begin
        $display("Error: Could not open log file");
        $finish;
    end

    // Initial message
    $display("Starting ALU testbench simulation");
    $fwrite(file_handle, "Starting ALU testbench simulation\n");

    // Apply reset
    rstn = 0;
    #20 rstn = 1;
    
    // Test Phase 1: ADD Operation
    $display("Starting Test Phase 1: ADD Operation");
    CE = 1;
    OP_CODE = OP_ADD; 
    left_operand = 8'b00000001;
    right_operand = 8'b00000001;
    carry_in = 0;
    repeat(10) @(posedge clk);
    
    // Test Phase 2: SUB Operation
    $display("Starting Test Phase 2: SUB Operation");
    CE = 1;
    OP_CODE = OP_SUB; 
    left_operand = 8'b00000010;
    right_operand = 8'b00000001;
    carry_in = 0;
    repeat(10) @(posedge clk);

    // Test Phase 3: AND Operation
    $display("Starting Test Phase 3: AND Operation");
    CE = 1;
    OP_CODE = OP_AND; 
    left_operand = 8'b11111111;
    right_operand = 8'b01010101;
    carry_in = 0;
    repeat(10) @(posedge clk);

    // Test Phase 4: OR Operation
    $display("Starting Test Phase 4: OR Operation");
    CE = 1;
    OP_CODE = OP_OR; 
    left_operand = 8'b10101010;
    right_operand = 8'b01010101;
    carry_in = 0;
    repeat(10) @(posedge clk);

    // Test Phase 5: XOR Operation
    $display("Starting Test Phase 5: XOR Operation");
    CE = 1;
    OP_CODE = OP_XOR; 
    left_operand = 8'b10101010;
    right_operand = 8'b01010101;
    carry_in = 0;
    repeat(10) @(posedge clk);

    // Test Phase 6: NOT Operation
    $display("Starting Test Phase 6: NOT Operation");
    CE = 1;
    OP_CODE = OP_NOT; 
    left_operand = 8'b10101010;
    right_operand = 8'b01010101;
    carry_in = 0;
    repeat(10) @(posedge clk);

    // Test Phase 7: LD Operation
    $display("Starting Test Phase 7: LD Operation");
    CE = 1;
    OP_CODE = OP_LD; 
    left_operand = 8'b10101010;
    right_operand = 8'b01010101;
    carry_in = 0;
    repeat(10) @(posedge clk);

    // Test Phase 8: ST Operation
    $display("Starting Test Phase 8: ST Operation");
    CE = 1;
    OP_CODE = OP_ST; 
    left_operand = 8'b10101010;
    right_operand = 8'b01010101;
    carry_in = 0;
    repeat(10) @(posedge clk);


    // Test Phase 9: loop calculation
    $display("Starting Test Phase 9: loop calculation");
    CE = 1;
    OP_CODE = OP_ADD; 
    left_operand = 8'b00000001;
    right_operand = 8'b00000001;
    carry_in = 0;
    repeat(1) @(posedge clk);
    right_operand = op_out;
    repeat(10) @(posedge clk);

    // Finish Simulation
    $display("Testbench completed at %0t ns", $time);
    if (file_handle) begin
        $fwrite(file_handle, "Testbench completed at %0t ns\n", $time);
        $fclose(file_handle);
    end

    $finish;
end

endmodule
