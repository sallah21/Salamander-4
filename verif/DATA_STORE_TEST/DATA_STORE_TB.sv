`timescale 1ns / 1ps

module DATA_STORE_TB;
    // Parameters
    localparam SIZE = 8;
    localparam DATA_SIZE = 6;
    localparam ADDR_SIZE = 5;
    localparam CLK_PERIOD = 10;
    localparam ADDRES_STEP = 1;
    // Signals
    reg clk;
    reg rstn;
    reg W;
    reg [DATA_SIZE-1:0] DATA_WR;
    reg [ADDR_SIZE-1:0] ADDR;
    
    // For monitoring
    integer file_handle;
    
    // Instantiate the DUT
    top_level #(
        .SIZE(SIZE),
        .DATA_SIZE(DATA_SIZE),
        .ADDR_SIZE(ADDR_SIZE)
    ) DUT (
        .clk(clk),
        .rstn(rstn),
        .W(W),
        .DATA_WR(DATA_WR),
        .ADDR(ADDR)
    );

    // Clock Generation
    initial 
    begin
        clk = 0;
        forever 
            #(CLK_PERIOD/2) clk = ~clk;
    end

    // Write to instruction memory
    task write_instruction;
        input [5:0] instruction;
        input [4:0] address;
        begin
            W = 1;
            DATA_WR = instruction;
            ADDR = address;
            #(CLK_PERIOD * ADDRES_STEP);
            W = 0;
        end
    endtask
    // Test stimulus
    initial 
    begin
        // Open VCD file
        $dumpfile("DATA_STORE_TEST.vcd");
        $dumpvars(0, DATA_STORE_TB);
        
        // Initialize signals
        rstn = 0;
        W = 0;
        DATA_WR = 0;
        ADDR = 0;
        
        // Reset sequence
        #(CLK_PERIOD * 2);
        rstn = 1;
        #(CLK_PERIOD * 2);

        // Test 1: Store value 0x55 to register 0
        // First load 0x55 to accumulator through instruction
        write_instruction(
        {
            2'b00, // Register 0 address
            OP_LD, // Load accumulator to register
            1'b1   // Accumulator  enable
         },
            5'd0);
            
        // Write 0x00 to instruction memory

        // Execute ST operation to store accumulator value to register 0
        @(posedge clk);

        
        // Test 2: Load value from register 0 to accumulator
        @(posedge clk);

        
        // Test 3: Store value 0xAA to register 1
        @(posedge clk);

        
        @(posedge clk);

        
        // Test 4: Load value from register 1 to accumulator
        @(posedge clk);

        
        // Add monitoring messages
        $display("Test 1: Stored 0x55 to register 0");
        $display("Test 2: Loaded value from register 0: 0x%h", DUT.ALU_out_val_w);
        $display("Test 3: Stored 0xAA to register 1");
        $display("Test 4: Loaded value from register 1: 0x%h", DUT.ALU_out_val_w);
        
        // End simulation
        #(CLK_PERIOD * 2);
        $finish;
    end
    
    // Monitor changes
    always @(DUT.ALU_out_val_w)
        $display("Time %0t: Accumulator value changed to 0x%h", $time, DUT.ALU_out_val_w);
        
    always @(DUT.REG_FILE_DATA_OUT_w)
        $display("Time %0t: Register file output changed to 0x%h", $time, DUT.REG_FILE_DATA_OUT_w);

endmodule
