`timescale 1ns / 1ps
//----------------------------------------------------------
// Transaction class for ALU
//----------------------------------------------------------
class transaction;

    parameter DATA_WIDTH = 8;
    parameter ALU_OP_BITS = 4;

    rand bit [DATA_WIDTH-1:0] acc;
    rand bit [DATA_WIDTH-1:0] src;
    rand bit [ALU_OP_BITS-1:0] op;
    rand bit carry_flag;
    rand bit temp_result;

    constraint op_in_range { op <= 4'b1111 && op >= 4'b0000; } // op must be 4 bits (0 to 15)
endclass


//----------------------------------------------------------
// Generator class
//----------------------------------------------------------
class generator;

    event trans_rdy;
    mailbox gen_mb;

    rand transaction trans;
    int test_num;

    function new(event trans_event, mailbox gen_mailbox);
        this.trans_rdy = trans_event;
        this.gen_mb = gen_mailbox;
    endfunction

    task gen();
        repeat (test_num) begin
            trans = new();
            trans.randomize();
            $display("Generated transaction: %p", trans);
            gen_mb.put(trans);
            $display("Transaction sent to generator");
        end
        -> trans_rdy;
    endtask

endclass


//----------------------------------------------------------
// ALU interface
//----------------------------------------------------------

interface alu_intf(input logic clk, reset);

    parameter DATA_WIDTH = 8;
    parameter ALU_OP_BITS = 4;

    // ALU inputs
    logic [DATA_WIDTH-1:0] acc;
    logic [DATA_WIDTH-1:0] src;
    logic [ALU_OP_BITS-1:0] alu_op;
    logic carry_flag;

    // ALU outputs
    logic [DATA_WIDTH-1:0] temp_result;

    // Monitor clock
    clocking mon_clk @(posedge clk);
        default input #1 output #1;
        input acc;
        input src;
        input alu_op;
        input carry_flag;
        input temp_result;
    endclocking

    // Driver clock
    clocking drv_clk @(posedge clk);
        default input #1 output #1;
        output acc;
        output src;
        output alu_op;
        output carry_flag;
    endclocking

    // Monitor modport
    modport mon_mode (clocking mon_clk, input clk, input reset);    

    // Driver modport
    modport drv_mode (clocking drv_clk, input clk, input reset);

endinterface

//----------------------------------------------------------
// Driver class
//----------------------------------------------------------

class driver;
    integer trans_num;
    virtual alu_intf.drv_mode vif;
    mailbox gen_mb;
    
    function new(virtual alu_intf.drv_mode vif, mailbox gen_mb);
        this.vif = vif;
        this.gen_mb = gen_mb;
        this.trans_num = 0;
    endfunction
    
    task reset();
        vif.drv_clk.acc <= 0;
        vif.drv_clk.src <= 0;
        vif.drv_clk.alu_op <= 0;
        vif.drv_clk.carry_flag <= 0;
    endtask

    task drive();
        transaction trans;
        forever begin
            gen_mb.get(trans);
            @(posedge vif.clk);
            vif.drv_clk.acc <= trans.acc;
            vif.drv_clk.src <= trans.src;
            vif.drv_clk.alu_op <= trans.op;
            vif.drv_clk.carry_flag <= trans.carry_flag;
            this.trans_num++;
        end
    endtask
endclass


//----------------------------------------------------------
// Monitor class
//----------------------------------------------------------

class monitor;
    virtual alu_intf.mon_mode vif;
    mailbox mon_mb;
    int trans_num;
    transaction last_trans;

    function new(virtual alu_intf.mon_mode vif, mailbox mon_mb);
        this.vif = vif;
        this.mon_mb = mon_mb;
        this.trans_num = 0;
        this.last_trans = new();
    endfunction

    task monitor();
        forever begin
            transaction trans = new();
            @(posedge vif.clk);
            
            // Sample signals using the monitor clocking block
            trans.acc = vif.mon_clk.acc;
            trans.src = vif.mon_clk.src;
            trans.op = vif.mon_clk.alu_op;
            trans.carry_flag = vif.mon_clk.carry_flag;
            trans.temp_result = vif.mon_clk.temp_result;
            
            mon_mb.put(trans);
            last_trans = trans;
            this.trans_num++;
            
            $display("[MON] Monitored transaction: acc=%h, src=%h, op=%h, cf=%b, result=%h", 
                     trans.acc, trans.src, trans.op, trans.carry_flag, trans.temp_result);
        end
    endtask
endclass 

//----------------------------------------------------------
// Scoreboard class
//----------------------------------------------------------

class scoreboard;
    parameter DATA_W = 8;
    parameter ALU_OP_BITS = 4;  // Added missing parameter
    mailbox mon_mb;
    int trans_num;

    logic [DATA_W-1:0] acu_value;

    function new(mailbox mon_mb);
        this.mon_mb = mon_mb;
        this.acu_value = 0;
        this.trans_num = 0;
    endfunction

    // Operation codes
    localparam [ALU_OP_BITS-1:0]
        OP_PASS = 4'b0000,
        OP_ADD  = 4'b0001,
        OP_SUB  = 4'b0010,
        OP_INC  = 4'b0011,
        OP_DEC  = 4'b0100,
        OP_RL   = 4'b0101,
        OP_RR   = 4'b0110,
        OP_AND  = 4'b0111,
        OP_OR   = 4'b1000,
        OP_XOR  = 4'b1001,
        OP_NOT  = 4'b1010;

    // Main task
    task main();
        transaction trans;
        logic [DATA_W-1:0] expected_op_out;
        forever begin
            #100; // wait for transaction
            $display("[SCRBD] Waiting for mail from monitor");
            mon_mb.get(trans);
            $display("[SCRBD] Mail received: %p, a=%h", trans, acu_value);
            case (trans.op)
                OP_PASS: expected_op_out = {1'b0, trans.src};
                OP_ADD: expected_op_out = acu_value + trans.src + trans.carry_flag;
                OP_SUB: expected_op_out = acu_value - trans.src - trans.carry_flag;
                OP_INC: expected_op_out = acu_value + 1'b1;
                OP_DEC: expected_op_out = acu_value - 1'b1;
                OP_RL:  expected_op_out = {acu_value[DATA_W-2:0], acu_value[DATA_W-1]};
                OP_RR:  expected_op_out = {acu_value[0], acu_value[DATA_W-1:1]};
                OP_AND: expected_op_out = acu_value & trans.src;
                OP_OR:  expected_op_out = acu_value | trans.src;
                OP_XOR: expected_op_out = acu_value ^ trans.src;
                OP_NOT: expected_op_out = ~acu_value;
                default: $error("[SCRBD] Invalid operation code: %b", trans.op);
            endcase
            acu_value = expected_op_out;
            if (expected_op_out !== trans.temp_result) begin
                $error("[SCRBD] INVALID TEMP_RESULT!! EXPECTED: %h, GOT: %h", expected_op_out, trans.temp_result);
            end
            this.trans_num++;
        end

    endtask
endclass

//----------------------------------------------------------
// Environment class
//----------------------------------------------------------

class environment;  
    mailbox gen_mb;
    mailbox mon_mb;
    scoreboard scrbd;
    driver drv;
    generator gen;
    monitor mon;
    event gen_ended;
    virtual alu_intf vif;
    
    // Constructor
    function new(virtual alu_intf vif);
        this.vif = vif;
        gen_mb = new();
        mon_mb = new();
        scrbd = new(mon_mb);
        drv = new(vif, gen_mb);
        gen = new(gen_ended, gen_mb);
        mon = new(vif, mon_mb);
    endfunction

    task reset();
        drv.reset();
    endtask

    task start_test();
        fork
            gen.gen();
            drv.drive();
            mon.monitor();
            scrbd.main(); 
        join_any
    endtask

    task end_test();
        wait(gen_ended.triggered);
        wait(gen.test_num == drv.trans_num);
        wait(gen.test_num == mon.trans_num);
    endtask

    task main();
        $display("[ENV] Starting test");
        $display("[ENV] reset env");
        reset();
        $display("[ENV] start test");
        start_test();
        $display("[ENV] end test");
        end_test();
        $display("[ENV] Test finished");
        $stop;
    endtask
endclass


//----------------------------------------------------------
// Test program 
//----------------------------------------------------------

program test(alu_intf intf);
    environment env;

    initial begin
        env = new(intf);
        env.gen.test_num = 20;
        env.main();
    end
endprogram

//----------------------------------------------------------
// ALU verification top level
//----------------------------------------------------------

module ALU_verif_top;
    parameter DATA_W = 8;
    parameter ALU_OP_W = 4;
    bit clk;
    bit reset;
    
    // System clock generation
    always #5 clk = ~clk;

    // Reset generation
    initial begin
        reset = 1;
        #5 reset = 0;
    end

    // ALU interface instantiation
    alu_intf intf(clk, reset);

    // Test program instantiation
    test test1(intf);

    // DUT instantiation
    alu #(
        .DATA_WIDTH(DATA_W),
        .ALU_OP_BITS(ALU_OP_W)
    ) alu_dut(
        .acc(intf.acc),
        .src(intf.src),
        .alu_op(intf.alu_op),
        .carry_flag(intf.carry_flag),
        .temp_result(intf.temp_result)
    );

endmodule