// ------------------------------------------------------------------
// Fetcher Module Testbench (CORRECTED)
//
// Purpose: Validate fetcher.sv performance and correctness
// Reference: dispatcher_control.sv orchestration pattern
//
// This version matches EXACT interfaces from working RTL
//
// Date: 2025-11-03
// ------------------------------------------------------------------

`timescale 1ns/1ps

`include "nap_interfaces.svh"

module tb_fetcher;

    // ====================================================================
    // Parameters (match dispatcher_control.sv)
    // ====================================================================
    localparam MAN_WIDTH = 256;
    localparam EXP_WIDTH = 8;
    localparam BRAM_DEPTH = 512;
    localparam AXI_ADDR_WIDTH = 42;
    localparam BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH);  // 9
    localparam TILE_ADDR_WIDTH = $clog2(BRAM_DEPTH);  // 9
    localparam [8:0] GDDR6_PAGE_ID = 9'd2;

    // ====================================================================
    // Clock and Reset
    // ====================================================================
    logic clk = 1'b0;
    logic reset_n;

    localparam CLK_PERIOD = 2.5;  // 400MHz
    always #(CLK_PERIOD/2) clk <= ~clk;

    // ====================================================================
    // Test Control
    // ====================================================================
    integer test_errors;
    integer cycle_count;
    integer fetch_left_cycles;
    integer fetch_right_cycles;

    // ====================================================================
    // AXI Interface (NAP to GDDR6)
    // ====================================================================
    t_AXI4 #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LEN_WIDTH(8),
        .ID_WIDTH(8)
    ) axi_nap();

    // ====================================================================
    // GDDR6 Memory Model (Realistic - 32 Outstanding Limit)
    // ====================================================================
    logic [31:0] mem_outstanding_count;
    logic [31:0] mem_total_ar_received;
    logic [31:0] mem_total_r_issued;

    tb_memory_model_realistic #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LINES_PER_BLOCK(528),
        .NUM_BLOCKS(2),
        .LATENCY_CYCLES(40),      // 100ns @ 400MHz = realistic GDDR6
        .MAX_OUTSTANDING(32),     // Achronix GDDR6 NoC limit
        .VERBOSITY(1)             // 0=quiet, 1=summary, 2=detailed
    ) u_gddr6_model (
        .i_clk(clk),
        .i_reset_n(reset_n),
        .axi_mem_if(axi_nap.responder),  // ← Memory is responder
        .o_outstanding_count(mem_outstanding_count),
        .o_total_ar_received(mem_total_ar_received),
        .o_total_r_issued(mem_total_r_issued)
    );

    // ====================================================================
    // Internal Signals (match dispatcher_control.sv pattern)
    // ====================================================================
    
    // Fetcher control
    logic                         fetch_en;
    logic [25:0]                  fetch_addr;    // link_addr_width_gp = 26
    logic [15:0]                  fetch_len;     // link_len_width_gp = 16
    logic                         fetch_target;  // 0=left, 1=right
    logic                         fetch_done;

    // Fetcher → Dispatcher BRAM Write (lines 106-118)
    logic [MAN_WIDTH-1:0]         fetcher_bram_wr_data;
    logic [BRAM_ADDR_WIDTH+2:0]   fetcher_bram_wr_addr;  // 11-bit
    logic                         fetcher_bram_wr_en;
    logic                         fetcher_bram_wr_target;

    // Fetcher → Dispatcher BRAM Exp Aligned Write
    logic [TILE_ADDR_WIDTH-1:0]   fetcher_exp_left_wr_addr;
    logic                         fetcher_exp_left_wr_en;
    logic [EXP_WIDTH-1:0]         fetcher_exp_left_wr_data;
    logic [TILE_ADDR_WIDTH-1:0]   fetcher_exp_right_wr_addr;
    logic                         fetcher_exp_right_wr_en;
    logic [EXP_WIDTH-1:0]         fetcher_exp_right_wr_data;

    // Fetcher ← Dispatcher BRAM Exp Packed Read
    logic [3:0]                   fetcher_exp_packed_rd_addr;
    logic                         fetcher_exp_packed_rd_target;
    logic [MAN_WIDTH-1:0]         dispatcher_bram_exp_packed_rd_data;

    // Testbench → Dispatcher BRAM Read (for verification)
    logic [BRAM_ADDR_WIDTH-1:0]   dispatcher_man_left_rd_addr;
    logic                         dispatcher_man_left_rd_en;
    logic [MAN_WIDTH-1:0]         dispatcher_bram_man_left_rd_data;
    logic [BRAM_ADDR_WIDTH-1:0]   dispatcher_man_right_rd_addr;
    logic                         dispatcher_man_right_rd_en;
    logic [MAN_WIDTH-1:0]         dispatcher_bram_man_right_rd_data;
    logic [TILE_ADDR_WIDTH-1:0]   dispatcher_exp_left_rd_addr;
    logic                         dispatcher_exp_left_rd_en;
    logic [EXP_WIDTH-1:0]         dispatcher_bram_exp_left_rd_data;
    logic [TILE_ADDR_WIDTH-1:0]   dispatcher_exp_right_rd_addr;
    logic                         dispatcher_exp_right_rd_en;
    logic [EXP_WIDTH-1:0]         dispatcher_bram_exp_right_rd_data;

    // ====================================================================
    // DUT: Fetcher Module - OPTIMIZED VERSION
    // ====================================================================
    fetcher_opt #(
        .MAN_WIDTH      (MAN_WIDTH),
        .EXP_WIDTH      (EXP_WIDTH),
        .BRAM_DEPTH     (BRAM_DEPTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .BRAM_ADDR_WIDTH(BRAM_ADDR_WIDTH),
        .TILE_ADDR_WIDTH(TILE_ADDR_WIDTH),
        .GDDR6_PAGE_ID  (GDDR6_PAGE_ID)
    ) u_fetcher (
        .i_clk                  (clk),
        .i_reset_n              (reset_n),
        .i_fetch_en             (fetch_en),
        .i_fetch_addr           (fetch_addr),
        .i_fetch_len            (fetch_len),
        .i_fetch_target         (fetch_target),
        .o_fetch_done           (fetch_done),
        .o_bram_wr_data         (fetcher_bram_wr_data),
        .o_bram_wr_addr         (fetcher_bram_wr_addr),
        .o_bram_wr_en           (fetcher_bram_wr_en),
        .o_bram_wr_target       (fetcher_bram_wr_target),
        .o_exp_left_wr_addr     (fetcher_exp_left_wr_addr),
        .o_exp_left_wr_en       (fetcher_exp_left_wr_en),
        .o_exp_left_wr_data     (fetcher_exp_left_wr_data),
        .o_exp_right_wr_addr    (fetcher_exp_right_wr_addr),
        .o_exp_right_wr_en      (fetcher_exp_right_wr_en),
        .o_exp_right_wr_data    (fetcher_exp_right_wr_data),
        .o_exp_packed_rd_addr   (fetcher_exp_packed_rd_addr),
        .o_exp_packed_rd_target (fetcher_exp_packed_rd_target),
        .i_exp_packed_rd_data   (dispatcher_bram_exp_packed_rd_data),
        .axi_ddr_if             (axi_nap.initiator),  // ← Fetcher is initiator
        .o_fetcher_state        (),  // Debug (unused)
        .o_wr_addr              (),  // Debug (unused)
        .o_wr_en                ()   // Debug (unused)
    );

    // ====================================================================
    // Dispatcher BRAM (exact instantiation from dispatcher_control.sv)
    // ====================================================================
    dispatcher_bram #(
        .MAN_WIDTH          (MAN_WIDTH),
        .EXP_WIDTH          (EXP_WIDTH),
        .EXP_PACKED_DEPTH   (16),
        .BRAM_DEPTH         (BRAM_DEPTH),
        .WR_ADDR_WIDTH      (BRAM_ADDR_WIDTH + 2),  // 11-bit
        .RD_ADDR_WIDTH      (BRAM_ADDR_WIDTH)        // 9-bit
    ) u_dispatcher_bram (
        .i_clk                  (clk),
        .i_reset_n              (reset_n),
        
        // Write ports (from fetcher)
        .i_wr_data              (fetcher_bram_wr_data),
        .i_wr_addr              (fetcher_bram_wr_addr),
        .i_wr_en                (fetcher_bram_wr_en),
        .i_wr_target            (fetcher_bram_wr_target),
        
        // Exp aligned write (from fetcher)
        .i_exp_left_wr_addr     (fetcher_exp_left_wr_addr),
        .i_exp_left_wr_en       (fetcher_exp_left_wr_en),
        .i_exp_left_wr_data     (fetcher_exp_left_wr_data),
        .i_exp_right_wr_addr    (fetcher_exp_right_wr_addr),
        .i_exp_right_wr_en      (fetcher_exp_right_wr_en),
        .i_exp_right_wr_data    (fetcher_exp_right_wr_data),
        
        // Read ports (to testbench for verification)
        .i_man_left_rd_addr     (dispatcher_man_left_rd_addr),
        .i_man_left_rd_en       (dispatcher_man_left_rd_en),
        .o_man_left_rd_data     (dispatcher_bram_man_left_rd_data),
        .i_man_right_rd_addr    (dispatcher_man_right_rd_addr),
        .i_man_right_rd_en      (dispatcher_man_right_rd_en),
        .o_man_right_rd_data    (dispatcher_bram_man_right_rd_data),
        .i_exp_left_rd_addr     (dispatcher_exp_left_rd_addr),
        .i_exp_left_rd_en       (dispatcher_exp_left_rd_en),
        .o_exp_left_rd_data     (dispatcher_bram_exp_left_rd_data),
        .i_exp_right_rd_addr    (dispatcher_exp_right_rd_addr),
        .i_exp_right_rd_en      (dispatcher_exp_right_rd_en),
        .o_exp_right_rd_data    (dispatcher_bram_exp_right_rd_data),
        
        // Exp packed read (for fetcher unpacking)
        .i_exp_packed_rd_addr   (fetcher_exp_packed_rd_addr),
        .i_exp_packed_rd_target (fetcher_exp_packed_rd_target),
        .o_exp_packed_rd_data   (dispatcher_bram_exp_packed_rd_data)
    );

    // ====================================================================
    // Golden Reference Storage
    // ====================================================================
    logic [EXP_WIDTH-1:0]   golden_left_exp[0:511];
    logic [MAN_WIDTH-1:0]   golden_left_man[0:511];
    logic [EXP_WIDTH-1:0]   golden_right_exp[0:511];
    logic [MAN_WIDTH-1:0]   golden_right_man[0:511];

    // ====================================================================
    // Tasks
    // ====================================================================
    task automatic run_fetch(
        input logic [25:0] start_addr,
        input logic        target,
        input string       test_name
    );
        integer start_cycle, duration;

        $display("\n========================================");
        $display("[TEST] %s", test_name);
        $display("[TEST] Address: 0x%07x (line %0d)", start_addr, start_addr);
        $display("[TEST] Target: %s", target ? "RIGHT" : "LEFT");
        $display("========================================");

        start_cycle = cycle_count;

        // Issue fetch command
        fetch_addr = start_addr;
        fetch_len = 16'd528;
        fetch_target = target;
        fetch_en = 1'b1;
        @(posedge clk);
        fetch_en = 1'b0;

        // Wait for completion
        wait(fetch_done == 1'b1);
        @(posedge clk);

        duration = cycle_count - start_cycle;
        $display("[TEST] Complete in %0d cycles (%.2f lines/cycle)", 
                 duration, 528.0/duration);

        if (target == 1'b0) fetch_left_cycles = duration;
        else fetch_right_cycles = duration;

        repeat(10) @(posedge clk);
    endtask

    task automatic capture_golden(input logic is_left);
        integer i;

        $display("[GOLDEN] Capturing %s matrix...", is_left ? "left" : "right");

        for (i = 0; i < 512; i++) begin
            if (is_left) begin
                dispatcher_exp_left_rd_addr = i[8:0];
                dispatcher_exp_left_rd_en = 1'b1;
                dispatcher_man_left_rd_addr = i[8:0];
                dispatcher_man_left_rd_en = 1'b1;
                @(posedge clk);
                @(posedge clk);  // Extra cycle for registered BRAM output
                golden_left_exp[i] = dispatcher_bram_exp_left_rd_data;
                golden_left_man[i] = dispatcher_bram_man_left_rd_data;
            end else begin
                dispatcher_exp_right_rd_addr = i[8:0];
                dispatcher_exp_right_rd_en = 1'b1;
                dispatcher_man_right_rd_addr = i[8:0];
                dispatcher_man_right_rd_en = 1'b1;
                @(posedge clk);
                @(posedge clk);  // Extra cycle for registered BRAM output
                golden_right_exp[i] = dispatcher_bram_exp_right_rd_data;
                golden_right_man[i] = dispatcher_bram_man_right_rd_data;
            end
        end
        
        dispatcher_exp_left_rd_en = 1'b0;
        dispatcher_man_left_rd_en = 1'b0;
        dispatcher_exp_right_rd_en = 1'b0;
        dispatcher_man_right_rd_en = 1'b0;
        
        $display("[GOLDEN] Capture complete");
    endtask

    task automatic verify_bram(
        input logic is_left,
        input string matrix_name
    );
        integer errors = 0;
        integer i;

        $display("\n[VERIFY] Checking %s matrix...", matrix_name);

        for (i = 0; i < 512; i++) begin
            if (is_left) begin
                dispatcher_exp_left_rd_addr = i[8:0];
                dispatcher_exp_left_rd_en = 1'b1;
                dispatcher_man_left_rd_addr = i[8:0];
                dispatcher_man_left_rd_en = 1'b1;
                @(posedge clk);
                @(posedge clk);  // Extra cycle for registered BRAM output

                if (dispatcher_bram_exp_left_rd_data !== golden_left_exp[i]) begin
                    $error("[VERIFY] %s exp[%0d]: got 0x%02x, expected 0x%02x",
                           matrix_name, i, dispatcher_bram_exp_left_rd_data, golden_left_exp[i]);
                    errors++;
                end
                if (dispatcher_bram_man_left_rd_data !== golden_left_man[i]) begin
                    $error("[VERIFY] %s man[%0d]: mismatch", matrix_name, i);
                    errors++;
                end
            end else begin
                dispatcher_exp_right_rd_addr = i[8:0];
                dispatcher_exp_right_rd_en = 1'b1;
                dispatcher_man_right_rd_addr = i[8:0];
                dispatcher_man_right_rd_en = 1'b1;
                @(posedge clk);
                @(posedge clk);  // Extra cycle for registered BRAM output

                if (dispatcher_bram_exp_right_rd_data !== golden_right_exp[i]) begin
                    $error("[VERIFY] %s exp[%0d]: got 0x%02x, expected 0x%02x",
                           matrix_name, i, dispatcher_bram_exp_right_rd_data, golden_right_exp[i]);
                    errors++;
                end
                if (dispatcher_bram_man_right_rd_data !== golden_right_man[i]) begin
                    $error("[VERIFY] %s man[%0d]: mismatch", matrix_name, i);
                    errors++;
                end
            end

            if (errors > 10) break;
        end
        
        dispatcher_exp_left_rd_en = 1'b0;
        dispatcher_man_left_rd_en = 1'b0;
        dispatcher_exp_right_rd_en = 1'b0;
        dispatcher_man_right_rd_en = 1'b0;
        
        if (errors == 0) begin
            $display("[VERIFY] %s: PASS", matrix_name);
        end else begin
            $display("[VERIFY] %s: FAIL (%0d errors)", matrix_name, errors);
            test_errors += errors;
        end
    endtask

    // ====================================================================
    // Main Test
    // ====================================================================
    initial begin
        reset_n = 1'b0;
        test_errors = 0;
        cycle_count = 0;
        fetch_en = 1'b0;
        fetch_addr = '0;
        fetch_len = '0;
        fetch_target = 1'b0;
        
        dispatcher_man_left_rd_addr = '0;
        dispatcher_man_left_rd_en = 1'b0;
        dispatcher_man_right_rd_addr = '0;
        dispatcher_man_right_rd_en = 1'b0;
        dispatcher_exp_left_rd_addr = '0;
        dispatcher_exp_left_rd_en = 1'b0;
        dispatcher_exp_right_rd_addr = '0;
        dispatcher_exp_right_rd_en = 1'b0;

        $display("\n===============================================");
        $display("FETCHER TESTBENCH - Golden Reference");
        $display("===============================================\n");

        repeat(10) @(posedge clk);
        reset_n = 1'b1;
        repeat(10) @(posedge clk);

        // Test 1: Fetch left
        run_fetch(26'd0, 1'b0, "FETCH LEFT (line 0)");
        capture_golden(1'b1);

        // Test 2: Fetch right
        run_fetch(26'd528, 1'b1, "FETCH RIGHT (line 528)");
        capture_golden(1'b0);

        // Verify
        $display("\n===============================================");
        $display("VERIFICATION");
        $display("===============================================");
        
        run_fetch(26'd0, 1'b0, "VERIFY LEFT");
        verify_bram(1'b1, "LEFT");

        run_fetch(26'd528, 1'b1, "VERIFY RIGHT");
        verify_bram(1'b0, "RIGHT");

        // Summary
        $display("\n===============================================");
        $display("PERFORMANCE SUMMARY");
        $display("===============================================");
        $display("Left:  %0d cycles (%.2f lines/cycle)", 
                 fetch_left_cycles, 528.0/fetch_left_cycles);
        $display("Right: %0d cycles (%.2f lines/cycle)", 
                 fetch_right_cycles, 528.0/fetch_right_cycles);
        $display("Memory reads: %0d", mem_total_r_issued);
        $display("===============================================");

        if (test_errors == 0) begin
            $display("\n*** TEST PASSED ***\n");
        end else begin
            $display("\n*** TEST FAILED (%0d errors) ***\n", test_errors);
        end

        $finish;
    end

    // Cycle counter
    always @(posedge clk) begin
        if (reset_n) cycle_count <= cycle_count + 1;
        else cycle_count <= 0;
    end

    // Timeout
    initial begin
        #(CLK_PERIOD * 100000);
        $error("[TB] Timeout!");
        $finish;
    end

endmodule
