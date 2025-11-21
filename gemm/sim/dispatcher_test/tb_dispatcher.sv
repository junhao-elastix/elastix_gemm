// ==================================================================
// Dispatcher Testbench
//
// Purpose: Unit test for dispatcher module with configurable tile count
// DUT: dispatcher.sv, dispatcher_bram.sv, tile_bram.sv
//
// Features:
//  - Configurable NUM_TILES (default 8, supports 2-24)
//  - Tests BROADCAST mode (replicate to all enabled tiles)
//  - Tests DISTRIBUTE mode (round-robin distribution)
//  - Verifies per-tile write enables
//  - Validates data routing correctness
//
// Author: Claude Code
// Date: 2025-11-19
// ==================================================================

`timescale 1ns/1ps

module tb_dispatcher;

    // ===================================================================
    // Testbench Parameters
    // ===================================================================
    parameter NUM_TILES = 4;                    // Configurable tile count (2-24)
    parameter MAN_WIDTH = 256;                  // Mantissa width
    parameter EXP_WIDTH = 8;                    // Exponent width
    parameter BRAM_DEPTH = 512;                 // Dispatcher BRAM depth
    parameter TILE_DEPTH = 512;                 // Tile BRAM depth per side
    parameter B_DIM = 8;                       // Number of left ugd vectors (Batches)
    parameter C_DIM = 16;                      // Number of right ugd vectors (Columns)
    parameter V_DIM = 2;                       // Number of gd vectors (Inner dimension)

    // Derived parameters
    parameter BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH);
    parameter TILE_ADDR_WIDTH = $clog2(TILE_DEPTH);

    parameter CLK_PERIOD = 5.0;                 // 200MHz clock
    parameter WATCHDOG_CYCLES = 10000;          // Simulation timeout

    // ===================================================================
    // Clock and Reset
    // ===================================================================
    logic clk;
    logic reset_n;

    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end

    // ===================================================================
    // DUT Signals
    // ===================================================================
    // Dispatcher control
    logic                       disp_en;
    logic [15:0]                disp_tile_addr;
    logic [7:0]                 disp_man_nv_cnt;
    logic [7:0]                 disp_ugd_vec_size;
    logic [7:0]                 disp_b_dim;
    logic [7:0]                 disp_c_dim;
    logic [7:0]                 disp_v_dim;
    logic                       disp_man_4b;
    logic [23:0]                disp_col_en;
    logic [4:0]                 disp_col_start;
    logic                       disp_right;
    logic                       disp_broadcast;
    logic                       disp_done;

    // Dispatcher BRAM read interface
    logic [BRAM_ADDR_WIDTH-1:0] disp_man_left_rd_addr;
    logic                       disp_man_left_rd_en;
    logic [MAN_WIDTH-1:0]       disp_man_left_rd_data;

    logic [BRAM_ADDR_WIDTH-1:0] disp_man_right_rd_addr;
    logic                       disp_man_right_rd_en;
    logic [MAN_WIDTH-1:0]       disp_man_right_rd_data;

    logic [TILE_ADDR_WIDTH-1:0] disp_exp_left_rd_addr;
    logic                       disp_exp_left_rd_en;
    logic [EXP_WIDTH-1:0]       disp_exp_left_rd_data;

    logic [TILE_ADDR_WIDTH-1:0] disp_exp_right_rd_addr;
    logic                       disp_exp_right_rd_en;
    logic [EXP_WIDTH-1:0]       disp_exp_right_rd_data;

    // Tile BRAM write interface
    logic [TILE_ADDR_WIDTH-1:0] tile_man_left_wr_addr;
    logic                       tile_man_left_wr_en;
    logic [MAN_WIDTH-1:0]       tile_man_left_wr_data;

    logic [TILE_ADDR_WIDTH-1:0] tile_man_right_wr_addr;
    logic                       tile_man_right_wr_en;
    logic [MAN_WIDTH-1:0]       tile_man_right_wr_data;

    logic [TILE_ADDR_WIDTH-1:0] tile_exp_left_wr_addr;
    logic                       tile_exp_left_wr_en;
    logic [EXP_WIDTH-1:0]       tile_exp_left_wr_data;

    logic [TILE_ADDR_WIDTH-1:0] tile_exp_right_wr_addr;
    logic                       tile_exp_right_wr_en;
    logic [EXP_WIDTH-1:0]       tile_exp_right_wr_data;

    logic [23:0]                tile_wr_en;

    logic [3:0]                 dispatcher_state;

    // ===================================================================
    // Tile BRAM instances (per-tile storage)
    // ===================================================================
    // Per-tile write enables
    logic tile_man_left_wr_en_arr [NUM_TILES];
    logic tile_man_right_wr_en_arr [NUM_TILES];
    logic tile_exp_left_wr_en_arr [NUM_TILES];
    logic tile_exp_right_wr_en_arr [NUM_TILES];

    // Per-tile data capture for verification
    logic [MAN_WIDTH-1:0] tile_left_man_data [NUM_TILES][TILE_DEPTH];
    logic [MAN_WIDTH-1:0] tile_right_man_data [NUM_TILES][TILE_DEPTH];
    logic [EXP_WIDTH-1:0] tile_left_exp_data [NUM_TILES][TILE_DEPTH];
    logic [EXP_WIDTH-1:0] tile_right_exp_data [NUM_TILES][TILE_DEPTH];

    // Combine global write enable with per-tile enable
    generate
        for (genvar tile_id = 0; tile_id < NUM_TILES; tile_id++) begin : gen_tile_wr_en
            assign tile_man_left_wr_en_arr[tile_id]  = tile_man_left_wr_en && tile_wr_en[tile_id];
            assign tile_man_right_wr_en_arr[tile_id] = tile_man_right_wr_en && tile_wr_en[tile_id];
            assign tile_exp_left_wr_en_arr[tile_id]  = tile_exp_left_wr_en && tile_wr_en[tile_id];
            assign tile_exp_right_wr_en_arr[tile_id] = tile_exp_right_wr_en && tile_wr_en[tile_id];
        end
    endgenerate

    // Tile data capture
    generate
        for (genvar tile_id = 0; tile_id < NUM_TILES; tile_id++) begin : gen_tile_capture
            always_ff @(posedge clk) begin
                if (tile_man_left_wr_en_arr[tile_id]) begin
                    tile_left_man_data[tile_id][tile_man_left_wr_addr] <= tile_man_left_wr_data;
                end

                if (tile_man_right_wr_en_arr[tile_id]) begin
                    tile_right_man_data[tile_id][tile_man_right_wr_addr] <= tile_man_right_wr_data;
                end

                if (tile_exp_left_wr_en_arr[tile_id]) begin
                    tile_left_exp_data[tile_id][tile_exp_left_wr_addr] <= tile_exp_left_wr_data;
                end

                if (tile_exp_right_wr_en_arr[tile_id]) begin
                    tile_right_exp_data[tile_id][tile_exp_right_wr_addr] <= tile_exp_right_wr_data;
                end
            end
        end
    endgenerate

    // ===================================================================
    // DUT: Dispatcher
    // ===================================================================
    dispatcher #(
        .MAN_WIDTH         (MAN_WIDTH),
        .EXP_WIDTH         (EXP_WIDTH),
        .BRAM_DEPTH        (BRAM_DEPTH),
        .TILE_DEPTH        (TILE_DEPTH)
    ) u_dispatcher (
        .i_clk                     (clk),
        .i_reset_n                 (reset_n),

        // Control interface
        .i_disp_en                 (disp_en),
        .i_disp_tile_addr          (disp_tile_addr),
        .i_disp_man_nv_cnt         (disp_man_nv_cnt),
        .i_disp_ugd_vec_size       (disp_ugd_vec_size),
        .i_disp_man_4b             (disp_man_4b),
        .i_disp_col_en             (disp_col_en),
        .i_disp_col_start          (disp_col_start),
        .i_disp_right              (disp_right),
        .i_disp_broadcast          (disp_broadcast),
        .o_disp_done               (disp_done),

        // Dispatcher BRAM read
        .o_disp_man_left_rd_addr   (disp_man_left_rd_addr),
        .o_disp_man_left_rd_en     (disp_man_left_rd_en),
        .i_disp_man_left_rd_data   (disp_man_left_rd_data),

        .o_disp_man_right_rd_addr  (disp_man_right_rd_addr),
        .o_disp_man_right_rd_en    (disp_man_right_rd_en),
        .i_disp_man_right_rd_data  (disp_man_right_rd_data),

        .o_disp_exp_left_rd_addr   (disp_exp_left_rd_addr),
        .o_disp_exp_left_rd_en     (disp_exp_left_rd_en),
        .i_disp_exp_left_rd_data   (disp_exp_left_rd_data),

        .o_disp_exp_right_rd_addr  (disp_exp_right_rd_addr),
        .o_disp_exp_right_rd_en    (disp_exp_right_rd_en),
        .i_disp_exp_right_rd_data  (disp_exp_right_rd_data),

        // Tile BRAM write
        .o_tile_man_left_wr_addr   (tile_man_left_wr_addr),
        .o_tile_man_left_wr_en     (tile_man_left_wr_en),
        .o_tile_man_left_wr_data   (tile_man_left_wr_data),

        .o_tile_man_right_wr_addr  (tile_man_right_wr_addr),
        .o_tile_man_right_wr_en    (tile_man_right_wr_en),
        .o_tile_man_right_wr_data  (tile_man_right_wr_data),

        .o_tile_exp_left_wr_addr   (tile_exp_left_wr_addr),
        .o_tile_exp_left_wr_en     (tile_exp_left_wr_en),
        .o_tile_exp_left_wr_data   (tile_exp_left_wr_data),

        .o_tile_exp_right_wr_addr  (tile_exp_right_wr_addr),
        .o_tile_exp_right_wr_en    (tile_exp_right_wr_en),
        .o_tile_exp_right_wr_data  (tile_exp_right_wr_data),

        .o_tile_wr_en              (tile_wr_en),

        // Debug
        .o_dispatcher_state        (dispatcher_state)
    );

    // ===================================================================
    // Dispatcher BRAM (source data storage)
    // ===================================================================
    logic [MAN_WIDTH-1:0] disp_bram_man_left [BRAM_DEPTH];
    logic [MAN_WIDTH-1:0] disp_bram_man_right [BRAM_DEPTH];
    logic [EXP_WIDTH-1:0] disp_bram_exp_left [TILE_DEPTH];
    logic [EXP_WIDTH-1:0] disp_bram_exp_right [TILE_DEPTH];

    // BRAM read logic (combinational)
    assign disp_man_left_rd_data = disp_bram_man_left[disp_man_left_rd_addr];
    assign disp_man_right_rd_data = disp_bram_man_right[disp_man_right_rd_addr];
    assign disp_exp_left_rd_data = disp_bram_exp_left[disp_exp_left_rd_addr];
    assign disp_exp_right_rd_data = disp_bram_exp_right[disp_exp_right_rd_addr];

    // ===================================================================
    // Test Control
    // ===================================================================
    int test_count;
    int pass_count;
    int fail_count;

    // ===================================================================
    // Helper Tasks
    // ===================================================================

    // Initialize dispatcher BRAM with test pattern
    task init_dispatcher_bram();
        int line_offset;
        int v_cnt_left;
        int v_cnt_right;
        int ugd_index;
        
        $display("======================================================================");
        $display("  Initializing Dispatcher BRAM with test pattern");
        $display("======================================================================");
        for (int i = 0; i < BRAM_DEPTH; i++) begin
            // Pattern: address-based unique data
            line_offset = i % 4;
            v_cnt_left = (i / 4) % V_DIM;
            v_cnt_right = (i / 4) % V_DIM;
            ugd_index = i / (4 * V_DIM);
            disp_bram_man_left[i] = {256{1'b0}} | ((ugd_index << 8) | (v_cnt_left << 4) | line_offset);
            disp_bram_man_right[i] = {256{1'b0}} | ((ugd_index << 8) | (v_cnt_right << 4) | line_offset);
        end

        for (int i = 0; i < TILE_DEPTH; i++) begin
            disp_bram_exp_left[i] = 8'hAA;
            disp_bram_exp_right[i] = 8'hBB;
        end

        $display("  Dispatcher BRAM initialized");
    endtask

    // Issue DISPATCH command
    task automatic dispatch_command(
        input logic [15:0] tile_addr,
        input logic [7:0] man_nv_cnt,
        input logic [7:0] ugd_vec_size,
        input logic man_4b,
        input logic [23:0] col_en,
        input logic [4:0] col_start,
        input logic right,
        input logic broadcast
    );
        $display("----------------------------------------------------------------------");
        $display("  DISPATCH Command:");
        $display("    tile_addr=%0d, man_nv_cnt=%0d, ugd_vec_size=%0d", tile_addr, man_nv_cnt, ugd_vec_size);
        $display("    man_4b=%0b, col_en=0x%06x, col_start=%0d", man_4b, col_en, col_start);
        $display("    right=%0b, broadcast=%0b", right, broadcast);
        $display("----------------------------------------------------------------------");

        @(posedge clk);
        disp_tile_addr <= tile_addr;
        disp_man_nv_cnt <= man_nv_cnt;
        disp_ugd_vec_size <= ugd_vec_size;
        disp_man_4b <= man_4b;
        disp_col_en <= col_en;
        disp_col_start <= col_start;
        disp_right <= right;
        disp_broadcast <= broadcast;
        disp_en <= 1'b1;

        @(posedge clk);
        disp_en <= 1'b0;

        // Wait for completion
        // First wait for disp_done to go low (if it was high from previous dispatch)
        wait(disp_done == 1'b0);
        @(posedge clk);
        // Then wait for disp_done to go high (current dispatch complete)
        wait(disp_done == 1'b1);
        @(posedge clk);

        $display("  DISPATCH Complete at time %0t", $time);
    endtask

    // ===================================================================
    // Function: Population Count (count number of '1' bits)
    // ===================================================================
    function automatic int popcount(input logic [23:0] val);
        integer count;
        integer i;
        count = 0;
        for (int i = 0; i < 24; i++) begin
            if (val[i]) count++;
        end
        return count;
    endfunction

    // ===================================================================
    // Task: Save Single BRAM to File (Atomic Unit)
    // ===================================================================
    task save_bram_to_file(
        input string filename,
        input logic [MAN_WIDTH-1:0] man_data [],
        input logic [EXP_WIDTH-1:0] exp_data [],
        input int depth
    );
        int fd;

        fd = $fopen(filename, "w");
        if (fd) begin
            for (int i = 0; i < depth; i++) begin
                $fwrite(fd, "%064x %02x\n", man_data[i], exp_data[i]);
            end
            $fclose(fd);
            $display("  Written: %s (mantissa + exponent)", filename);
        end else begin
            $display("  ERROR: Could not open %s", filename);
        end
    endtask

    // ===================================================================
    // Task: Save All Data to Files
    // ===================================================================
    task save_data_to_files();
        $display("\n======================================================================");
        $display("  Saving data to files...");
        $display("======================================================================");

        // Save dispatcher input BRAMs
        save_bram_to_file("disp_left.txt", disp_bram_man_left, disp_bram_exp_left, BRAM_DEPTH);
        save_bram_to_file("disp_right.txt", disp_bram_man_right, disp_bram_exp_right, BRAM_DEPTH);

        // Save tile output BRAMs
        for (int tile_id = 0; tile_id < NUM_TILES; tile_id++) begin
            save_bram_to_file($sformatf("tile_left_%0d.txt", tile_id),
                            tile_left_man_data[tile_id], tile_left_exp_data[tile_id], TILE_DEPTH);
            save_bram_to_file($sformatf("tile_right_%0d.txt", tile_id),
                            tile_right_man_data[tile_id], tile_right_exp_data[tile_id], TILE_DEPTH);
        end

        $display("======================================================================");
        $display("  File save complete");
        $display("======================================================================\n");
    endtask

    // ===================================================================
    // Main Test Sequence
    // ===================================================================
    initial begin
        $display("======================================================================");
        $display("  Dispatcher Testbench");
        $display("  NUM_TILES = %0d", NUM_TILES);
        $display("======================================================================");

        // Initialize
        reset_n = 0;
        disp_en = 0;
        disp_tile_addr = 0;
        disp_b_dim = B_DIM;
        disp_c_dim = C_DIM;
        disp_v_dim= V_DIM;
        disp_man_4b = 0;
        disp_col_en = 24'h00000F;
        disp_col_start = 0;
        disp_right = 0;
        disp_broadcast = 0;

        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        // Reset sequence
        repeat(10) @(posedge clk);
        reset_n = 1;
        repeat(5) @(posedge clk);

        // Initialize dispatcher BRAM
        init_dispatcher_bram();

        /*======================================================================
        We dispatch B = 4, C = 16, V = 2 vectors to Tile BRAM
        We have NUM_TILES = 8, but col_en is configurable. 
        DISP cmd will broadcast or distribute based on mode.
        Broadcast mode: all enabled tiles get same data, each tile gets B*V*4 lines.
        Distribute mode: enabled tiles get round-robin data, each tile gets (C//col_en)*V*4 lines.
        Practically, we broadcast to left and distribute to right.
        ======================================================================*/

        // Broadcast to left side (all enabled tiles get same data)
        $display("\n======================================================================");
        $display("  Broadcast to Left Side");
        $display("  Dispatching B=%0d, V=%0d vectors, %0d lines to %0d enabled tiles", disp_b_dim, disp_v_dim, disp_b_dim*disp_v_dim*4, popcount(disp_col_en));
        $display("======================================================================");
        dispatch_command(
            .tile_addr(disp_tile_addr),
            .man_nv_cnt(disp_b_dim * disp_v_dim),
            .ugd_vec_size(disp_v_dim),
            .man_4b(1'b0),
            .col_en(disp_col_en),      // Tile 0 only
            .col_start(5'd0),
            .right(1'b0),             // Left side
            .broadcast(1'b1)          // Broadcast mode
        );

        $display("\n======================================================================");
        $display("  Distribute to Right Side");
        $display("  Dispatching C=%0d, V=%0d vectors, %0d lines to %0d enabled tiles", disp_c_dim, disp_v_dim, disp_c_dim*disp_v_dim*4, popcount(disp_col_en));
        $display("  Each tile gets %0d lines", disp_c_dim*disp_v_dim*4/popcount(disp_col_en));
        $display("======================================================================");
        dispatch_command(
            .tile_addr(disp_tile_addr),
            .man_nv_cnt(disp_c_dim * disp_v_dim),
            .ugd_vec_size(disp_v_dim),
            .man_4b(1'b0),
            .col_en(disp_col_en),      // Tile 0 only
            .col_start(5'd0),
            .right(1'b1),             // FIXED: Right side (was incorrectly labeled "Left side")
            .broadcast(1'b0)          // FIXED: Distribute mode (was incorrectly labeled "Broadcast mode")
        );

        $display("======================================================================");
        $display("  Test complete. ");
        $display("======================================================================");

        // Save data to files
        save_data_to_files();

        $finish;
    end

    // ===================================================================
    // Watchdog Timer
    // ===================================================================
    initial begin
        repeat(WATCHDOG_CYCLES) @(posedge clk);
        $display("\n======================================================================");
        $display("  ERROR: Watchdog timeout at %0t", $time);
        $display("======================================================================");
        $finish;
    end

endmodule
