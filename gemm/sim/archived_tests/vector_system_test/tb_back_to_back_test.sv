// Simple back-to-back test to reproduce shift bug
// Runs 3 tests without reset, like hardware Stage 2

`timescale 1ns/1ps
`include "nap_interfaces.svh"

module tb_back_to_back_test;
    import gemm_pkg::*;
    
    localparam CLK_PERIOD = 10;
    
    logic clk, reset_n;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // DUT signals
    logic [31:0]  cmd_fifo_wdata;
    logic         cmd_fifo_wen;
    logic         cmd_fifo_full;
    logic [15:0]  result_fifo_rdata;
    logic         result_fifo_ren;
    logic         result_fifo_empty;
    
    // Result packer signals
    logic [8:0]   result_bram_wr_addr;
    logic [255:0] result_bram_wr_data;
    logic         result_bram_wr_en;
    logic [31:0]  result_bram_wr_strobe;
    logic [15:0]  result_0, result_1, result_2, result_3;
    logic [12:0]  result_rd_ptr = 13'b0;
    logic [12:0]  result_wr_ptr;
    logic [13:0]  result_used_entries;
    
    // BRAM model
    logic [255:0] result_bram_model [0:511];
    
    // Instantiate result packer
    result_fifo_to_simple_bram u_packer (
        .i_clk(clk),
        .i_reset_n(reset_n),
        .i_fifo_rdata(result_fifo_rdata),
        .o_fifo_ren(result_fifo_ren),
        .i_fifo_empty(result_fifo_empty),
        .o_bram_wr_addr(result_bram_wr_addr),
        .o_bram_wr_data(result_bram_wr_data),
        .o_bram_wr_en(result_bram_wr_en),
        .o_bram_wr_strobe(result_bram_wr_strobe),
        .o_result_0(result_0),
        .o_result_1(result_1),
        .o_result_2(result_2),
        .o_result_3(result_3),
        .i_rd_ptr(result_rd_ptr),
        .o_wr_ptr(result_wr_ptr),
        .o_used_entries(result_used_entries),
        .o_empty(),
        .o_almost_full()
    );
    
    // BRAM write capture
    always_ff @(posedge clk) begin
        if (result_bram_wr_en) begin
            for (int i = 0; i < 32; i++) begin
                if (result_bram_wr_strobe[i])
                    result_bram_model[result_bram_wr_addr][i*8 +: 8] <= result_bram_wr_data[i*8 +: 8];
            end
            $display("[BRAM WRITE] @%0t addr=%0d, wr_ptr=%0d, strobe=0x%08x", 
                     $time, result_bram_wr_addr, result_wr_ptr, result_bram_wr_strobe);
        end
    end
    
    // Simple FIFO emulator - produces test data
    logic [15:0] test_data[$];
    int test_idx = 0;
    
    assign result_fifo_empty = (test_data.size() == 0);
    assign result_fifo_rdata = (test_data.size() > 0) ? test_data[0] : 16'h0;
    
    always_ff @(posedge clk) begin
        if (result_fifo_ren && !result_fifo_empty) begin
            $display("[FIFO READ] @%0t data=0x%04x, remaining=%0d", $time, test_data[0], test_data.size()-1);
            void'(test_data.pop_front());
        end
    end
    
    // Test sequence
    initial begin
        $display("\n=== BACK-TO-BACK TEST (Reproducing Hardware Stage 2) ===\n");
        reset_n = 0;
        #100;
        reset_n = 1;
        #50;
        
        $display("[TEST 1] Starting B1_C1_V1 (expect 1 result)");
        $display("  Before: wr_ptr=%0d, rd_ptr=%0d, used=%0d", result_wr_ptr, result_rd_ptr, result_used_entries);
        test_data.push_back(16'h253e);  // Expected: 0x253e at position 0
        #500;  // Wait for drain
        $display("  After:  wr_ptr=%0d, rd_ptr=%0d, used=%0d", result_wr_ptr, result_rd_ptr, result_used_entries);
        $display("  BRAM[0][15:0] = 0x%04x (expected 0x253e)", result_bram_model[0][15:0]);
        
        #100;
        
        $display("\n[TEST 2] Starting B2_C2_V2 (expect 4 results) WITHOUT RESET");
        $display("  Before: wr_ptr=%0d, rd_ptr=%0d, used=%0d", result_wr_ptr, result_rd_ptr, result_used_entries);
        test_data.push_back(16'h22f7);  // Expected: 0x22f7 at position 1
        test_data.push_back(16'h25b7);  // Expected: 0x25b7 at position 2
        test_data.push_back(16'ha390);  // Expected: 0xa390 at position 3
        test_data.push_back(16'ha40a);  // Expected: 0xa40a at position 4
        #1000;
        $display("  After:  wr_ptr=%0d, rd_ptr=%0d, used=%0d", result_wr_ptr, result_rd_ptr, result_used_entries);
        
        // Check results
        $display("\n=== RESULT VERIFICATION ===");
        $display("Position 0: 0x%04x (expected 0x253e) %s", result_bram_model[0][15:0], 
                 (result_bram_model[0][15:0] == 16'h253e) ? "PASS" : "FAIL");
        $display("Position 1: 0x%04x (expected 0x22f7) %s", result_bram_model[0][31:16],
                 (result_bram_model[0][31:16] == 16'h22f7) ? "PASS" : "FAIL");
        $display("Position 2: 0x%04x (expected 0x25b7) %s", result_bram_model[0][47:32],
                 (result_bram_model[0][47:32] == 16'h25b7) ? "PASS" : "FAIL");
        $display("Position 3: 0x%04x (expected 0xa390) %s", result_bram_model[0][63:48],
                 (result_bram_model[0][63:48] == 16'ha390) ? "PASS" : "FAIL");
        $display("Position 4: 0x%04x (expected 0xa40a) %s", result_bram_model[0][79:64],
                 (result_bram_model[0][79:64] == 16'ha40a) ? "PASS" : "FAIL");
        
        if (result_bram_model[0][31:16] == 16'h253e) begin
            $display("\n*** SHIFT BUG DETECTED! Position 1 has duplicate of position 0! ***");
        end
        
        #100;
        $finish;
    end
    
    // Watchdog
    initial begin
        #50000;
        $display("ERROR: Timeout!");
        $finish;
    end
    
endmodule
