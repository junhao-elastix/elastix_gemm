// ------------------------------------------------------------------
// GEMM Engine with GDDR6 BFM Testbench
// 
// Purpose: Full system simulation with real GDDR6 memory model
// Tests: FETCH, DISPATCH, MATMUL commands with actual data
// ------------------------------------------------------------------

`timescale 1ps/1ps

// NOTE: These includes are found via +incdir+ in Makefile:
// - gddr_dci_port_names.svh
// - gddr_model_names.svh  
// - nap_interfaces.svh

module tb_engine_gddr6;

    // ========================================================================
    // Clock and Reset
    // ========================================================================
    logic i_nap_clk = 1'b0;
    logic i_reg_clk = 1'b0;
    logic i_adm_clk = 1'b0;
    logic reset_n;
    logic chip_ready;

    // Clock periods
    localparam I_NAP_CLK_PERIOD = 2000;   // 500MHz
    localparam I_REG_CLK_PERIOD = 5000;   // 200MHz
    localparam I_ADM_CLK_PERIOD = 10000;  // 100MHz
    
    // GDDR6 config - using 12Gbps for simulation speed
    localparam GDDR_DATA_RATE = 12;
    localparam GDDR_CONTROLLER_NOC_CLOCK_PERIOD = 1344; // 744MHz

    always #(I_NAP_CLK_PERIOD/2) i_nap_clk <= ~i_nap_clk;
    always #(I_REG_CLK_PERIOD/2) i_reg_clk <= ~i_reg_clk;
    always #(I_ADM_CLK_PERIOD/2) i_adm_clk <= ~i_adm_clk;

    // ========================================================================
    // Test Control Signals
    // ========================================================================
    logic test_start;
    logic test_complete;
    logic test_passed;
    integer test_errors;
    
    // Test counters
    integer total_tests = 0;
    integer passed_tests = 0;
    integer failed_tests = 0;
    
    // Test result comparison variables
    integer expected_count;
    integer match_count;
    
    // Test configuration structure
    typedef struct {
        int B;
        int C;
        int V;
        string name;
    } test_config_t;
    
    // Test configurations (same as vector_system_test)
    test_config_t test_configs[] = '{
        '{B: 1, C: 1, V: 1,   name: "B1_C1_V1"},
        '{B: 2, C: 2, V: 2,   name: "B2_C2_V2"},
        '{B: 4, C: 4, V: 4,   name: "B4_C4_V4"},
        '{B: 2, C: 2, V: 64,  name: "B2_C2_V64"},
        '{B: 4, C: 4, V: 32,  name: "B4_C4_V32"},
        '{B: 8, C: 8, V: 16,  name: "B8_C8_V16"},
        '{B: 1, C: 128, V: 1, name: "B1_C128_V1"},
        '{B: 128, C: 1, V: 1, name: "B128_C1_V1"},
        '{B: 1, C: 1, V: 128, name: "B1_C1_V128"}
    };
    
    // Golden reference storage
    logic [15:0] golden_results [0:16383];
    integer golden_count;
    integer golden_file;
    string golden_filename;

    // ========================================================================
    // Register Interface (emulating software)
    // ========================================================================
    logic [31:0] user_regs_write [0:132];
    logic [31:0] user_regs_read [0:132];
    logic [132:0] write_strobes;

    // Register addresses (from elastix_gemm_top.sv)
    localparam ENGINE_CMD_WORD0  = 15;  // 0x3C
    localparam ENGINE_CMD_WORD1  = 16;  // 0x40
    localparam ENGINE_CMD_WORD2  = 17;  // 0x44
    localparam ENGINE_CMD_WORD3  = 18;  // 0x48
    localparam ENGINE_CMD_SUBMIT = 19;  // 0x4C
    localparam ENGINE_STATUS     = 20;  // 0x50
    localparam ENGINE_RESULT_COUNT = 21; // 0x54

    // Import command package for structure definitions
    import gemm_pkg::*;

    // Initialize register interface
    initial begin
        for (int i = 0; i < 133; i++) begin
            user_regs_write[i] = 32'h0;
        end
        write_strobes = '0;
    end

    // ========================================================================
    // NAP AXI Interface for Channel 1
    // ========================================================================
    t_AXI4 #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LEN_WIDTH(8),
        .ID_WIDTH(8)
    ) nap();

    // ========================================================================
    // DUT: elastix_gemm_top (Channel 1 only, simplified)
    // ========================================================================
    // NAP interface connects directly to memory model (no responder wrapper needed)

    // Engine signals
    logic        engine_busy;
    logic [3:0]  mc_state, dc_state, ce_state;
    logic [31:0] engine_result_count;
    logic [12:0] cmd_fifo_count;

    // Simplified engine_top instantiation
    // We'll directly instantiate the key modules
    logic [31:0] cmd_fifo_wdata;
    logic        cmd_fifo_wen;
    logic        cmd_fifo_full, cmd_fifo_afull;
    logic        bridge_busy;

    // CSR to FIFO bridge
    csr_to_fifo_bridge i_csr_bridge (
        .i_clk(i_nap_clk),
        .i_reset_n(reset_n),
        .i_cmd_word0(user_regs_write[ENGINE_CMD_WORD0]),
        .i_cmd_word1(user_regs_write[ENGINE_CMD_WORD1]),
        .i_cmd_word2(user_regs_write[ENGINE_CMD_WORD2]),
        .i_cmd_word3(user_regs_write[ENGINE_CMD_WORD3]),
        .i_cmd_submit(write_strobes[ENGINE_CMD_SUBMIT]),
        .o_bridge_busy(bridge_busy),
        .o_fifo_wdata(cmd_fifo_wdata),
        .o_fifo_wen(cmd_fifo_wen),
        .i_fifo_full(cmd_fifo_full),
        .i_fifo_afull(cmd_fifo_afull)
    );

    // Result FIFO interface
    logic [15:0] result_fifo_rdata;
    logic        result_fifo_ren;
    logic        result_fifo_empty;
    logic [14:0] result_fifo_count;
    logic [15:0] result_count_16bit;
    logic [3:0]  last_opcode;
    logic [3:0]  mc_state_next;
    logic [9:0]  bram_wr_count;

    // Engine top
    engine_top #(
        .GDDR6_PAGE_ID(9'd2),
        .TGT_DATA_WIDTH(256),
        .AXI_ADDR_WIDTH(42)
    ) i_engine_top (
        .i_clk(i_nap_clk),
        .i_reset_n(reset_n),
        // Command FIFO
        .i_cmd_fifo_wdata(cmd_fifo_wdata),
        .i_cmd_fifo_wen(cmd_fifo_wen),
        .o_cmd_fifo_full(cmd_fifo_full),
        .o_cmd_fifo_afull(cmd_fifo_afull),
        .o_cmd_fifo_count(cmd_fifo_count),
        // Result FIFO
        .o_result_fifo_rdata(result_fifo_rdata),
        .i_result_fifo_ren(result_fifo_ren),
        .o_result_fifo_empty(result_fifo_empty),
        .o_result_fifo_count(result_fifo_count),
        // NAP AXI
        .nap_axi(nap.initiator),
        // Status
        .o_engine_busy(engine_busy),
        .o_mc_state(mc_state),
        .o_mc_state_next(mc_state_next),
        .o_dc_state(dc_state),
        .o_ce_state(ce_state),
        .o_last_opcode(last_opcode),
        // Debug
        .o_bram_wr_count(bram_wr_count),
        .o_result_count(result_count_16bit)
    );

    assign user_regs_read[ENGINE_STATUS] = {12'h0, mc_state_next, mc_state, dc_state, ce_state, 3'b0, engine_busy};
    assign user_regs_read[ENGINE_RESULT_COUNT] = {16'h0, result_count_16bit};

    // Result FIFO to BRAM Adapter (matches hardware)
    logic [15:0] result_0, result_1, result_2, result_3;
    logic [8:0]  result_bram_wr_addr;
    logic [255:0] result_bram_wr_data;
    logic result_bram_wr_en;
    
    // Simple adapter: one FP16 result per BRAM line (easier for simulation and host readback)
    result_fifo_to_simple_bram i_result_adapter (
        .i_clk(i_nap_clk),
        .i_reset_n(reset_n),
        .i_fifo_rdata(result_fifo_rdata),
        .o_fifo_ren(result_fifo_ren),
        .i_fifo_empty(result_fifo_empty),
        .o_bram_wr_addr(result_bram_wr_addr),
        .o_bram_wr_data(result_bram_wr_data),
        .o_bram_wr_en(result_bram_wr_en),
        .o_result_0(result_0),
        .o_result_1(result_1),
        .o_result_2(result_2),
        .o_result_3(result_3)
    );
    
    // Monitor result register captures (matches hardware register reads)
    logic [15:0] results_hw [0:16383];
    integer result_idx = 0;
    integer mismatches = 0;
    logic [15:0] prev_result_0 = 16'h0;
    logic [15:0] prev_result_1 = 16'h0;
    logic [15:0] prev_result_2 = 16'h0;
    logic [15:0] prev_result_3 = 16'h0;
    
    always_ff @(posedge i_nap_clk) begin
        if (!reset_n) begin
            result_idx <= 0;
            mismatches <= 0;
            prev_result_0 <= 16'h0;
            prev_result_1 <= 16'h0;
            prev_result_2 <= 16'h0;
            prev_result_3 <= 16'h0;
            for (int i = 0; i < 16384; i++) results_hw[i] <= 16'h0;
        end else if (result_bram_wr_en) begin
            // Path 1: Capture from BRAM write (ONE FP16 result per 256-bit line, zero-padded)
            logic [15:0] hw_result;
            hw_result = result_bram_wr_data[15:0];  // Result is in LSB 16 bits
            results_hw[result_idx] = hw_result;
            
            // Compare with golden reference if loaded
            if (result_idx < golden_count) begin
                // Calculate absolute difference (matching vector_system_test tolerance)
                automatic int diff;
                diff = (hw_result > golden_results[result_idx]) ? 
                       (hw_result - golden_results[result_idx]) : 
                       (golden_results[result_idx] - hw_result);
                       
                if (diff > 2) begin  // Allow 2 LSB tolerance for FP16 rounding
                    $display("[TB] @%0t MISMATCH Result[%0d]: hw=0x%04x golden=0x%04x diff=%0d",
                             $time, result_idx, hw_result, golden_results[result_idx], diff);
                    mismatches <= mismatches + 1;
                end else begin
                    $display("[TB] @%0t MATCH Result[%0d]: 0x%04x", 
                             $time, result_idx, hw_result);
                end
            end else begin
                $display("[TB] @%0t Result[%0d]: 0x%04x (no golden)", 
                         $time, result_idx, hw_result);
            end
            result_idx <= result_idx + 1;  // One result per BRAM write
        end else begin
            // Path 2: Monitor register outputs for small result sets (< 16 results)
            // These are the first 4 results exposed to registers by result_fifo_to_bram
            if (result_0 !== prev_result_0 && result_0 !== 16'h0000) begin
                results_hw[0] = result_0;
                if (0 < golden_count) begin
                    automatic int diff0;
                    diff0 = (result_0 > golden_results[0]) ? 
                            (result_0 - golden_results[0]) : 
                            (golden_results[0] - result_0);
                    if (diff0 > 2) begin
                        $display("[TB] @%0t MISMATCH Result[0]: hw=0x%04x golden=0x%04x diff=%0d",
                                 $time, result_0, golden_results[0], diff0);
                        mismatches <= mismatches + 1;
                    end else begin
                        $display("[TB] @%0t MATCH Result[0]: 0x%04x", $time, result_0);
                    end
                end
                prev_result_0 <= result_0;
                if (result_idx < 1) result_idx <= 1;
            end
            
            if (result_1 !== prev_result_1 && result_1 !== 16'h0000) begin
                results_hw[1] = result_1;
                if (1 < golden_count) begin
                    automatic int diff1;
                    diff1 = (result_1 > golden_results[1]) ? 
                            (result_1 - golden_results[1]) : 
                            (golden_results[1] - result_1);
                    if (diff1 > 2) begin
                        $display("[TB] @%0t MISMATCH Result[1]: hw=0x%04x golden=0x%04x diff=%0d",
                                 $time, result_1, golden_results[1], diff1);
                        mismatches <= mismatches + 1;
                    end else begin
                        $display("[TB] @%0t MATCH Result[1]: 0x%04x", $time, result_1);
                    end
                end
                prev_result_1 <= result_1;
                if (result_idx < 2) result_idx <= 2;
            end
            
            if (result_2 !== prev_result_2 && result_2 !== 16'h0000) begin
                results_hw[2] = result_2;
                if (2 < golden_count) begin
                    automatic int diff2;
                    diff2 = (result_2 > golden_results[2]) ? 
                            (result_2 - golden_results[2]) : 
                            (golden_results[2] - result_2);
                    if (diff2 > 2) begin
                        $display("[TB] @%0t MISMATCH Result[2]: hw=0x%04x golden=0x%04x diff=%0d",
                                 $time, result_2, golden_results[2], diff2);
                        mismatches <= mismatches + 1;
                    end else begin
                        $display("[TB] @%0t MATCH Result[2]: 0x%04x", $time, result_2);
                    end
                end
                prev_result_2 <= result_2;
                if (result_idx < 3) result_idx <= 3;
            end
            
            if (result_3 !== prev_result_3 && result_3 !== 16'h0000) begin
                results_hw[3] = result_3;
                if (3 < golden_count) begin
                    automatic int diff3;
                    diff3 = (result_3 > golden_results[3]) ? 
                            (result_3 - golden_results[3]) : 
                            (golden_results[3] - result_3);
                    if (diff3 > 2) begin
                        $display("[TB] @%0t MISMATCH Result[3]: hw=0x%04x golden=0x%04x diff=%0d",
                                 $time, result_3, golden_results[3], diff3);
                        mismatches <= mismatches + 1;
                    end else begin
                        $display("[TB] @%0t MATCH Result[3]: 0x%04x", $time, result_3);
                    end
                end
                prev_result_3 <= result_3;
                if (result_idx < 4) result_idx <= 4;
            end
        end
    end
    
    // Monitor adapter FIFO interface
    logic prev_fifo_ren = 1'b0;
    logic [15:0] prev_result_0_mon = 16'h0;
    logic [15:0] prev_result_1_mon = 16'h0;
    logic [15:0] prev_result_2_mon = 16'h0;
    logic [15:0] prev_result_3_mon = 16'h0;
    
    always @(posedge i_nap_clk) begin
        prev_fifo_ren <= result_fifo_ren;
        
        if (result_fifo_ren && !prev_fifo_ren) begin
            $display("[ADAPTER] @%0t FIFO read issued", $time);
        end
        
        if (prev_fifo_ren && !result_fifo_empty) begin
            $display("[ADAPTER] @%0t FIFO data available: 0x%04x (will capture next cycle)", 
                     $time, result_fifo_rdata);
        end
        
        // Monitor register updates
        if (result_0 !== 16'h0 && prev_result_0_mon !== result_0) begin
            $display("[ADAPTER] @%0t result_0 updated: 0x%04x", $time, result_0);
        end
        if (result_1 !== 16'h0 && prev_result_1_mon !== result_1) begin
            $display("[ADAPTER] @%0t result_1 updated: 0x%04x", $time, result_1);
        end
        if (result_2 !== 16'h0 && prev_result_2_mon !== result_2) begin
            $display("[ADAPTER] @%0t result_2 updated: 0x%04x", $time, result_2);
        end
        if (result_3 !== 16'h0 && prev_result_3_mon !== result_3) begin
            $display("[ADAPTER] @%0t result_3 updated: 0x%04x", $time, result_3);
        end
        
        // Update history
        prev_result_0_mon <= result_0;
        prev_result_1_mon <= result_1;
        prev_result_2_mon <= result_2;
        prev_result_3_mon <= result_3;
    end
    
    // Periodic monitor of register outputs (less verbose)
    integer monitor_counter = 0;
    always @(posedge i_nap_clk) begin
        monitor_counter <= monitor_counter + 1;
        if (monitor_counter % 1000 == 0) begin
            if (result_0 !== 16'h0 || result_1 !== 16'h0 || result_2 !== 16'h0 || result_3 !== 16'h0) begin
                $display("[TB] @%0t Register Snapshot: [0]=0x%04x [1]=0x%04x [2]=0x%04x [3]=0x%04x", 
                         $time, result_0, result_1, result_2, result_3);
            end
        end
    end

    // ========================================================================
    // Behavioral Memory Model (Simplified for testing)
    // ========================================================================
    // Using behavioral memory instead of full GDDR6 BFM for faster simulation
    
    logic [31:0] mem_read_count, mem_last_addr;
    
    tb_memory_model #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LINES_PER_BLOCK(528),
        .NUM_BLOCKS(2),
        .READ_LATENCY_NS(20)
    ) u_memory_model (
        .i_clk(i_nap_clk),
        .i_reset_n(reset_n),
        .axi_mem_if(nap),
        .o_read_count(mem_read_count),
        .o_last_addr(mem_last_addr)
    );

    // ========================================================================
    // GDDR6 Preload Task
    // ========================================================================
    task preload_gddr6();
        $display("\n[TB] Memory model preloads data automatically from hex files");
        $display("[TB]   left.hex  -> Block 0 (lines 0-527)");
        $display("[TB]   right.hex -> Block 1 (lines 528-1055)");
        $display("[TB] Memory preload complete\n");
        // Memory model loads data in its initial block
        // Note: The tb_memory_model automatically loads from /home/workstation/elastix_gemm/hex/left.hex and right.hex
        // This provides consistent test data for all configurations
    endtask

    // ========================================================================
    // CSR Write Tasks (emulating software)
    // ========================================================================
    task write_csr(input integer addr, input logic [31:0] data);
        @(posedge i_nap_clk);
        user_regs_write[addr] <= data;
        write_strobes[addr] <= 1'b1;
        @(posedge i_nap_clk);
        write_strobes[addr] <= 1'b0;
        @(posedge i_nap_clk);
    endtask

    task issue_command(input logic [31:0] w0, w1, w2, w3);
        $display("[TB] @%0t Issuing command: w0=0x%08x w1=0x%08x w2=0x%08x w3=0x%08x", 
                 $time, w0, w1, w2, w3);
        write_csr(ENGINE_CMD_WORD0, w0);
        write_csr(ENGINE_CMD_WORD1, w1);
        write_csr(ENGINE_CMD_WORD2, w2);
        write_csr(ENGINE_CMD_WORD3, w3);
        write_csr(ENGINE_CMD_SUBMIT, 32'h1);
    endtask

    task wait_engine_idle(input integer timeout_cycles);
        integer cycle_count;
        cycle_count = 0;
        while (engine_busy && cycle_count < timeout_cycles) begin
            @(posedge i_nap_clk);
            cycle_count++;
        end
        if (cycle_count >= timeout_cycles) begin
            $error("[TB] Timeout waiting for engine idle");
            test_errors++;
        end else begin
            $display("[TB] @%0t Engine idle after %0d cycles", $time, cycle_count);
        end
    endtask

    // ========================================================================
    // Golden Reference Loading
    // ========================================================================
    task load_golden_reference();
        // This is a legacy function - use load_golden_reference_for_test() instead
        $display("[TB] WARNING: load_golden_reference() is deprecated, use load_golden_reference_for_test()");
        // Set default golden values
        golden_results[0] = 16'h0000;
        golden_results[1] = 16'h0000;
        golden_results[2] = 16'h0000;
        golden_results[3] = 16'h0000;
        golden_count = 4;
    endtask

    // ========================================================================
    // Command Generation Tasks (from working testbench)
    // ========================================================================
    task automatic generate_fetch_command(
        input logic [7:0] id,
        input logic [link_addr_width_gp-1:0] start_addr,
        input logic [link_len_width_gp-1:0] num_lines,
        input logic fetch_right,  // 0=left, 1=right
        output logic [31:0] cmd [0:3]
    );
        cmd_fetch_s payload;
        
        // Pack using structure for correct bit alignment
        payload.start_addr = start_addr;
        payload.len = num_lines;
        payload.fetch_right = fetch_right;
        payload.reserved = '0;
        
        // All commands are 4 words: header + 3 payload words
        cmd[0] = {16'd12, id, e_cmd_op_fetch};
        cmd[1] = payload[31:0];    // start_addr
        cmd[2] = payload[63:32];   // len in upper 16 bits, fetch_right bit
        cmd[3] = 32'h00000000;     // Unused payload word 3
    endtask

    task automatic generate_disp_command(
        input logic [7:0] id,
        input logic [tile_mem_addr_width_gp-1:0] disp_addr,
        input logic [tile_mem_addr_width_gp-1:0] disp_len,
        input logic man_4b,
        output logic [31:0] cmd [0:3]
    );
        cmd[0] = {16'd8, id, e_cmd_op_disp};
        cmd[1] = {man_4b, 10'b0, disp_len, disp_addr};
        cmd[2] = 32'h00000000;
        cmd[3] = 32'h00000000;
    endtask

    task automatic generate_wait_disp_command(
        input logic [7:0] id,
        input logic [7:0] wait_id,
        output logic [31:0] cmd [0:3]
    );
        cmd[0] = {wait_id, 8'd0, id, e_cmd_op_wait_disp};
        cmd[1] = 32'h00000000;
        cmd[2] = 32'h00000000;
        cmd[3] = 32'h00000000;
    endtask

    task automatic generate_tile_command(
        input logic [7:0] id,
        input logic [tile_mem_addr_width_gp-1:0] left_addr,
        input logic [tile_mem_addr_width_gp-1:0] right_addr,
        input int dim_b,
        input int dim_c,
        input int dim_v,
        output logic [31:0] cmd [0:3]
    );
        cmd_header_s header;
        cmd_tile_s payload;
        
        // Pack header
        header.op       = e_cmd_op_tile;
        header.id       = id;
        header.len      = cmd_tile_len_gp;
        header.reserved = 8'h00;
        
        // Pack payload using structure (automatic bit width handling)
        payload.left_addr      = left_addr;
        payload.right_addr     = right_addr;
        payload.left_ugd_len   = 11'd1;      // Default: 1 unified group dot
        payload.right_ugd_len  = 11'd1;
        payload.vec_len        = dim_v[10:0];
        payload.dim_b          = dim_b[7:0];
        payload.dim_c          = dim_c[7:0];
        payload.dim_v          = dim_v[7:0];
        payload.flags.left_man_4b        = 1'b0;
        payload.flags.right_man_4b       = 1'b0;
        payload.flags.main_loop_over_left = 1'b0;
        payload.flags.reserved            = '0;
        
        // Output words (87 bits needs 3 words, padded to 96 bits)
        cmd[0] = header;
        cmd[1] = payload[31:0];              // Bits [31:0]
        cmd[2] = payload[63:32];             // Bits [63:32]
        cmd[3] = {9'b0, payload[86:64]};     // Bits [86:64], zero-padded
    endtask

    task automatic generate_wait_tile_command(
        input logic [7:0] id,
        input logic [7:0] wait_id,
        output logic [31:0] cmd [0:3]
    );
        cmd[0] = {wait_id, 8'd0, id, e_cmd_op_wait_tile};
        cmd[1] = 32'h00000000;
        cmd[2] = 32'h00000000;
        cmd[3] = 32'h00000000;
    endtask

    // ========================================================================
    // Task: Run Single Test
    // ========================================================================
    task automatic run_single_test(
        input int config_B,
        input int config_C,
        input int config_V,
        input string test_name
    );
        integer local_mismatches = 0;
        integer local_test_errors = 0;
        integer local_result_idx = 0;
        
        total_tests++;
        
        $display("\n[TB] ====================================================================");
        $display("[TB] TEST %0d: Running configuration %s (B=%0d, C=%0d, V=%0d)",
                 total_tests, test_name, config_B, config_C, config_V);
        $display("[TB] ====================================================================");

        // Load golden reference for this test
        load_golden_reference_for_test(test_name);

        // Preload GDDR6
        preload_gddr6();

        // Reset test signals
        test_start = 1'b0;
        test_complete = 1'b0;
        test_passed = 1'b0;
        local_mismatches = 0;
        local_test_errors = 0;
        local_result_idx = 0;

        // Start test
        test_start = 1'b1;
        run_test_sequence_for_config(config_B, config_C, config_V);

        // Test complete
        test_complete = 1'b1;
        repeat(100000) @(posedge i_nap_clk);  // Wait for completion
        
        // Sample final register outputs
        $display("\n[TB] Final Register Outputs for %s:", test_name);
        $display("[TB]   result_0 = 0x%04x (expected 0x%04x)", result_0, golden_results[0]);
        $display("[TB]   result_1 = 0x%04x (expected 0x%04x)", result_1, golden_results[1]);
        $display("[TB]   result_2 = 0x%04x (expected 0x%04x)", result_2, golden_results[2]);
        $display("[TB]   result_3 = 0x%04x (expected 0x%04x)", result_3, golden_results[3]);
        
        // Final comparison (allowing 1 LSB tolerance for FP16 rounding)
        // Only check the expected number of results (config_B * config_C)
        expected_count = config_B * config_C;
        match_count = 0;
        
        if (expected_count >= 1 && (result_0 == golden_results[0] || result_0 == (golden_results[0] + 1) || result_0 == (golden_results[0] - 1))) match_count++;
        if (expected_count >= 2 && (result_1 == golden_results[1] || result_1 == (golden_results[1] + 1) || result_1 == (golden_results[1] - 1))) match_count++;
        if (expected_count >= 3 && (result_2 == golden_results[2] || result_2 == (golden_results[2] + 1) || result_2 == (golden_results[2] - 1))) match_count++;
        if (expected_count >= 4 && (result_3 == golden_results[3] || result_3 == (golden_results[3] + 1) || result_3 == (golden_results[3] - 1))) match_count++;
        
        if (match_count == expected_count) begin
            $display("[TB] PASS: %s - All %0d results matched within tolerance!", test_name, expected_count);
            passed_tests++;
        end else begin
            $display("[TB] FAIL: %s - %0d/%0d results matched golden reference", test_name, match_count, expected_count);
            failed_tests++;
        end
        
        repeat(100) @(posedge i_nap_clk);  // Delay between tests
        
    endtask

    // ========================================================================
    // Task: Load Golden Reference for Specific Test
    // ========================================================================
    task automatic load_golden_reference_for_test(input string test_name);
        string golden_filename;
        integer scan_result;
        integer idx;
        
        golden_filename = $sformatf("/home/workstation/elastix_gemm/hex/golden_%s.hex", test_name);
        golden_file = $fopen(golden_filename, "r");
        if (golden_file == 0) begin
            $display("[TB] ERROR: Cannot open golden reference file: %s", golden_filename);
            $display("[TB] Using default golden values for test %s", test_name);
            // Set default golden values
            golden_results[0] = 16'h0000;
            golden_results[1] = 16'h0000;
            golden_results[2] = 16'h0000;
            golden_results[3] = 16'h0000;
            golden_count = 4;
            return;
        end
        
        // Load golden results
        idx = 0;
        while (!$feof(golden_file) && idx < 16384) begin
            scan_result = $fscanf(golden_file, "%h\n", golden_results[idx]);
            if (scan_result == 1) idx++;
        end
        $fclose(golden_file);
        golden_count = idx;
        $display("[TB] Loaded %0d golden results from %s", idx, golden_filename);
    endtask

    // ========================================================================
    // Task: Run Test Sequence for Specific Configuration
    // ========================================================================
    task automatic run_test_sequence_for_config(
        input int config_B,
        input int config_C,
        input int config_V
    );
        logic [31:0] cmd [0:3];

        // Step 1: FETCH left matrix (start_addr=0, len=528, fetch_right=0)
        $display("[TB] Step 1: FETCH left matrix (528 lines from 0x0)");
        generate_fetch_command(0, 0, 528, 1'b0, cmd);
        $display("[TB]   cmd[0]=0x%08x cmd[1]=0x%08x cmd[2]=0x%08x cmd[3]=0x%08x",
                 cmd[0], cmd[1], cmd[2], cmd[3]);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(100000);

        // Step 2: FETCH right matrix (start_addr=528, len=528, fetch_right=1)
        $display("\n[TB] Step 2: FETCH right matrix (528 lines from 0x4200)");
        generate_fetch_command(1, 528, 528, 1'b1, cmd);
        $display("[TB]   cmd[0]=0x%08x cmd[1]=0x%08x cmd[2]=0x%08x cmd[3]=0x%08x",
                 cmd[0], cmd[1], cmd[2], cmd[3]);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(100000);

        // Step 3: DISPATCH left (addr=0, len=128)
        $display("\n[TB] Step 3: DISPATCH left (addr=0, len=128)");
        generate_disp_command(2, 0, 128, 1'b0, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        // Step 4: WAIT_DISPATCH left (id=2)
        $display("\n[TB] Step 4: WAIT_DISPATCH left (id=2)");
        generate_wait_disp_command(3, 2, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        // Step 5: DISPATCH right (addr=0, len=128) <- TWO-BRAM: right also starts at 0!
        $display("\n[TB] Step 5: DISPATCH right (addr=0, len=128) [TWO-BRAM architecture]");
        generate_disp_command(4, 0, 128, 1'b0, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        // Step 6: WAIT_DISPATCH right (id=4)
        $display("\n[TB] Step 6: WAIT_DISPATCH right (id=4)");
        generate_wait_disp_command(5, 4, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        // Step 7: TILE (matrix multiply) - TWO-BRAM: both left_addr=0, right_addr=0!
        $display("\n[TB] Step 7: TILE (B=%0d, C=%0d, V=%0d) [left_addr=0, right_addr=0]",
                 config_B, config_C, config_V);
        generate_tile_command(6, 0, 0, config_B, config_C, config_V, cmd);
        $display("[TB]   cmd[0]=0x%08x cmd[1]=0x%08x cmd[2]=0x%08x cmd[3]=0x%08x",
                 cmd[0], cmd[1], cmd[2], cmd[3]);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(50000);

        // Step 8: WAIT_TILE
        $display("\n[TB] Step 8: WAIT_TILE (id=6)");
        generate_wait_tile_command(7, 6, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        $display("\n[TB] Test sequence complete for B=%0d, C=%0d, V=%0d", config_B, config_C, config_V);
    endtask

    // ========================================================================
    // Test Sequence
    // ========================================================================
    initial begin
        reset_n = 1'b0;
        test_start = 1'b0;
        test_complete = 1'b0;
        test_passed = 1'b0;
        test_errors = 0;
        chip_ready = 1'b1;  // Simplified - assume chip ready

        $display("\n================================================================================");
        $display("TB: GEMM Engine GDDR6 Simulation Testbench - Multiple Test Configurations");
        $display("================================================================================\n");

        // Wait for clocks to stabilize
        repeat(10) @(posedge i_nap_clk);

        // Release reset
        reset_n = 1'b1;
        repeat(50) @(posedge i_nap_clk);

        $display("[TB] @%0t Reset released\n", $time);

        // Run all test configurations
        foreach (test_configs[i]) begin
            run_single_test(
                test_configs[i].B,
                test_configs[i].C,
                test_configs[i].V,
                test_configs[i].name
            );
        end

        // Print summary
        $display("\n================================================================================");
        $display("TEST SUMMARY");
        $display("================================================================================");
        $display("Total Tests: %0d", total_tests);
        $display("Passed:      %0d", passed_tests);
        $display("Failed:      %0d", failed_tests);
        if (failed_tests == 0) begin
            $display("STATUS: ALL TESTS PASSED");
        end else begin
            $display("STATUS: %0d TESTS FAILED", failed_tests);
        end
        $display("================================================================================");

        $finish;
    end

    // ========================================================================
    // Test Sequence Task (using structure-based command generation)
    // ========================================================================
    task run_test_sequence();
        logic [31:0] cmd [0:3];

        // Step 1: FETCH left matrix (start_addr=0, len=528, fetch_right=0)
        $display("[TB] Step 1: FETCH left matrix (528 lines from 0x0)");
        generate_fetch_command(0, 0, 528, 1'b0, cmd);
        $display("[TB]   cmd[0]=0x%08x cmd[1]=0x%08x cmd[2]=0x%08x cmd[3]=0x%08x",
                 cmd[0], cmd[1], cmd[2], cmd[3]);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(100000);

        // Step 2: FETCH right matrix (start_addr=528, len=528, fetch_right=1)
        $display("\n[TB] Step 2: FETCH right matrix (528 lines from 0x4200)");
        generate_fetch_command(1, 528, 528, 1'b1, cmd);
        $display("[TB]   cmd[0]=0x%08x cmd[1]=0x%08x cmd[2]=0x%08x cmd[3]=0x%08x",
                 cmd[0], cmd[1], cmd[2], cmd[3]);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(100000);

        // Step 3: DISPATCH left (addr=0, len=128)
        $display("\n[TB] Step 3: DISPATCH left (addr=0, len=128)");
        generate_disp_command(2, 0, 128, 1'b0, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        // Step 4: WAIT_DISPATCH left (id=2)
        $display("\n[TB] Step 4: WAIT_DISPATCH left (id=2)");
        generate_wait_disp_command(3, 2, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        // Step 5: DISPATCH right (addr=0, len=128) <- TWO-BRAM: right also starts at 0!
        $display("\n[TB] Step 5: DISPATCH right (addr=0, len=128) [TWO-BRAM architecture]");
        generate_disp_command(4, 0, 128, 1'b0, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        // Step 6: WAIT_DISPATCH right (id=4)
        $display("\n[TB] Step 6: WAIT_DISPATCH right (id=4)");
        generate_wait_disp_command(5, 4, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        // Step 7: TILE (matrix multiply) - TWO-BRAM: both left_addr=0, right_addr=0!
        $display("\n[TB] Step 7: TILE (B=2, C=1, V=32) [left_addr=0, right_addr=0]");
        generate_tile_command(6, 0, 0, 2, 1, 32, cmd);
        $display("[TB]   cmd[0]=0x%08x cmd[1]=0x%08x cmd[2]=0x%08x cmd[3]=0x%08x",
                 cmd[0], cmd[1], cmd[2], cmd[3]);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(50000);

        // Step 8: WAIT_TILE
        $display("\n[TB] Step 8: WAIT_TILE (id=6)");
        generate_wait_tile_command(7, 6, cmd);
        issue_command(cmd[0], cmd[1], cmd[2], cmd[3]);
        wait_engine_idle(10000);

        $display("\n[TB] Test sequence complete");
    endtask

    // ========================================================================
    // Timeout Watchdog
    // ========================================================================
    initial begin
        #(I_NAP_CLK_PERIOD * 1000000);  // 1M cycles
        $error("[TB] Simulation timeout");
        $finish;
    end

endmodule

