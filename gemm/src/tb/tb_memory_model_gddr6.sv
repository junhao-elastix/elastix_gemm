// ------------------------------------------------------------------
// GDDR6-Realistic Memory Model for GEMM Engine
//
// Purpose: Enhanced memory model with GDDR6-realistic timing characteristics
// Features:
//  - Based on tb_memory_model.sv but with realistic GDDR6 latencies
//  - Configurable read latency (70-100ns typical for GDDR6)
//  - Burst-aware timing with inter-burst gaps
//  - NoC routing delay emulation
//  - Maintains same AXI4 interface as original for drop-in replacement
//
// GDDR6 Timing Characteristics:
//  - tCL (CAS Latency): ~35-40 cycles @ 2GHz
//  - tRCD (Row to Column Delay): ~20-25ns
//  - tRP (Row Precharge): ~20-25ns
//  - NoC routing: ~10-20 cycles additional
//  - Total first-word latency: ~70-100ns (140-200 cycles @ 2GHz)
//  - Subsequent burst words: 1 cycle each (full bandwidth)
//
// Author: Enhanced for GDDR6-realistic simulation
// Date: Thu Oct 30 2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module tb_memory_model
#(
    parameter DATA_WIDTH = 256,        // 256-bit AXI data width
    parameter ADDR_WIDTH = 42,         // AXI address width
    parameter LINES_PER_BLOCK = 528,   // GFP8 block size
    parameter NUM_BLOCKS = 2,          // Left and right blocks

    // GDDR6-Realistic Timing Parameters (in cycles)
    parameter GDDR6_CAS_LATENCY = 40,      // ~20ns @ 2GHz GDDR6 clock
    parameter GDDR6_ROW_LATENCY = 50,      // tRCD + tRP overhead
    parameter NOC_ROUTING_LATENCY = 15,    // NoC fabric routing delay
    parameter INTER_BURST_GAP = 5,         // Gap between consecutive bursts

    // Derived total latency
    parameter FIRST_WORD_LATENCY = GDDR6_CAS_LATENCY + NOC_ROUTING_LATENCY,  // ~55 cycles
    parameter NEW_ROW_LATENCY = GDDR6_CAS_LATENCY + GDDR6_ROW_LATENCY + NOC_ROUTING_LATENCY  // ~105 cycles
)
(
    input  logic        i_clk,
    input  logic        i_reset_n,

    // AXI4 Slave Interface (same as original)
    t_AXI4.responder    axi_mem_if,

    // Debug outputs
    output logic [31:0] o_read_count,
    output logic [31:0] o_last_addr,
    output logic [31:0] o_total_latency_cycles,  // New: track cumulative latency
    output logic [31:0] o_total_burst_cycles     // New: track burst transfer cycles
);

    // ===================================================================
    // Memory Array (same as original)
    // ===================================================================
    logic [DATA_WIDTH-1:0] mem_array [0:NUM_BLOCKS*LINES_PER_BLOCK-1];

    // Enhanced AXI State Machine with realistic timing
    typedef enum logic [3:0] {
        AXI_IDLE            = 4'b0000,
        AXI_ARREADY_DELAY   = 4'b0001,  // NoC arbitration delay
        AXI_ROW_ACTIVATE    = 4'b0010,  // GDDR6 row activation
        AXI_CAS_LATENCY     = 4'b0011,  // Column access latency
        AXI_RDATA           = 4'b0100,  // Burst data transfer
        AXI_INTER_BURST     = 4'b0101   // Inter-burst gap
    } axi_state_t;

    axi_state_t axi_state_reg, axi_state_next;

    // Timing counters
    logic [7:0] latency_counter_reg;
    logic [7:0] target_latency_reg;

    // Row tracking for realistic row hit/miss behavior
    logic [15:0] current_row_reg;
    logic [15:0] last_accessed_row_reg;
    logic        row_hit;

    // ===================================================================
    // AXI Transaction Registers (same as original)
    // ===================================================================
    logic [ADDR_WIDTH-1:0] ar_addr_reg;
    logic [7:0]            ar_id_reg;
    logic [7:0]            ar_len_reg;
    logic [2:0]            ar_size_reg;
    logic [1:0]            ar_burst_reg;

    logic [7:0]            beat_count_reg;
    logic [DATA_WIDTH-1:0] read_data_reg;
    logic                  read_valid_reg;
    logic                  read_last_reg;

    // Debug counters
    logic [31:0] read_count_reg;
    logic [31:0] last_addr_reg;
    logic [31:0] total_latency_cycles_reg;
    logic [31:0] total_burst_cycles_reg;
    logic [31:0] burst_count_reg;

    // ===================================================================
    // Memory Initialization (same as original)
    // ===================================================================
    initial begin
        integer fd_left, fd_right;
        string line_str;
        integer line_idx, byte_idx;
        logic [7:0] byte_val;
        integer scan_result;

        $display("[TB_GDDR6_MODEL] ===============================================");
        $display("[TB_GDDR6_MODEL] ** GDDR6-REALISTIC TIMING MODE **");
        $display("[TB_GDDR6_MODEL] - First word latency: %0d cycles (~%0dns @ 400MHz)",
                 FIRST_WORD_LATENCY, FIRST_WORD_LATENCY * 2.5);
        $display("[TB_GDDR6_MODEL] - Row miss penalty: %0d cycles", NEW_ROW_LATENCY);
        $display("[TB_GDDR6_MODEL] - Inter-burst gap: %0d cycles", INTER_BURST_GAP);
        $display("[TB_GDDR6_MODEL] - This emulates realistic GDDR6+NoC behavior");
        $display("[TB_GDDR6_MODEL] ===============================================");

        // Initialize all memory to zero first
        for (int i = 0; i < NUM_BLOCKS*LINES_PER_BLOCK; i = i + 1) begin
            mem_array[i] = '0;
        end

        // Load Block 0: Left matrix from hex file
        fd_left = $fopen("/home/workstation/elastix_gemm/hex/left.hex", "r");
        if (fd_left == 0) begin
            $display("[TB_GDDR6_MODEL] ERROR: Could not open /home/workstation/elastix_gemm/hex/left.hex");
            $display("[TB_GDDR6_MODEL] Using zero-initialized memory for left matrix");
        end else begin
            line_idx = 0;
            while (!$feof(fd_left) && line_idx < LINES_PER_BLOCK) begin
                if ($fgets(line_str, fd_left)) begin
                    // Parse hex line: expects 32 hex bytes separated by spaces
                    automatic logic [7:0] hex_bytes[0:31];
                    scan_result = $sscanf(line_str,
                        "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                        hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                        hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                        hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                        hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                        hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                        hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                        hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                        hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);

                    if (scan_result == 32) begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx = byte_idx + 1) begin
                            mem_array[line_idx][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                    line_idx = line_idx + 1;
                end
            end
            $fclose(fd_left);
            $display("[TB_GDDR6_MODEL] Loaded %0d lines from left.hex (Block 0)", line_idx);
        end

        // Load Block 1: Right matrix from hex file
        // Right matrix starts at line offset 528 (LINES_PER_BLOCK)
        fd_right = $fopen("/home/workstation/elastix_gemm/hex/right.hex", "r");
        if (fd_right == 0) begin
            $display("[TB_GDDR6_MODEL] ERROR: Could not open /home/workstation/elastix_gemm/hex/right.hex");
            $display("[TB_GDDR6_MODEL] Using zero-initialized memory for right matrix");
        end else begin
            line_idx = 0;
            while (!$feof(fd_right) && line_idx < LINES_PER_BLOCK) begin
                if ($fgets(line_str, fd_right)) begin
                    // Parse hex line: expects 32 hex bytes separated by spaces
                    automatic logic [7:0] hex_bytes[0:31];
                    scan_result = $sscanf(line_str,
                        "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                        hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                        hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                        hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                        hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                        hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                        hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                        hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                        hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);

                    if (scan_result == 32) begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx = byte_idx + 1) begin
                            // Write to Block 1 starting at line 528
                            mem_array[LINES_PER_BLOCK + line_idx][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                    line_idx = line_idx + 1;
                end
            end
            $fclose(fd_right);
            $display("[TB_GDDR6_MODEL] Loaded %0d lines from right.hex (Block 1)", line_idx);
        end

        $display("[TB_GDDR6_MODEL] Memory initialization complete");
        $display("[TB_GDDR6_MODEL]   Total: %0d blocks x %0d lines = %0d lines",
                 NUM_BLOCKS, LINES_PER_BLOCK, NUM_BLOCKS*LINES_PER_BLOCK);
        $display("[TB_GDDR6_MODEL]   Block 0 (Left matrix):  Lines 0-%0d", LINES_PER_BLOCK-1);
        $display("[TB_GDDR6_MODEL]   Block 1 (Right matrix): Lines %0d-%0d", LINES_PER_BLOCK, 2*LINES_PER_BLOCK-1);

        // Display first few bytes for verification
        $display("[TB_GDDR6_MODEL] Left matrix first line[7:0]: 0x%02h %02h %02h %02h",
                 mem_array[0][7:0], mem_array[0][15:8], mem_array[0][23:16], mem_array[0][31:24]);
        $display("[TB_GDDR6_MODEL] Right matrix first line[7:0]: 0x%02h %02h %02h %02h",
                 mem_array[528][7:0], mem_array[528][15:8], mem_array[528][23:16], mem_array[528][31:24]);
    end

    // ===================================================================
    // Row Hit/Miss Detection
    // ===================================================================
    always_comb begin
        logic [15:0] new_row;
        new_row = ar_addr_reg[20:5];  // Assuming 32 lines per row (5 bits)
        row_hit = (new_row == last_accessed_row_reg) && (burst_count_reg > 0);
        current_row_reg = new_row;
    end

    // ===================================================================
    // State Machine - Sequential
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            axi_state_reg <= AXI_IDLE;
            latency_counter_reg <= '0;
            target_latency_reg <= '0;
            last_accessed_row_reg <= '1;  // Invalid row initially
            burst_count_reg <= '0;
        end else begin
            axi_state_reg <= axi_state_next;

            // Update latency counter
            if (axi_state_reg != AXI_IDLE && axi_state_reg != AXI_RDATA) begin
                latency_counter_reg <= latency_counter_reg + 1;
            end else begin
                latency_counter_reg <= '0;
            end

            // Update row tracking
            if (axi_state_reg == AXI_ROW_ACTIVATE) begin
                last_accessed_row_reg <= current_row_reg;
            end

            // Track burst count
            if (axi_state_reg == AXI_IDLE && axi_mem_if.arvalid) begin
                burst_count_reg <= burst_count_reg + 1;
            end
        end
    end

    // ===================================================================
    // State Machine - Combinational Next State
    // ===================================================================
    always_comb begin
        axi_state_next = axi_state_reg;

        case (axi_state_reg)
            AXI_IDLE: begin
                if (axi_mem_if.arvalid && axi_mem_if.arready) begin
                    // Transition directly to ROW_ACTIVATE after accepting AR
                    axi_state_next = AXI_ROW_ACTIVATE;
                end
            end

            AXI_ROW_ACTIVATE: begin
                // Row activation time (skip if row hit)
                if (row_hit) begin
                    axi_state_next = AXI_CAS_LATENCY;
                end else if (latency_counter_reg >= GDDR6_ROW_LATENCY) begin
                    axi_state_next = AXI_CAS_LATENCY;
                end
            end

            AXI_CAS_LATENCY: begin
                // Column access latency
                if (latency_counter_reg >= GDDR6_CAS_LATENCY + NOC_ROUTING_LATENCY) begin
                    axi_state_next = AXI_RDATA;
                end
            end

            AXI_RDATA: begin
                // Data transfer - continuous for burst
                if (axi_mem_if.rvalid && axi_mem_if.rready) begin
                    if (axi_mem_if.rlast) begin
                        // Add inter-burst gap
                        axi_state_next = AXI_INTER_BURST;
                    end
                end
            end

            AXI_INTER_BURST: begin
                // Inter-burst gap before accepting next transaction
                if (latency_counter_reg >= INTER_BURST_GAP) begin
                    axi_state_next = AXI_IDLE;
                end
            end

            default: begin
                axi_state_next = AXI_IDLE;
            end
        endcase
    end

    // ===================================================================
    // AXI Read Address Channel
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_addr_reg <= '0;
            ar_id_reg <= '0;
            ar_len_reg <= '0;
            ar_size_reg <= '0;
            ar_burst_reg <= '0;
        end else begin
            if (axi_mem_if.arvalid && axi_mem_if.arready) begin
                ar_addr_reg <= axi_mem_if.araddr[ADDR_WIDTH-1:0];
                ar_id_reg <= axi_mem_if.arid;
                ar_len_reg <= axi_mem_if.arlen;
                ar_size_reg <= axi_mem_if.arsize;
                ar_burst_reg <= axi_mem_if.arburst;
            end
        end
    end

    // ARREADY: Accept immediately when in IDLE (no initial delay needed for memory model)
    assign axi_mem_if.arready = (axi_state_reg == AXI_IDLE);

    // ===================================================================
    // AXI Read Data Channel
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            beat_count_reg <= '0;
            read_data_reg <= '0;
            read_valid_reg <= 1'b0;
            read_last_reg <= 1'b0;
            read_count_reg <= '0;
            last_addr_reg <= '0;
            total_latency_cycles_reg <= '0;
            total_burst_cycles_reg <= '0;
        end else begin
            read_valid_reg <= 1'b0;
            read_last_reg <= 1'b0;

            case (axi_state_reg)
                AXI_IDLE: begin
                    // Reset beat counter when AR handshake completes
                    if (axi_mem_if.arvalid && axi_mem_if.arready) begin
                        beat_count_reg <= '0;
                    end
                end

                AXI_ROW_ACTIVATE: begin
                    // No special handling needed - just waiting for latency
                end

                AXI_CAS_LATENCY: begin
                    // Track latency overhead
                    total_latency_cycles_reg <= total_latency_cycles_reg + 1;
                end

                AXI_RDATA: begin
                    if (!read_valid_reg || (read_valid_reg && axi_mem_if.rready)) begin
                        // Calculate memory address
                        logic [ADDR_WIDTH-1:0] byte_addr;
                        logic [25:0] line_addr_26bit;
                        logic [15:0] line_addr_16bit;

                        byte_addr = ar_addr_reg + (beat_count_reg << ar_size_reg);
                        line_addr_26bit = byte_addr[30:5];
                        line_addr_16bit = line_addr_26bit[15:0];

                        // Read from memory
                        if (line_addr_16bit < NUM_BLOCKS*LINES_PER_BLOCK) begin
                            read_data_reg <= mem_array[line_addr_16bit];
                        end else begin
                            read_data_reg <= {DATA_WIDTH{1'b0}};
                        end

                        read_valid_reg <= 1'b1;
                        read_last_reg <= (beat_count_reg == ar_len_reg);

                        // Update counters
                        beat_count_reg <= beat_count_reg + 1;
                        read_count_reg <= read_count_reg + 1;
                        last_addr_reg <= line_addr_16bit;
                        total_burst_cycles_reg <= total_burst_cycles_reg + 1;

                        // Debug output for key addresses
                        if (beat_count_reg == 0) begin
                            $display("[TB_GDDR6] @%0t Burst start after %0d cycle latency, addr=%0d",
                                    $time, latency_counter_reg, line_addr_16bit);
                        end
                    end
                end
            endcase
        end
    end

    // AXI Read Data outputs
    assign axi_mem_if.rdata = read_data_reg;
    assign axi_mem_if.rvalid = read_valid_reg;
    assign axi_mem_if.rlast = read_last_reg;
    assign axi_mem_if.rid = ar_id_reg;
    assign axi_mem_if.rresp = 2'b00;  // OKAY

    // AXI Write channels (not implemented - read-only memory)
    assign axi_mem_if.awready = 1'b0;
    assign axi_mem_if.wready = 1'b0;
    assign axi_mem_if.bvalid = 1'b0;
    assign axi_mem_if.bid = '0;
    assign axi_mem_if.bresp = 2'b00;

    // Debug outputs
    assign o_read_count = read_count_reg;
    assign o_last_addr = last_addr_reg;
    assign o_total_latency_cycles = total_latency_cycles_reg;
    assign o_total_burst_cycles = total_burst_cycles_reg;

    // Performance reporting
    final begin
        if (burst_count_reg > 0) begin
            $display("[TB_GDDR6_MODEL] ===============================================");
            $display("[TB_GDDR6_MODEL] Performance Summary:");
            $display("[TB_GDDR6_MODEL]   Total bursts: %0d", burst_count_reg);
            $display("[TB_GDDR6_MODEL]   Total latency cycles: %0d", total_latency_cycles_reg);
            $display("[TB_GDDR6_MODEL]   Total burst cycles: %0d", total_burst_cycles_reg);
            $display("[TB_GDDR6_MODEL]   Average latency per burst: %0d cycles",
                     total_latency_cycles_reg / burst_count_reg);
            $display("[TB_GDDR6_MODEL]   Efficiency: %0d%%",
                     (total_burst_cycles_reg * 100) / (total_latency_cycles_reg + total_burst_cycles_reg));
            $display("[TB_GDDR6_MODEL] ===============================================");
        end
    end

endmodule : tb_memory_model