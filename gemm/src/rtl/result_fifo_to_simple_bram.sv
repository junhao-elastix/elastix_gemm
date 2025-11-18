// =============================================================================
// result_fifo_to_simple_bram.sv - Line-Copy Bridge (No Packing)
// =============================================================================
// Line-copy bridge: Result Arbiter (256-bit packed lines) -> Outgoing BRAM
//
// Description:
//   - Receives 256-bit packed lines from result_arbiter
//   - Copies lines to outgoing BRAM on READOUT command
//   - Implements circular buffer with 13-bit rd_ptr/wr_ptr (8192 FP16 capacity)
//   - Provides backpressure when buffer nearly full
//
// Key Changes from Previous Version:
//   - Changed from 16-bit PUSH interface to 256-bit LINE interface
//   - No longer packs FP16 results (arbiter does that now)
//   - READOUT command triggers line copying from arbiter to outgoing BRAM
//   - Simple bridge operation for future extension purposes
//
// Architecture:
//   - Line interface: 256-bit data + address + valid from arbiter
//   - READOUT command: Triggers copying lines to outgoing BRAM
//   - Circular buffer wraps at 8192 FP16 (512 lines)
//   - Four result registers capture first 4 FP16 for quick host access
//
// Author: Junhao Pan
// Date: Nov 17, 2025 - Converted to line-copy bridge
// =============================================================================

module result_fifo_to_simple_bram (
    input  logic        i_clk,
    input  logic        i_reset_n,

    // READOUT Command Interface (from master_control)
    input  logic        i_readout_en,        // READOUT command trigger
    output logic        o_readout_done,      // READOUT completion signal

    // Line interface (from result_arbiter)
    input  logic [255:0] i_line_data,        // Packed 256-bit line (16 FP16)
    input  logic [8:0]   i_line_addr,        // Line address (0-511)
    input  logic         i_line_valid,       // Line write strobe
    input  logic         i_collection_done,  // Arbiter collection completion signal

    // BRAM interface (256-bit per line, byte-granular writes)
    output logic [8:0]   o_bram_wr_addr,     // Line address (0-511)
    output logic [255:0] o_bram_wr_data,     // 256-bit line data
    output logic         o_bram_wr_en,
    output logic [31:0]  o_bram_wr_strobe,   // Byte enables (all 32 bits set for full line)

    // First 4 results exposed to registers (for quick host access)
    output logic [15:0] o_result_0,
    output logic [15:0] o_result_1,
    output logic [15:0] o_result_2,
    output logic [15:0] o_result_3,

    // Circular buffer interface
    input  logic [12:0] i_rd_ptr,            // Read pointer from host (0-8191 FP16)
    output logic [12:0] o_wr_ptr,            // Write pointer (0-8191 FP16)
    output logic [13:0] o_used_entries,      // Number of valid FP16 results (0-8192)
    output logic        o_empty,             // Buffer empty flag
    output logic        o_almost_full        // Backpressure signal
);

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam TOTAL_CAPACITY = 8192;           // Total FP16 results
    localparam ALMOST_FULL_THRESHOLD = 8128;    // Trigger when < 256 FP16s free

    // =========================================================================
    // State Machine for READOUT Command
    // =========================================================================
    typedef enum logic [1:0] {
        BRIDGE_IDLE,        // Wait for READOUT command
        BRIDGE_COPY,        // Copy lines from arbiter to outgoing BRAM
        BRIDGE_DONE         // Signal completion
    } bridge_state_t;

    bridge_state_t bridge_state_reg;

    // =========================================================================
    // Internal State
    // =========================================================================
    logic [12:0]  rd_ptr;                    // FP16 read position (0-8191)
    logic [12:0]  wr_ptr;                    // FP16 write position (0-8191)
    logic [12:0]  first_four_count;          // Counter for first 4 results capture
    logic [8:0]   copy_line_count;           // Lines copied so far (0-511)
    logic [8:0]   total_lines_to_copy;       // Total lines to copy
    logic         readout_done_reg;          // Completion signal

    // =========================================================================
    // Circular Buffer Management
    // =========================================================================
    logic [13:0] used_entries;               // 14-bit to hold 0-8192

    // Calculate used entries (circular buffer arithmetic)
    always_comb begin
        if (wr_ptr >= rd_ptr) begin
            used_entries = {1'b0, wr_ptr} - {1'b0, rd_ptr};  // Normal case
        end else begin
            used_entries = 14'd8192 - {1'b0, rd_ptr} + {1'b0, wr_ptr};  // Wrapped case
        end
    end

    // =========================================================================
    // Continuous Line Capture (Independent of READOUT State Machine)
    // =========================================================================
    // The arbiter outputs lines during MATMUL execution via i_line_valid strobes.
    // The bridge must capture these lines in real-time, not wait for READOUT.
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_bram_wr_en <= 1'b0;
            o_bram_wr_addr <= 9'd0;
            o_bram_wr_data <= 256'd0;
            o_bram_wr_strobe <= 32'd0;
            copy_line_count <= 9'd0;
            wr_ptr <= 13'd0;  // CRITICAL FIX: Reset write pointer
        end else begin
            // Default: no write
            o_bram_wr_en <= 1'b0;

            // Capture incoming line whenever valid (regardless of state machine)
            if (i_line_valid && !o_almost_full) begin
                // Write full 256-bit line to BRAM
                o_bram_wr_addr <= i_line_addr;       // Use arbiter's line address
                o_bram_wr_data <= i_line_data;       // 256-bit packed line
                o_bram_wr_en <= 1'b1;
                o_bram_wr_strobe <= 32'hFFFFFFFF;    // All bytes enabled (full line write)

                // Update write pointer (16 FP16 per line)
                if (wr_ptr + 13'd16 >= TOTAL_CAPACITY) begin
                    wr_ptr <= (wr_ptr + 13'd16) - TOTAL_CAPACITY;  // Wrap around
                end else begin
                    wr_ptr <= wr_ptr + 13'd16;
                end

                copy_line_count <= copy_line_count + 1;

                `ifdef SIMULATION
                $display("[BRIDGE] @%0t LINE_CAPTURE: Line[%0d] written to BRAM, wr_ptr=%0d",
                        $time, i_line_addr, wr_ptr + 13'd16);
                `endif
            end

            // Reset line count when READOUT starts (for tracking)
            if (i_readout_en) begin
                copy_line_count <= 9'd0;
            end
        end
    end

    // =========================================================================
    // READOUT State Machine - Synchronization Only
    // =========================================================================
    // The READOUT command is just a synchronization barrier.
    // Lines are already captured above, so READOUT just waits for collection_done.
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            bridge_state_reg <= BRIDGE_IDLE;
            readout_done_reg <= 1'b0;
        end else begin
            case (bridge_state_reg)
                BRIDGE_IDLE: begin
                    // Clear completion signal when idle
                    readout_done_reg <= 1'b0;

                    // Wait for READOUT command
                    if (i_readout_en) begin
                        bridge_state_reg <= BRIDGE_COPY;

                        `ifdef SIMULATION
                        $display("[BRIDGE] @%0t READOUT received, waiting for collection_done", $time);
                        `endif
                    end
                end

                BRIDGE_COPY: begin
                    // Wait for arbiter to finish collecting
                    // Lines are being captured continuously by the separate always_ff block above
                    if (i_collection_done) begin
                        bridge_state_reg <= BRIDGE_DONE;
                        `ifdef SIMULATION
                        $display("[BRIDGE] @%0t Collection complete", $time);
                        `endif
                    end
                end

                BRIDGE_DONE: begin
                    // Signal completion
                    readout_done_reg <= 1'b1;
                    bridge_state_reg <= BRIDGE_IDLE;

                    `ifdef SIMULATION
                    $display("[BRIDGE] @%0t READOUT complete", $time);
                    `endif
                end

                default: bridge_state_reg <= BRIDGE_IDLE;
            endcase
        end
    end

    // =========================================================================
    // First 4 Results Capture (from line data)
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_result_0 <= 16'd0;
            o_result_1 <= 16'd0;
            o_result_2 <= 16'd0;
            o_result_3 <= 16'd0;
            first_four_count <= 13'd0;
        end else begin
            // Capture first 4 FP16 from incoming lines
            if (i_line_valid && first_four_count < 4) begin
                case (first_four_count)
                    13'd0: o_result_0 <= i_line_data[15:0];    // First FP16 in line
                    13'd1: o_result_1 <= i_line_data[15:0];
                    13'd2: o_result_2 <= i_line_data[15:0];
                    13'd3: o_result_3 <= i_line_data[15:0];
                    default: ;
                endcase
                first_four_count <= first_four_count + 13'd1;
            end

            // Reset counter on READOUT
            if (i_readout_en) begin
                first_four_count <= 13'd0;
            end
        end
    end

    // =========================================================================
    // Read Pointer Management
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            rd_ptr <= 13'd0;
        end else if (i_rd_ptr != rd_ptr) begin
            rd_ptr <= i_rd_ptr;
        end
    end

    // =========================================================================
    // Threshold Detection for Backpressure
    // =========================================================================
    always_comb begin
        o_almost_full = (used_entries >= ALMOST_FULL_THRESHOLD);
        o_empty = (wr_ptr == rd_ptr);
    end

    // =========================================================================
    // Output Assignments
    // =========================================================================
    assign o_wr_ptr = wr_ptr;
    assign o_used_entries = used_entries;
    assign o_readout_done = readout_done_reg;

endmodule : result_fifo_to_simple_bram
