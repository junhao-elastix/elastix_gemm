// ------------------------------------------------------------------
// Compute Engine - BRAM Readback Test Mode
//
// Purpose: Temporary stub for verifying FETCH → dispatcher_bram path
//
// Test Mode Operation:
//   - Reads sequential BRAM addresses from i_left_addr to i_left_addr + i_dim_b - 1
//   - Outputs 256-bit BRAM data as FP24 stream (using upper 24 bits)
//   - Allows host to verify dispatcher BRAM contents via result DMA
//
// Usage:
//   1. DMA test pattern to GDDR6
//   2. Issue FETCH command (loads GDDR6 → dispatcher BRAM)
//   3. Issue MATMUL with:
//      - i_left_addr = BRAM start address to read
//      - i_dim_b = number of BRAM lines to read
//   4. DMA results from Result BRAM and compare
//
// Author: Temporary test for dispatcher validation
// Date: Wed Oct 8 2025
// ------------------------------------------------------------------

module compute_engine
import gemm_pkg::*;
(
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // Master Control Interface (TILE command) - using subset for readback
    input  logic                          i_tile_en,
    input  logic [tile_mem_addr_width_gp-1:0] i_left_addr,      // BRAM start address
    input  logic [tile_mem_addr_width_gp-1:0] i_right_addr,     // Unused in readback mode
    input  logic [tile_mem_addr_width_gp-1:0] i_left_ugd_len,   // Unused
    input  logic [tile_mem_addr_width_gp-1:0] i_right_ugd_len,  // Unused
    input  logic [tile_mem_addr_width_gp-1:0] i_vec_len,        // Unused
    input  logic [7:0]                    i_dim_b,           // Number of BRAM lines to read
    input  logic [7:0]                    i_dim_c,           // Unused
    input  logic [7:0]                    i_dim_v,           // Unused
    input  logic                          i_left_man_4b,     // Unused
    input  logic                          i_right_man_4b,    // Unused
    input  logic                          i_main_loop_over_left, // Unused
    output logic                          o_tile_done,

    // BRAM Read Interface (from Dispatcher BRAM)
    output logic [10:0]                   o_bram_rd_addr,
    input  logic [255:0]                  i_bram_rd_data,
    output logic                          o_bram_rd_en,

    // Result FIFO Write Interface
    output logic [23:0]                   o_result_data,
    output logic                          o_result_valid,
    input  logic                          i_result_full,
    input  logic                          i_result_afull,

    // Debug Interface
    output logic [3:0]                    o_ce_state
);

    // ===================================================================
    // BRAM Readback Test FSM
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE         = 4'd0,
        ST_READ_REQUEST = 4'd1,  // Issue BRAM read
        ST_READ_WAIT    = 4'd2,  // Wait for BRAM latency
        ST_OUTPUT       = 4'd3,  // Output data to result stream
        ST_NEXT         = 4'd4,  // Move to next address
        ST_DONE         = 4'd5
    } state_t;

    state_t state_reg, state_next;

    // Control registers
    logic [10:0] start_addr_reg;
    logic [10:0] current_addr_reg;
    logic [7:0]  lines_to_read_reg;
    logic [7:0]  lines_read_reg;
    logic [255:0] bram_data_reg;
    logic [3:0]  output_count_reg;  // 0-10 (output 11 FP24 values from 256-bit line)

    // ===================================================================
    // State Machine
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
        end
    end

    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (i_tile_en) begin
                    state_next = ST_READ_REQUEST;
                    $display("[CE_READBACK] @%0t TILE_EN: start_addr=%0d, num_lines=%0d",
                             $time, i_left_addr, i_dim_b);
                end
            end

            ST_READ_REQUEST: begin
                state_next = ST_READ_WAIT;
            end

            ST_READ_WAIT: begin
                // 1 cycle BRAM latency
                state_next = ST_OUTPUT;
            end

            ST_OUTPUT: begin
                if (!i_result_afull) begin
                    if (output_count_reg >= 10) begin
                        // Outputted 11 values, move to next BRAM line
                        state_next = ST_NEXT;
                    end
                end
            end

            ST_NEXT: begin
                if (lines_read_reg >= lines_to_read_reg - 1) begin
                    state_next = ST_DONE;
                end else begin
                    state_next = ST_READ_REQUEST;
                end
            end

            ST_DONE: begin
                state_next = ST_IDLE;
            end
        endcase
    end

    // ===================================================================
    // Control Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            start_addr_reg <= '0;
            current_addr_reg <= '0;
            lines_to_read_reg <= '0;
            lines_read_reg <= '0;
            bram_data_reg <= '0;
            output_count_reg <= '0;
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    if (i_tile_en) begin
                        start_addr_reg <= i_left_addr[10:0];
                        current_addr_reg <= i_left_addr[10:0];
                        lines_to_read_reg <= i_dim_b;
                        lines_read_reg <= '0;
                        output_count_reg <= '0;
                    end
                end

                ST_READ_WAIT: begin
                    // Capture BRAM data (available after 1-cycle latency)
                    bram_data_reg <= i_bram_rd_data;
                    output_count_reg <= '0;
                    $display("[CE_READBACK] @%0t BRAM_READ: addr=%0d, data[63:0]=0x%016h",
                             $time, current_addr_reg, i_bram_rd_data[63:0]);
                end

                ST_OUTPUT: begin
                    if (!i_result_afull) begin
                        output_count_reg <= output_count_reg + 1;
                    end
                end

                ST_NEXT: begin
                    current_addr_reg <= current_addr_reg + 1;
                    lines_read_reg <= lines_read_reg + 1;
                end
            endcase
        end
    end

    // ===================================================================
    // BRAM Read Control
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            o_bram_rd_addr <= '0;
            o_bram_rd_en <= 1'b0;
        end else begin
            o_bram_rd_en <= 1'b0;  // Default

            if (state_reg == ST_READ_REQUEST) begin
                o_bram_rd_addr <= current_addr_reg;
                o_bram_rd_en <= 1'b1;
            end
        end
    end

    // ===================================================================
    // Result Output
    // ===================================================================
    logic [23:0] result_data_reg;
    logic result_valid_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            result_data_reg <= '0;
            result_valid_reg <= 1'b0;
        end else begin
            result_valid_reg <= 1'b0;  // Default

            if (state_reg == ST_OUTPUT && !i_result_afull) begin
                // Extract 24 bits from 256-bit BRAM data based on output_count
                // Each FP24 value uses 24 bits, we can fit 10.66 values per 256-bit line
                // For simplicity, output first 11×24 = 264 bits (some overlap acceptable)
                case (output_count_reg)
                    4'd0:  result_data_reg <= bram_data_reg[23:0];
                    4'd1:  result_data_reg <= bram_data_reg[47:24];
                    4'd2:  result_data_reg <= bram_data_reg[71:48];
                    4'd3:  result_data_reg <= bram_data_reg[95:72];
                    4'd4:  result_data_reg <= bram_data_reg[119:96];
                    4'd5:  result_data_reg <= bram_data_reg[143:120];
                    4'd6:  result_data_reg <= bram_data_reg[167:144];
                    4'd7:  result_data_reg <= bram_data_reg[191:168];
                    4'd8:  result_data_reg <= bram_data_reg[215:192];
                    4'd9:  result_data_reg <= bram_data_reg[239:216];
                    4'd10: result_data_reg <= {bram_data_reg[255:240], 8'h00};  // Last partial
                    default: result_data_reg <= 24'h0;
                endcase
                result_valid_reg <= 1'b1;

                if (output_count_reg == 0 || output_count_reg == 10) begin
                    $display("[CE_READBACK] @%0t OUTPUT[%0d]: data=0x%06h",
                             $time, output_count_reg, result_data_reg);
                end
            end
        end
    end

    assign o_result_data = result_data_reg;
    assign o_result_valid = result_valid_reg;

    // ===================================================================
    // Status Outputs
    // ===================================================================
    assign o_ce_state = state_reg;
    assign o_tile_done = (state_reg == ST_DONE);

endmodule : compute_engine
