// ------------------------------------------------------------------
// Fetcher 2D Module (Generic Block Reader)
//
// Purpose: Read N lines from memory address, push to external FIFO
// Features:
//  - 64-deep internal FIFO for AR burst management
//  - Back-to-back AR issuing (up to 32 outstanding requests)
//  - Configurable fetch length via i_fetch_len
//  - Raw 256-bit data pushed to external FIFO
//  - State machine: IDLE <-> ACTIVE (simplified 2-state)
//
// Usage:
//  1. Set i_fetch_addr (line address) and i_fetch_len (number of lines)
//  2. Pulse i_fetch_en high for one cycle
//  3. Wait for o_fetch_done
//  4. Downstream drains external FIFO
// 
// VERY IMPORTANT:
//  GDDR6 CONTROL ID is used to route the address to the correct GDDR6 controller.
//  Addr[41:37] = 5'b00000
//  Addr[36:33] = GDDR6_CTRL_ID
//  Addr[32:0] = Line address
//
// Author: Junhao Pan
// Date: 01/21/2026
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module fetcher_2d
import gemm_pkg::*;
#(
    parameter DATA_WIDTH = 256,
    parameter AXI_ADDR_WIDTH = 42,
    parameter [8:0] GDDR6_CTRL_ID = 9'd0
)
(
    // Clock and Reset
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // Fetch Command Interface
    input  logic                         i_fetch_en,
    input  logic [link_addr_width_gp-1:0] i_fetch_addr,  // Line address (not byte address)
    input  logic [link_len_width_gp-1:0]  i_fetch_len,   // Number of lines to fetch
    output logic                         o_fetch_done,

    // External FIFO Write Interface
    output logic [DATA_WIDTH-1:0]        o_fifo_wr_data,
    output logic                         o_fifo_wr_en,
    input  logic                         i_fifo_afull,

    // AXI-4 Initiator Interface
    t_AXI4.initiator                     axi_ddr_if,

    // Debug Interface
    output logic [3:0]                   o_fetcher_state,
    output logic [15:0]                  o_lines_received
);

    // ===================================================================
    // State Machine Definition (Simplified 2-state)
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE         = 4'd0,
        ST_FETCH_ACTIVE = 4'd1
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam BURST_LEN = 16;              // 16 beats per burst
    localparam AXI_ARLEN = BURST_LEN - 1;   // arlen = 15 means 16 beats
    localparam ADDR_BYTE_SHIFT = 5;         // 32 bytes per beat
    localparam AR_FIFO_DEPTH = 64;

    // ===================================================================
    // Internal Signals
    // ===================================================================
    logic [link_addr_width_gp-1:0] fetch_addr_reg;
    logic [link_len_width_gp-1:0]  fetch_len_reg;
    logic        fetch_en_prev;

    // Calculated burst count
    logic [9:0]  total_bursts_reg;          // (fetch_len + 15) / 16

    // AR issuing control
    logic [9:0]  ars_issued;
    logic [15:0] current_line_reg;
    logic        ar_issue_req;
    logic        ar_can_issue;

    // R data receiving control
    logic [15:0] lines_received;
    logic [15:0] lines_to_receive;
    
    // Completion detection
    logic        fetch_complete;

    // ===================================================================
    // AR FIFO - 64-deep Regular FIFO
    // ===================================================================
    logic [15:0] ar_fifo [0:AR_FIFO_DEPTH-1];
    logic [5:0]  ar_fifo_wr_ptr;
    logic [5:0]  ar_fifo_rd_ptr;
    logic [6:0]  ar_fifo_count;
    logic [15:0] ar_fifo_rd_data_reg;
    logic        ar_fifo_empty;
    logic        ar_fifo_full;
    logic        ar_fifo_wr;
    logic        ar_fifo_rd;

    assign ar_fifo_empty = (ar_fifo_count == 0);
    assign ar_fifo_full = (ar_fifo_count >= AR_FIFO_DEPTH);
    assign ar_fifo_wr = ar_issue_req && ar_can_issue;
    assign ar_fifo_rd = (axi_ddr_if.arvalid && axi_ddr_if.arready);
    assign ar_can_issue = !ar_fifo_full;

    // FIFO write and read with registered output
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_fifo_wr_ptr <= '0;
            ar_fifo_rd_ptr <= '0;
            ar_fifo_rd_data_reg <= '0;
        end else if (state_reg == ST_IDLE) begin
            // Reset FIFO when idle
            ar_fifo_wr_ptr <= '0;
            ar_fifo_rd_ptr <= '0;
            ar_fifo_rd_data_reg <= '0;
        end else begin
            if (ar_fifo_wr) begin
                ar_fifo[ar_fifo_wr_ptr] <= current_line_reg;
                ar_fifo_wr_ptr <= ar_fifo_wr_ptr + 1;

                if (ar_fifo_empty) begin
                    ar_fifo_rd_data_reg <= current_line_reg;
                end
            end

            if (ar_fifo_rd) begin
                ar_fifo_rd_ptr <= ar_fifo_rd_ptr + 1;
                if ((ar_fifo_count > 1) || ar_fifo_wr) begin
                    if (ar_fifo_wr && (ar_fifo_wr_ptr == (ar_fifo_rd_ptr + 1))) begin
                        ar_fifo_rd_data_reg <= current_line_reg;
                    end else begin
                        ar_fifo_rd_data_reg <= ar_fifo[ar_fifo_rd_ptr + 1];
                    end
                end
            end
        end
    end

    // FIFO count
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_fifo_count <= '0;
        end else if (state_reg == ST_IDLE) begin
            ar_fifo_count <= '0;
        end else begin
            case ({ar_fifo_wr, ar_fifo_rd})
                2'b00: ar_fifo_count <= ar_fifo_count;
                2'b01: ar_fifo_count <= ar_fifo_count - 1;
                2'b10: ar_fifo_count <= ar_fifo_count + 1;
                2'b11: ar_fifo_count <= ar_fifo_count;
            endcase
        end
    end

    // ===================================================================
    // Completion Detection
    // ===================================================================
    assign fetch_complete = (state_reg == ST_FETCH_ACTIVE) && 
                           (lines_received >= lines_to_receive) && 
                           (lines_to_receive > 0);

    // ===================================================================
    // State Machine
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
            fetch_en_prev <= 1'b0;
        end else begin
            state_reg <= state_next;
            fetch_en_prev <= i_fetch_en;
        end
    end

    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (i_fetch_en && !fetch_en_prev) begin
                    state_next = ST_FETCH_ACTIVE;
                end
            end

            ST_FETCH_ACTIVE: begin
                // Complete when all requested lines received
                if (fetch_complete) begin
                    state_next = ST_IDLE;
                end
            end

            default: state_next = ST_IDLE;
        endcase
    end

    // Debug: Trace state transitions and command processing
    // synthesis translate_off
    `ifdef DEBUG_FETCHER
    always_ff @(posedge i_clk) begin
        if (i_fetch_en && !fetch_en_prev) begin
            $display("[FETCHER_%0d] @%0t START: addr=0x%06x, len=%0d",
                     GDDR6_CTRL_ID[3:0], $time, i_fetch_addr, i_fetch_len);
        end
        if (state_reg != state_next) begin
            $display("[FETCHER_%0d] @%0t STATE: %0d -> %0d",
                     GDDR6_CTRL_ID[3:0], $time, state_reg, state_next);
        end
        if (fetch_complete) begin
            $display("[FETCHER_%0d] @%0t DONE: received=%0d lines",
                     GDDR6_CTRL_ID[3:0], $time, lines_received);
        end
    end
    `endif
    // synthesis translate_on

    // ===================================================================
    // FETCH Command Processing
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            fetch_addr_reg <= '0;
            fetch_len_reg <= '0;
            total_bursts_reg <= '0;
            lines_to_receive <= '0;
            ars_issued <= '0;
            current_line_reg <= '0;
            lines_received <= '0;
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    if (i_fetch_en && !fetch_en_prev) begin
                        fetch_addr_reg <= i_fetch_addr;
                        fetch_len_reg <= i_fetch_len;
                        // Calculate bursts needed: ceiling(fetch_len / 16)
                        total_bursts_reg <= (i_fetch_len + BURST_LEN - 1) / BURST_LEN;
                        lines_to_receive <= i_fetch_len;
                        ars_issued <= '0;
                        current_line_reg <= '0;
                        lines_received <= '0;
                    end
                end

                ST_FETCH_ACTIVE: begin
                    // AR issuing
                    if (ar_issue_req && ar_can_issue) begin
                        current_line_reg <= current_line_reg + BURST_LEN;
                        ars_issued <= ars_issued + 1;
                    end

                    // R data receiving (count up to requested length)
                    if (axi_ddr_if.rvalid && axi_ddr_if.rready && lines_received < lines_to_receive) begin
                        lines_received <= lines_received + 1;
                    end
                end

                default: begin
                    // Nothing to do
                end
            endcase
        end
    end

    // AR issue request: issue bursts until we've covered all requested lines
    always_comb begin
        ar_issue_req = 1'b0;
        if (state_reg == ST_FETCH_ACTIVE) begin
            ar_issue_req = (ars_issued < total_bursts_reg);
        end
    end

    // ===================================================================
    // AXI Read Address Channel
    // ===================================================================
    logic ar_valid_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_valid_reg <= 1'b0;
        end else if (state_reg == ST_IDLE) begin
            ar_valid_reg <= 1'b0;
        end else begin
            if (ar_fifo_wr) begin
                ar_valid_reg <= 1'b1;
            end else if (axi_ddr_if.arvalid && axi_ddr_if.arready && ar_fifo_count == 1) begin
                ar_valid_reg <= 1'b0;
            end
        end
    end

    // AXI4 AR channel assignments
    logic [25:0] line_addr_26bit;
    always_comb begin
        line_addr_26bit = (fetch_addr_reg + ar_fifo_rd_data_reg[10:0]);
    end

    assign axi_ddr_if.arvalid = ar_valid_reg;
    assign axi_ddr_if.arid = 8'hFE;
    assign axi_ddr_if.araddr = {GDDR6_CTRL_ID, 2'b00, line_addr_26bit, {ADDR_BYTE_SHIFT{1'b0}}};
    assign axi_ddr_if.arlen = AXI_ARLEN;
    assign axi_ddr_if.arsize = 3'h5;  // 32 bytes
    assign axi_ddr_if.arburst = 2'b01;  // INCR
    assign axi_ddr_if.arlock = 1'b0;
    assign axi_ddr_if.arcache = 4'h0;
    assign axi_ddr_if.arprot = 3'b010;
    assign axi_ddr_if.arqos = 4'h0;
    assign axi_ddr_if.arregion = 4'h0;

    // ===================================================================
    // AXI Read Data Channel - with backpressure from FIFO
    // ===================================================================
    assign axi_ddr_if.rready = (state_reg == ST_FETCH_ACTIVE) && !i_fifo_afull;

    // ===================================================================
    // FIFO Write Logic - Push raw AXI data to external FIFO
    // ===================================================================
    logic fifo_wr_en_reg;
    logic [DATA_WIDTH-1:0] fifo_wr_data_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            fifo_wr_en_reg <= 1'b0;
            fifo_wr_data_reg <= '0;
        end else begin
            fifo_wr_en_reg <= 1'b0;  // Default

            if (state_reg == ST_FETCH_ACTIVE && axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                fifo_wr_data_reg <= axi_ddr_if.rdata;
                fifo_wr_en_reg <= 1'b1;
            end
        end
    end

    assign o_fifo_wr_data = fifo_wr_data_reg;
    assign o_fifo_wr_en = fifo_wr_en_reg;

    // ===================================================================
    // AXI Write Channels (unused - tie off)
    // ===================================================================
    assign axi_ddr_if.awvalid = 1'b0;
    assign axi_ddr_if.awid = '0;
    assign axi_ddr_if.awaddr = '0;
    assign axi_ddr_if.awlen = '0;
    assign axi_ddr_if.awsize = '0;
    assign axi_ddr_if.awburst = '0;
    assign axi_ddr_if.awlock = '0;
    assign axi_ddr_if.awcache = '0;
    assign axi_ddr_if.awprot = '0;
    assign axi_ddr_if.awqos = '0;
    assign axi_ddr_if.awregion = '0;
    assign axi_ddr_if.wvalid = 1'b0;
    assign axi_ddr_if.wdata = '0;
    assign axi_ddr_if.wstrb = '0;
    assign axi_ddr_if.wlast = 1'b0;
    assign axi_ddr_if.bready = 1'b0;

    // ===================================================================
    // Fetch Done Signal - pulse when transitioning ACTIVE -> IDLE
    // ===================================================================
    logic fetch_done_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            fetch_done_reg <= 1'b0;
        end else begin
            // Pulse done for one cycle when fetch completes
            fetch_done_reg <= fetch_complete;
        end
    end

    assign o_fetch_done = fetch_done_reg;

    // ===================================================================
    // Debug Outputs
    // ===================================================================
    assign o_fetcher_state = state_reg;
    assign o_lines_received = lines_received;

endmodule
