// ------------------------------------------------------------------
// Command FIFO Module
//
// Purpose: Synchronous FIFO for buffering incoming uCode commands
// Features:
//  - Simple registered read (1-cycle latency)
//  - Full/empty status flags
//  - Count output for monitoring available entries
//
// Author: Junhao Pan
// Date: 10/02/2025
// ------------------------------------------------------------------

module cmd_fifo
import gemm_pkg::*;
(
    input  logic                        i_clk,
    input  logic                        i_reset_n,

    // Write Interface
    input  logic [cmd_buf_width_gp-1:0] i_wr_data,
    input  logic                        i_wr_en,
    output logic                        o_full,
    output logic                        o_afull,  // Almost full threshold

    // Read Interface
    output logic [cmd_buf_width_gp-1:0] o_rd_data,
    input  logic                        i_rd_en,
    output logic                        o_empty,

    // Status
    output logic [6:0]                  o_count,

    // Debug
    output logic [15:0]                 o_total_writes  // Total writes ever (for debug)
);

    // ===================================================================
    // Parameters
    // ===================================================================
    localparam DEPTH      = cmd_buf_els_gp;
    localparam DATA_WIDTH = cmd_buf_width_gp;
    localparam ADDR_WIDTH = $clog2(DEPTH);
    localparam AFULL_THRESHOLD = 48;

    // ===================================================================
    // Internal Signals
    // ===================================================================

    // FIFO Storage - Use BRAM inference with ram_style attribute
    // Per Speedster7t UG086 p.265, proper inference patterns for BRAM
    (* ram_style = "block" *) logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
    
    // Initialize FIFO memory for simulation only (prevents X-states on first reads)
    `ifdef SIMULATION
    integer init_i;
    initial begin
        for (init_i = 0; init_i < DEPTH; init_i = init_i + 1) begin
            mem[init_i] = '0;
        end
    end
    `endif

    // Pointers
    logic [ADDR_WIDTH-1:0] wr_ptr;
    logic [ADDR_WIDTH-1:0] rd_ptr;

    // Count and Status
    logic [ADDR_WIDTH:0]   count_reg;
    logic                  full_reg;
    logic                  empty_reg;
    logic                  afull_reg;

    // Output data register
    logic [DATA_WIDTH-1:0] rd_data_reg;

    // Debug: Count total writes ever
    logic [15:0] total_writes;

    // ===================================================================
    // Write Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            wr_ptr <= '0;
            total_writes <= 16'd0;
        end else begin
            if (i_wr_en && !full_reg) begin
                mem[wr_ptr] <= i_wr_data;
                wr_ptr <= wr_ptr + 1'b1;
                total_writes <= total_writes + 1'd1;
                `ifdef SIMULATION
                $display("[FIFO_WRITE] @%0t wr_ptr=%0d, writing mem[%0d]=0x%08x",
                         $time, wr_ptr, wr_ptr, i_wr_data);
                `endif
            end
        end
    end

    // ===================================================================
    // Read Logic (Simple Registered Read - 1 cycle latency)
    // ===================================================================

    // Internal read pointer and output register
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            rd_ptr <= '0;
            rd_data_reg <= '0;
        end else begin
            if (i_rd_en && !empty_reg) begin
                rd_ptr <= rd_ptr + 1'b1;
                rd_data_reg <= mem[rd_ptr];  // Simple registered read
                `ifdef SIMULATION
                $display("[FIFO_READ] @%0t rd_en=1, empty=0, rd_ptr=%0d, reading mem[%0d]=0x%08x",
                         $time, empty_reg, rd_ptr, rd_ptr, mem[rd_ptr]);
                `endif
            end else if (i_rd_en && empty_reg) begin
                `ifdef SIMULATION
                $display("[FIFO_SKIP] @%0t rd_en=1, but empty=1, NOT reading", $time);
                `endif
            end
        end
    end

    // Output assignment
    assign o_rd_data = rd_data_reg;

    // ===================================================================
    // Count and Status Logic
    // ===================================================================

    // Next count value for immediate empty flag update
    logic [ADDR_WIDTH:0] count_next;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            count_reg <= '0;
        end else begin
            count_reg <= count_next;
        end
    end

    // Calculate next count combinatorially for zero-latency status
    always_comb begin
        case ({i_wr_en && !full_reg, i_rd_en && !empty_reg})
            2'b10:   count_next = count_reg + 1'b1;  // Write only
            2'b01:   count_next = count_reg - 1'b1;  // Read only
            default: count_next = count_reg;         // Both or neither
        endcase
    end

    // Status flags - Use NEXT count for immediate response
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            full_reg <= 1'b0;
            empty_reg <= 1'b1;
            afull_reg <= 1'b0;
        end else begin
            // Use count_next for zero-cycle latency on status updates
            full_reg  <= (count_next == DEPTH);
            empty_reg <= (count_next == 0);
            afull_reg <= (count_next >= AFULL_THRESHOLD);
        end
    end

    // Output assignments
    assign o_full  = full_reg;
    assign o_empty = empty_reg;
    assign o_afull = afull_reg;
    assign o_count = count_reg;
    assign o_total_writes = total_writes;

    // ===================================================================
    // Assertions (for simulation only)
    // ===================================================================

    `ifdef SIM
        // Check for overflow
        property no_overflow;
            @(posedge i_clk) disable iff (~i_reset_n)
            (i_wr_en && full_reg) |=> $stable(wr_ptr);
        endproperty
        assert property (no_overflow) else
            $error("[CMD_FIFO] Write to full FIFO attempted!");

        // Check for underflow
        property no_underflow;
            @(posedge i_clk) disable iff (~i_reset_n)
            (i_rd_en && empty_reg) |=> $stable(rd_ptr);
        endproperty
        assert property (no_underflow) else
            $error("[CMD_FIFO] Read from empty FIFO attempted!");
    `endif

endmodule : cmd_fifo
