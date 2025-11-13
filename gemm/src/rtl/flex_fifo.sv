// ------------------------------------------------------------------
// Flexible Generic FIFO Module
//
// Purpose: Parameterizable synchronous FIFO with BRAM inference
// Features:
//  - Parameterizable width and depth
//  - 1-cycle read latency (standard synchronous BRAM read)
//  - Adaptive almost-full threshold (10% remaining or 64, whichever smaller)
//  - Full/empty status flags
//  - Count output for monitoring
//
// Almost-Full Threshold Logic:
//  - Remaining space = min(10% of DEPTH, 64)
//  - AFULL asserts when remaining space drops below threshold
//  - Examples:
//    * DEPTH=512  → 10%=51,  min(51,64)=51,  AFULL_THRESHOLD=461
//    * DEPTH=1024 → 10%=102, min(102,64)=64, AFULL_THRESHOLD=960
//    * DEPTH=256  → 10%=26,  min(26,64)=26,  AFULL_THRESHOLD=230
//
// Author: Junhao Pan
// Date: 11/13/2025
// ------------------------------------------------------------------

module flex_fifo #(
    parameter DATA_WIDTH = 16,
    parameter DEPTH = 128
)(
    input  logic                    i_clk,
    input  logic                    i_reset_n,

    // Write Interface
    input  logic [DATA_WIDTH-1:0]   i_wr_data,
    input  logic                    i_wr_en,
    output logic                    o_full,
    output logic                    o_afull,

    // Read Interface
    output logic [DATA_WIDTH-1:0]   o_rd_data,
    input  logic                    i_rd_en,
    output logic                    o_empty,

    // Status
    output logic [$clog2(DEPTH):0]  o_count   // 0 to DEPTH
);

    // ===================================================================
    // Parameters - Almost-Full Threshold
    // ===================================================================
    localparam ADDR_WIDTH = $clog2(DEPTH);

    // Calculate 10% of DEPTH (ceiling division)
    localparam TEN_PERCENT = (DEPTH + 9) / 10;

    // Remaining space = min(10% of DEPTH, 64)
    localparam REMAINING_SPACE = (TEN_PERCENT < 64) ? TEN_PERCENT : 64;

    // Almost-full threshold
    localparam AFULL_THRESHOLD = DEPTH - REMAINING_SPACE;

    // ===================================================================
    // Internal Signals
    // ===================================================================

    // FIFO Storage - Use BRAM inference
    (* ram_style = "block" *) logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // Initialize FIFO memory for simulation only
    `ifdef SIMULATION
    integer init_i;
    initial begin
        for (init_i = 0; init_i < DEPTH; init_i = init_i + 1) begin
            mem[init_i] = '0;
        end
        // Display configuration
        $display("[FLEX_FIFO] Configuration: DEPTH=%0d, DATA_WIDTH=%0d", DEPTH, DATA_WIDTH);
        $display("[FLEX_FIFO] 10%% of DEPTH = %0d, REMAINING_SPACE = %0d", TEN_PERCENT, REMAINING_SPACE);
        $display("[FLEX_FIFO] AFULL_THRESHOLD = %0d (triggers with %0d remaining)",
                 AFULL_THRESHOLD, REMAINING_SPACE);
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

    // ===================================================================
    // FIFO Control Logic
    // ===================================================================

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            wr_ptr      <= '0;
            rd_ptr      <= '0;
            count_reg   <= '0;
            full_reg    <= 1'b0;
            empty_reg   <= 1'b1;
            afull_reg   <= 1'b0;
            rd_data_reg <= '0;
        end else begin
            // Write operation
            if (i_wr_en && !full_reg) begin
                mem[wr_ptr] <= i_wr_data;
                wr_ptr <= wr_ptr + 1;
            end

            // Read operation (1-cycle latency)
            if (i_rd_en && !empty_reg) begin
                rd_data_reg <= mem[rd_ptr];
                rd_ptr <= rd_ptr + 1;
            end

            // Update count
            case ({i_wr_en && !full_reg, i_rd_en && !empty_reg})
                2'b10:   count_reg <= count_reg + 1;  // Write only
                2'b01:   count_reg <= count_reg - 1;  // Read only
                default: count_reg <= count_reg;       // Both or neither
            endcase

            // Update status flags
            empty_reg <= (count_reg == 0) || (count_reg == 1 && i_rd_en && !i_wr_en);
            full_reg  <= (count_reg == DEPTH) || (count_reg == DEPTH-1 && i_wr_en && !i_rd_en);
            afull_reg <= (count_reg >= AFULL_THRESHOLD);
        end
    end

    // ===================================================================
    // Output Assignments
    // ===================================================================
    assign o_rd_data = rd_data_reg;
    assign o_full    = full_reg;
    assign o_afull   = afull_reg;
    assign o_empty   = empty_reg;
    assign o_count   = count_reg;

endmodule : flex_fifo
