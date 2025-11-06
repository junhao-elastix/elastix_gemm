// dispatcher_control_clean.sv
// Cleaned and reorganized version following reference manuals strictly
//
// Key improvements:
// 1. Clearer state machine with explicit control signals
// 2. Separated read and write pipelines
// 3. Simplified tile index management
// 4. Better documentation

module dispatcher_control_clean
import gemm_pkg::*;
(
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // ===================================================================
    // FETCH Interface (GDDR6 → dispatcher_bram)
    // ===================================================================
    input  logic                         i_fetch_en,
    input  logic [31:0]                  i_fetch_addr,
    input  logic [15:0]                  i_fetch_len,
    input  logic                         i_fetch_target,     // 0=left, 1=right
    output logic                         o_fetch_done,

    // AXI Read Interface to NAP (GDDR6 access)
    output logic                         o_axi_arvalid,
    input  logic                         i_axi_arready,
    output logic [39:0]                  o_axi_araddr,
    output logic [7:0]                   o_axi_arlen,
    input  logic                         i_axi_rvalid,
    output logic                         i_axi_rready,
    input  logic [255:0]                 i_axi_rdata,
    input  logic                         i_axi_rlast,

    // ===================================================================
    // DISPATCH Interface (dispatcher_bram → tile_bram)
    // ===================================================================
    input  logic                         i_disp_en,
    input  logic [7:0]                   i_disp_man_nv_cnt,  // Total NVs to dispatch
    input  logic [7:0]                   i_disp_ugd_vec_size,// NVs per batch
    input  logic [15:0]                  i_disp_tile_addr,   // Start addr in tile_bram
    input  logic                         i_disp_man_4b,      // 0=8-bit, 1=4-bit
    input  logic [23:0]                  i_disp_col_en,      // Tile enable mask
    input  logic [4:0]                   i_disp_col_start,   // Starting tile
    input  logic                         i_disp_right,       // 0=left, 1=right
    input  logic                         i_disp_broadcast,   // 0=distribute, 1=broadcast
    output logic                         o_disp_done,

    // ===================================================================
    // Dispatcher BRAM Read Ports (for DISPATCH operation)
    // ===================================================================
    output logic [TILE_ADDR_WIDTH-1:0]  o_disp_man_left_rd_addr,
    output logic                         o_disp_man_left_rd_en,
    input  logic [MAN_WIDTH-1:0]         i_disp_man_left_rd_data,

    output logic [TILE_ADDR_WIDTH-1:0]  o_disp_man_right_rd_addr,
    output logic                         o_disp_man_right_rd_en,
    input  logic [MAN_WIDTH-1:0]         i_disp_man_right_rd_data,

    output logic [TILE_ADDR_WIDTH-1:0]  o_disp_exp_left_rd_addr,
    output logic                         o_disp_exp_left_rd_en,
    input  logic [7:0]                   i_disp_exp_left_rd_data,

    output logic [TILE_ADDR_WIDTH-1:0]  o_disp_exp_right_rd_addr,
    output logic                         o_disp_exp_right_rd_en,
    input  logic [7:0]                   i_disp_exp_right_rd_data,

    // ===================================================================
    // Tile BRAM Write Ports (for DISPATCH operation)
    // ===================================================================
    output logic [8:0]                   o_tile_man_left_wr_addr,
    output logic [MAN_WIDTH-1:0]         o_tile_man_left_wr_data,
    output logic                         o_tile_man_left_wr_en,

    output logic [8:0]                   o_tile_man_right_wr_addr,
    output logic [MAN_WIDTH-1:0]         o_tile_man_right_wr_data,
    output logic                         o_tile_man_right_wr_en,

    output logic [8:0]                   o_tile_exp_left_wr_addr,
    output logic [7:0]                   o_tile_exp_left_wr_data,
    output logic                         o_tile_exp_left_wr_en,

    output logic [8:0]                   o_tile_exp_right_wr_addr,
    output logic [7:0]                   o_tile_exp_right_wr_data,
    output logic                         o_tile_exp_right_wr_en,

    // Multi-tile write enable (one-hot per tile)
    output logic [23:0]                  o_tile_wr_en,

    // ===================================================================
    // Dispatcher BRAM Write Ports (for FETCH operation)
    // ===================================================================
    output logic [DISP_MAN_ADDR_WIDTH-1:0] o_man_left_wr_addr,
    output logic [MAN_WIDTH-1:0]            o_man_left_wr_data,
    output logic                            o_man_left_wr_en,

    output logic [DISP_MAN_ADDR_WIDTH-1:0] o_man_right_wr_addr,
    output logic [MAN_WIDTH-1:0]            o_man_right_wr_data,
    output logic                            o_man_right_wr_en,

    output logic [DISP_EXP_ADDR_WIDTH-1:0] o_exp_left_wr_addr,
    output logic [7:0]                      o_exp_left_wr_data,
    output logic                            o_exp_left_wr_en,

    output logic [DISP_EXP_ADDR_WIDTH-1:0] o_exp_right_wr_addr,
    output logic [7:0]                      o_exp_right_wr_data,
    output logic                            o_exp_right_wr_en
);

    // ===================================================================
    // Parameters
    // ===================================================================
    localparam MAN_WIDTH = 256;
    localparam TILE_ADDR_WIDTH = 9;
    localparam DISP_MAN_ADDR_WIDTH = 9;
    localparam DISP_EXP_ADDR_WIDTH = 9;

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    typedef enum logic [2:0] {
        ST_IDLE         = 3'b000,
        ST_FETCH_BUSY   = 3'b001,
        ST_FETCH_DONE   = 3'b010,
        ST_DISP_BUSY    = 3'b011,
        ST_DISP_DONE    = 3'b100
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // DISPATCH Control Registers
    // ===================================================================
    // Command parameters (captured at DISP start)
    logic [7:0]  disp_man_nv_cnt_reg;       // Total NVs to dispatch
    logic [7:0]  disp_ugd_vec_size_reg;     // NVs per batch to one tile
    logic [15:0] disp_tile_addr_reg;        // Starting address in tile_bram
    logic [23:0] disp_col_en_reg;           // Tile enable mask
    logic        disp_right_reg;            // 0=left, 1=right
    logic        disp_broadcast_reg;        // 0=distribute, 1=broadcast

    // Calculated parameters
    logic [7:0]  disp_num_tiles_reg;        // Number of enabled tiles (popcount of col_en)
    logic [9:0]  disp_batch_lines_reg;      // Lines per batch (ugd_vec_size * 4)
    logic [7:0]  disp_total_batches_reg;    // Total batches (man_nv_cnt / ugd_vec_size)

    // ===================================================================
    // DISPATCH Read Pipeline (from dispatcher_bram)
    // ===================================================================
    logic [4:0]  read_tile_idx;             // Current tile being READ from
    logic [9:0]  read_src_addr;             // Read address in dispatcher_bram
    logic [9:0]  read_dst_addr;             // Destination address in tile_bram
    logic [7:0]  read_batch_cnt;            // Current batch counter
    logic [9:0]  read_line_cnt;             // Lines within current batch
    logic        read_active;               // Read operation active
    logic        read_done;                 // All reads complete

    // ===================================================================
    // DISPATCH Write Pipeline (to tile_bram)
    // ===================================================================
    logic [4:0]  write_tile_idx;            // Current tile being WRITTEN to
    logic [9:0]  write_dst_addr;            // Write address in tile_bram
    logic        write_active;              // Write operation active
    logic        write_valid;               // Write data valid

    // Pipeline registers for 1-cycle BRAM read latency
    logic [4:0]  write_tile_idx_pipe;       // Pipelined tile index
    logic [9:0]  write_dst_addr_pipe;       // Pipelined destination address
    logic        write_valid_pipe;          // Pipelined write valid

    // ===================================================================
    // Helper Functions
    // ===================================================================
    function automatic logic [7:0] popcount_24bit(input logic [23:0] bits);
        int count = 0;
        for (int i = 0; i < 24; i++) begin
            count = count + bits[i];
        end
        return count[7:0];
    endfunction

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
                if (i_fetch_en) begin
                    state_next = ST_FETCH_BUSY;
                end else if (i_disp_en) begin
                    state_next = ST_DISP_BUSY;
                end
            end

            ST_FETCH_BUSY: begin
                // Simplified - actual FETCH implementation would go here
                state_next = ST_FETCH_DONE;
            end

            ST_FETCH_DONE: begin
                state_next = ST_IDLE;
            end

            ST_DISP_BUSY: begin
                if (read_done && !write_valid_pipe) begin
                    // All reads complete AND last write flushed
                    state_next = ST_DISP_DONE;
                end
            end

            ST_DISP_DONE: begin
                state_next = ST_IDLE;
            end

            default: state_next = ST_IDLE;
        endcase
    end

    // ===================================================================
    // DISPATCH Parameter Capture
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            disp_man_nv_cnt_reg   <= '0;
            disp_ugd_vec_size_reg <= '0;
            disp_tile_addr_reg    <= '0;
            disp_col_en_reg       <= '0;
            disp_right_reg        <= '0;
            disp_broadcast_reg    <= '0;
            disp_num_tiles_reg    <= '0;
            disp_batch_lines_reg  <= '0;
            disp_total_batches_reg <= '0;
        end else if (state_reg == ST_IDLE && i_disp_en) begin
            // Capture parameters
            disp_man_nv_cnt_reg   <= i_disp_man_nv_cnt;
            disp_ugd_vec_size_reg <= i_disp_ugd_vec_size;
            disp_tile_addr_reg    <= i_disp_tile_addr;
            disp_col_en_reg       <= i_disp_col_en;
            disp_right_reg        <= i_disp_right;
            disp_broadcast_reg    <= i_disp_broadcast;

            // Calculate derived parameters
            disp_num_tiles_reg    <= popcount_24bit(i_disp_col_en);
            disp_batch_lines_reg  <= {i_disp_ugd_vec_size, 2'b00};  // ugd_vec_size * 4
            disp_total_batches_reg <= i_disp_man_nv_cnt / i_disp_ugd_vec_size;
        end
    end

    // ===================================================================
    // DISPATCH Read Control (from dispatcher_bram)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            read_tile_idx <= '0;
            read_src_addr <= '0;
            read_dst_addr <= '0;
            read_batch_cnt <= '0;
            read_line_cnt <= '0;
            read_active <= '0;
            read_done <= '0;
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    if (i_disp_en) begin
                        // Initialize for DISPATCH
                        read_tile_idx <= '0;
                        read_src_addr <= '0;
                        read_dst_addr <= disp_tile_addr_reg[9:0];
                        read_batch_cnt <= '0;
                        read_line_cnt <= '0;
                        read_active <= '1;
                        read_done <= '0;
                    end
                end

                ST_DISP_BUSY: begin
                    if (read_active) begin
                        // Increment line counter
                        read_line_cnt <= read_line_cnt + 1;

                        // Increment source address (always sequential)
                        read_src_addr <= read_src_addr + 1;

                        // Check if batch complete
                        if (read_line_cnt == disp_batch_lines_reg - 1) begin
                            // Reset for next batch
                            read_line_cnt <= '0;
                            read_batch_cnt <= read_batch_cnt + 1;

                            // Update tile index based on mode
                            if (disp_broadcast_reg) begin
                                // BROADCAST: Same data to all tiles sequentially
                                if (read_tile_idx == disp_num_tiles_reg - 1) begin
                                    // Wrap to tile 0 for next data batch
                                    read_tile_idx <= '0;
                                    // Move to next source data
                                    // (src_addr already incremented above)
                                end else begin
                                    // Next tile, same data
                                    read_tile_idx <= read_tile_idx + 1;
                                    // Reset source address to repeat data
                                    read_src_addr <= read_src_addr - (disp_batch_lines_reg - 1);
                                end
                            end else begin
                                // DISTRIBUTE: Different data to each tile round-robin
                                if (read_tile_idx == disp_num_tiles_reg - 1) begin
                                    // Wrap to tile 0
                                    read_tile_idx <= '0;
                                    // Increment destination when wrapping
                                    read_dst_addr <= read_dst_addr + disp_batch_lines_reg;
                                end else begin
                                    // Next tile
                                    read_tile_idx <= read_tile_idx + 1;
                                end
                            end

                            // Check if all batches complete
                            if (read_batch_cnt == disp_total_batches_reg - 1) begin
                                read_active <= '0;
                                read_done <= '1;
                            end
                        end
                    end
                end

                default: begin
                    read_active <= '0;
                    read_done <= '0;
                end
            endcase
        end
    end

    // ===================================================================
    // DISPATCH Write Pipeline (to tile_bram)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            write_tile_idx_pipe <= '0;
            write_dst_addr_pipe <= '0;
            write_valid_pipe <= '0;
        end else begin
            // Pipeline stage 1: Capture read parameters
            write_tile_idx_pipe <= read_tile_idx;
            write_dst_addr_pipe <= read_dst_addr + read_line_cnt;
            write_valid_pipe <= read_active;
        end
    end

    // ===================================================================
    // Tile Write Enable Generation
    // ===================================================================
    logic [23:0] tile_wr_en_comb;

    always_comb begin
        tile_wr_en_comb = '0;

        if (state_reg == ST_DISP_BUSY && write_valid_pipe) begin
            if (disp_broadcast_reg) begin
                // BROADCAST: All enabled tiles
                tile_wr_en_comb = disp_col_en_reg;
            end else begin
                // DISTRIBUTE: One-hot for specific tile
                tile_wr_en_comb = 24'h000001 << write_tile_idx_pipe;
            end
        end
    end

    assign o_tile_wr_en = tile_wr_en_comb;

    // ===================================================================
    // DISPATCH Read Outputs (from dispatcher_bram)
    // ===================================================================
    // Read enable based on side selection
    assign o_disp_man_left_rd_en  = read_active && !disp_right_reg;
    assign o_disp_man_right_rd_en = read_active && disp_right_reg;
    assign o_disp_exp_left_rd_en  = read_active && !disp_right_reg;
    assign o_disp_exp_right_rd_en = read_active && disp_right_reg;

    // Read addresses (same for all)
    assign o_disp_man_left_rd_addr  = read_src_addr;
    assign o_disp_man_right_rd_addr = read_src_addr;
    assign o_disp_exp_left_rd_addr  = read_src_addr;
    assign o_disp_exp_right_rd_addr = read_src_addr;

    // ===================================================================
    // DISPATCH Write Outputs (to tile_bram)
    // ===================================================================
    // Write enable based on side selection
    assign o_tile_man_left_wr_en  = write_valid_pipe && !disp_right_reg;
    assign o_tile_man_right_wr_en = write_valid_pipe && disp_right_reg;
    assign o_tile_exp_left_wr_en  = write_valid_pipe && !disp_right_reg;
    assign o_tile_exp_right_wr_en = write_valid_pipe && disp_right_reg;

    // Write addresses (same for all)
    assign o_tile_man_left_wr_addr  = write_dst_addr_pipe;
    assign o_tile_man_right_wr_addr = write_dst_addr_pipe;
    assign o_tile_exp_left_wr_addr  = write_dst_addr_pipe;
    assign o_tile_exp_right_wr_addr = write_dst_addr_pipe;

    // Write data (pass through from dispatcher_bram reads)
    assign o_tile_man_left_wr_data  = i_disp_man_left_rd_data;
    assign o_tile_man_right_wr_data = i_disp_man_right_rd_data;
    assign o_tile_exp_left_wr_data  = i_disp_exp_left_rd_data;
    assign o_tile_exp_right_wr_data = i_disp_exp_right_rd_data;

    // ===================================================================
    // Status Outputs
    // ===================================================================
    assign o_fetch_done = (state_reg == ST_FETCH_DONE);
    assign o_disp_done = (state_reg == ST_DISP_DONE);

    // ===================================================================
    // FETCH Implementation (simplified placeholder)
    // ===================================================================
    // The actual FETCH logic would go here
    // For now, just stub out the outputs
    assign o_man_left_wr_addr = '0;
    assign o_man_left_wr_data = '0;
    assign o_man_left_wr_en = '0;
    assign o_man_right_wr_addr = '0;
    assign o_man_right_wr_data = '0;
    assign o_man_right_wr_en = '0;
    assign o_exp_left_wr_addr = '0;
    assign o_exp_left_wr_data = '0;
    assign o_exp_left_wr_en = '0;
    assign o_exp_right_wr_addr = '0;
    assign o_exp_right_wr_data = '0;
    assign o_exp_right_wr_en = '0;
    assign o_axi_arvalid = '0;
    assign o_axi_araddr = '0;
    assign o_axi_arlen = '0;
    assign i_axi_rready = '0;

endmodule