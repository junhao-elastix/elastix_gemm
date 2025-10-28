// ------------------------------------------------------------------
// Dispatcher BRAM Module with 3-Buffer-Per-Side Architecture
//
// Purpose: Implement parallel exponent unpacking with separate buffers
// Architecture (as per 3-buffer refactoring plan):
//  - SIX buffers total (3 per side):
//    LEFT:  exp_packed (256x16), exp_aligned (8x512), man (256x512)
//    RIGHT: exp_packed (256x16), exp_aligned (8x512), man (256x512)
//
// FETCH Operation Flow:
//  1. Lines 0-15:   Write to exp_packed buffer (256-bit staging)
//  2. Lines 16-527: Write to man buffer (256-bit mantissas, stored at [0-511])
//  3. During step 2: Unpack exp_packed → exp_aligned (done by dispatcher_control)
//
// Four Output Ports (to compute engine):
//  1. left_exp (8-bit) - From exp_left_aligned
//  2. left_man (256-bit) - From man_left
//  3. right_exp (8-bit) - From exp_right_aligned
//  4. right_man (256-bit) - From man_right
//
// Write Interface (from dispatcher_control):
//  - i_wr_target: 0=left, 1=right
//  - Address [0-15]:   Write to exp_packed
//  - Address [16-527]: Write to man (stored at [addr-16])
//  - Exponents: Written separately via dedicated exp_aligned write ports
//
// Reference: Speedster7t Component Library UG086, BRAM_SDP chapter p.248
//
// Author: 3-buffer architecture implementation
// Date: October 13, 2025
// ------------------------------------------------------------------

module dispatcher_bram_dual_read #(
    parameter DATA_WIDTH = 256,       // 256-bit data width
    parameter EXP_PACKED_DEPTH = 16,  // 16 lines for packed exponents
    parameter EXP_ALIGNED_DEPTH = 512, // 512 exponents (aligned with groups)
    parameter MANTISSA_DEPTH = 2048,  // 2048 lines for mantissas (expanded for multi-tile addressing)
    parameter ADDR_WIDTH = 11         // 11-bit address for writes (covers 0-527)
)
(
    input  wire                     i_clk,
    
    // ===================================================================
    // WRITE PORTS (from dispatcher_control)
    // ===================================================================
    
    // Main write port for exp_packed and mantissas
    input  wire [DATA_WIDTH-1:0]    i_wr_data,
    input  wire [ADDR_WIDTH-1:0]    i_wr_addr,      // [0-15]: exp_packed, [16-527]: man
    input  wire                     i_wr_en,
    input  wire                     i_wr_target,    // 0=left, 1=right
    
    // Exponent aligned write ports (from unpacking logic in dispatcher_control)
    input  wire [8:0]               i_left_exp_aligned_wr_addr,
    input  wire [7:0]               i_left_exp_aligned_wr_data,
    input  wire                     i_left_exp_aligned_wr_en,
    
    input  wire [8:0]               i_right_exp_aligned_wr_addr,
    input  wire [7:0]               i_right_exp_aligned_wr_data,
    input  wire                     i_right_exp_aligned_wr_en,
    
    // ===================================================================
    // READ PORTS (to compute engine)
    // ===================================================================
    
    // Left matrix read ports
    input  wire [10:0]              i_rd_addr_left,      // Address [0-2047] - expanded for multi-tile
    input  wire                     i_rd_en_left,
    output wire [DATA_WIDTH-1:0]    o_rd_data_left,      // Mantissa
    
    input  wire [8:0]               i_left_exp_rd_addr,  // Address [0-511] - exponent still 9-bit
    output wire [7:0]               o_left_exp_rd_data,  // Exponent
    
    // Right matrix read ports
    input  wire [10:0]              i_rd_addr_right,     // Address [0-2047] - expanded for multi-tile
    input  wire                     i_rd_en_right,
    output wire [DATA_WIDTH-1:0]    o_rd_data_right,     // Mantissa
    
    input  wire [8:0]               i_right_exp_rd_addr, // Address [0-511] - exponent still 9-bit
    output wire [7:0]               o_right_exp_rd_data, // Exponent
    
    // ===================================================================
    // UNPACKING INTERFACE (for dispatcher_control to read exp_packed)
    // ===================================================================
    input  wire [3:0]               i_exp_packed_rd_addr, // Address [0-15]
    input  wire                     i_exp_packed_rd_target, // 0=left, 1=right
    output wire [DATA_WIDTH-1:0]    o_exp_packed_rd_data
);

    // ===================================================================
    // LEFT SIDE BUFFERS
    // ===================================================================
    
    // Buffer 1: Packed exponents (staging buffer)
    logic [DATA_WIDTH-1:0] exp_left_packed [0:EXP_PACKED_DEPTH-1];
    
    // Buffer 2: Aligned exponents (unpacked, one per group)
    logic [7:0] exp_left_aligned [0:EXP_ALIGNED_DEPTH-1];
    
    // Buffer 3: Mantissas (one group per line)
    logic [DATA_WIDTH-1:0] man_left [0:MANTISSA_DEPTH-1];
    
    // ===================================================================
    // RIGHT SIDE BUFFERS
    // ===================================================================
    
    // Buffer 1: Packed exponents (staging buffer)
    logic [DATA_WIDTH-1:0] exp_right_packed [0:EXP_PACKED_DEPTH-1];
    
    // Buffer 2: Aligned exponents (unpacked, one per group)
    logic [7:0] exp_right_aligned [0:EXP_ALIGNED_DEPTH-1];
    
    // Buffer 3: Mantissas (one group per line)
    logic [DATA_WIDTH-1:0] man_right [0:MANTISSA_DEPTH-1];
    
    // ===================================================================
    // SIMULATION INITIALIZATION (prevent X-states)
    // ===================================================================
    `ifdef SIMULATION
    integer init_i;
    initial begin
        for (init_i = 0; init_i < EXP_PACKED_DEPTH; init_i = init_i + 1) begin
            exp_left_packed[init_i] = '0;
            exp_right_packed[init_i] = '0;
        end
        for (init_i = 0; init_i < EXP_ALIGNED_DEPTH; init_i = init_i + 1) begin
            exp_left_aligned[init_i] = '0;
            exp_right_aligned[init_i] = '0;
        end
        for (init_i = 0; init_i < MANTISSA_DEPTH; init_i = init_i + 1) begin
            man_left[init_i] = '0;
            man_right[init_i] = '0;
        end
    end
    `endif
    
    // ===================================================================
    // WRITE LOGIC
    // ===================================================================
    
    always_ff @(posedge i_clk) begin
        if (i_wr_en) begin
            // Address [0-15]: Write to exp_packed
            if (i_wr_addr < 11'd16) begin
                if (i_wr_target == 1'b0) begin
                    exp_left_packed[i_wr_addr[3:0]] <= i_wr_data;
                    `ifdef SIMULATION
                    if (i_wr_addr == 11'd0) begin
                        $display("[BRAM_WR] @%0t LEFT exp_packed[0] <= 0x%064x (first 8 bytes: %02x %02x %02x %02x %02x %02x %02x %02x)",
                                 $time, i_wr_data,
                                 i_wr_data[7:0], i_wr_data[15:8], i_wr_data[23:16], i_wr_data[31:24],
                                 i_wr_data[39:32], i_wr_data[47:40], i_wr_data[55:48], i_wr_data[63:56]);
                    end
                    `endif
                end else begin
                    exp_right_packed[i_wr_addr[3:0]] <= i_wr_data;
                    `ifdef SIMULATION
                    if (i_wr_addr == 11'd0) begin
                        $display("[BRAM_WR] @%0t RIGHT exp_packed[0] <= 0x%064x (first 8 bytes: %02x %02x %02x %02x %02x %02x %02x %02x)",
                                 $time, i_wr_data,
                                 i_wr_data[7:0], i_wr_data[15:8], i_wr_data[23:16], i_wr_data[31:24],
                                 i_wr_data[39:32], i_wr_data[47:40], i_wr_data[55:48], i_wr_data[63:56]);
                    end
                    `endif
                end
            end
            // Address [16-527]: Write to mantissa buffer (stored at [addr-16])
            else if (i_wr_addr >= 11'd16 && i_wr_addr < 11'd528) begin
                if (i_wr_target == 1'b0) begin
                    man_left[i_wr_addr[8:0] - 9'd16] <= i_wr_data;
                    `ifdef SIMULATION
                    if (i_wr_addr == 11'd16) begin
                        $display("[BRAM_WR] @%0t LEFT man[0] <- 0x%064x (hex line 16, first 4 bytes: 0x%02x%02x%02x%02x)",
                                 $time, i_wr_data, i_wr_data[7:0], i_wr_data[15:8], i_wr_data[23:16], i_wr_data[31:24]);
                    end
                    `endif
                end else begin
                    man_right[i_wr_addr[8:0] - 9'd16] <= i_wr_data;
                end
            end
        end
    end
    
    // Exponent aligned write logic (from unpacking in dispatcher_control)
    always_ff @(posedge i_clk) begin
        if (i_left_exp_aligned_wr_en) begin
            exp_left_aligned[i_left_exp_aligned_wr_addr] <= i_left_exp_aligned_wr_data;
        end
        if (i_right_exp_aligned_wr_en) begin
            exp_right_aligned[i_right_exp_aligned_wr_addr] <= i_right_exp_aligned_wr_data;
        end
    end
    
    // ===================================================================
    // READ LOGIC - MANTISSAS
    // ===================================================================
    
    // Left mantissa read (registered)
    logic [DATA_WIDTH-1:0] rd_data_left_reg;
    always_ff @(posedge i_clk) begin
        if (i_rd_en_left) begin
            rd_data_left_reg <= man_left[i_rd_addr_left];
        end
    end
    assign o_rd_data_left = rd_data_left_reg;
    
    // Right mantissa read (registered)
    logic [DATA_WIDTH-1:0] rd_data_right_reg;
    always_ff @(posedge i_clk) begin
        if (i_rd_en_right) begin
            rd_data_right_reg <= man_right[i_rd_addr_right];
        end
    end
    assign o_rd_data_right = rd_data_right_reg;
    
    // ===================================================================
    // READ LOGIC - EXPONENTS (ALIGNED)
    // ===================================================================
    
    // Left exponent read (registered)
    logic [7:0] left_exp_rd_data_reg;
    always_ff @(posedge i_clk) begin
        left_exp_rd_data_reg <= exp_left_aligned[i_left_exp_rd_addr];
    end
    assign o_left_exp_rd_data = left_exp_rd_data_reg;
    
    // Right exponent read (registered)
    logic [7:0] right_exp_rd_data_reg;
    always_ff @(posedge i_clk) begin
        right_exp_rd_data_reg <= exp_right_aligned[i_right_exp_rd_addr];
    end
    assign o_right_exp_rd_data = right_exp_rd_data_reg;
    
    // ===================================================================
    // READ LOGIC - PACKED EXPONENTS (for unpacking)
    // ===================================================================
    
    // Read packed exponents (COMBINATIONAL to avoid stale data between FETCHes)
    // Using combinational read eliminates the problem of stale data from previous FETCH
    logic [DATA_WIDTH-1:0] exp_packed_rd_data_comb;
    always_comb begin
        if (i_exp_packed_rd_target == 1'b0) begin
            exp_packed_rd_data_comb = exp_left_packed[i_exp_packed_rd_addr];
        end else begin
            exp_packed_rd_data_comb = exp_right_packed[i_exp_packed_rd_addr];
        end
    end
    assign o_exp_packed_rd_data = exp_packed_rd_data_comb;
    
    `ifdef SIMULATION
    // Debug: Show combinational read
    always @(*) begin
        if (i_exp_packed_rd_addr == 0 && i_exp_packed_rd_target == 1) begin
            $display("[BRAM_RD_COMB] @%0t i_exp_packed_rd_target=%0d, addr=%0d: reading first 4 bytes=%02x %02x %02x %02x (combinational)",
                     $time, i_exp_packed_rd_target, i_exp_packed_rd_addr,
                     exp_packed_rd_data_comb[7:0], exp_packed_rd_data_comb[15:8],
                     exp_packed_rd_data_comb[23:16], exp_packed_rd_data_comb[31:24]);
        end
    end
    `endif

endmodule

