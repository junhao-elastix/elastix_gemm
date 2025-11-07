// ------------------------------------------------------------------
// Tile BRAM Module with Native Vector Packing
//
// Purpose: L1 memory layer with automatic NV packing for single-cycle reads
// Architecture:
//  - Storage: 128 Native Vectors (NVs) per side
//  - Each NV contains:
//    - 4 mantissa groups (256-bit each)
//    - 1 packed exponent (32-bit with 4 bytes)
//
// Write Interface:
//  - Line-based writes (same as before) with automatic NV packing
//  - FOUR PARALLEL WRITE PORTS - All can write in same cycle
//  - Writes are automatically packed into NV format internally
//
// Read Interface:
//  - NEW: Native Vector interface for single-cycle NV reads
//  - Combinational (0-latency) access to complete NVs
//  - Old line-based interface REMOVED
//
// Author: Junhao Pan
// Date: 10/31/2024
// ------------------------------------------------------------------

module tile_bram #(
    parameter MAN_WIDTH = 256,          // Mantissa line width
    parameter EXP_WIDTH = 8,            // Exponent width
    parameter BRAM_DEPTH = 512,
    parameter ADDR_WIDTH = $clog2(BRAM_DEPTH)
)
(
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // ====================================================================
    // Write Ports 
    // FOUR PARALLEL WRITE PORTS - All can write in same cycle
    // ====================================================================
    // Left mantissa write port
    input  logic [ADDR_WIDTH-1:0]       i_man_left_wr_addr,
    input  logic                        i_man_left_wr_en,
    input  logic [MAN_WIDTH-1:0]        i_man_left_wr_data,

    // Right mantissa write port
    input  logic [ADDR_WIDTH-1:0]       i_man_right_wr_addr,
    input  logic                        i_man_right_wr_en,
    input  logic [MAN_WIDTH-1:0]        i_man_right_wr_data,

    // Left exponent write port
    input  logic [ADDR_WIDTH-1:0]       i_exp_left_wr_addr,
    input  logic                        i_exp_left_wr_en,
    input  logic [EXP_WIDTH-1:0]        i_exp_left_wr_data,

    // Right exponent write port
    input  logic [ADDR_WIDTH-1:0]       i_exp_right_wr_addr,
    input  logic                        i_exp_right_wr_en,
    input  logic [EXP_WIDTH-1:0]        i_exp_right_wr_data,

    // ====================================================================
    // Native Vector Read Interface (NEW)
    // Combinational reads - complete NV in single cycle
    // ====================================================================
    // Left NV read
    input  logic [6:0]                  i_nv_left_rd_idx,
    output logic [31:0]                 o_nv_left_exp,         // Packed exponents
    output logic [MAN_WIDTH-1:0]        o_nv_left_man [0:3],   // 4 mantissa groups

    // Right NV read
    input  logic [6:0]                  i_nv_right_rd_idx,
    output logic [31:0]                 o_nv_right_exp,        // Packed exponents
    output logic [MAN_WIDTH-1:0]        o_nv_right_man [0:3]   // 4 mantissa groups
);

    // ===================================================================
    // NV-PACKED STORAGE (128 Native Vectors per side)
    // ===================================================================
    // Left side: 128 Native Vectors
    (* ram_style = "block" *) logic [MAN_WIDTH-1:0] nv_man_left [0:127][0:3];
    (* ram_style = "block" *) logic [31:0]          nv_exp_left [0:127];       // 128 NVs × packed exp
    
    // Right side: 128 Native Vectors  
    (* ram_style = "block" *) logic [MAN_WIDTH-1:0] nv_man_right [0:127][0:3];
    (* ram_style = "block" *) logic [31:0]          nv_exp_right [0:127];      // 128 NVs × packed exp

    // ===================================================================
    // SIMULATION NOTE: Memory initialization via DISPATCH operation
    // ===================================================================
    // No initial block needed - testbench writes data via tile_bram write ports
    // (simulating DISPATCH operation)

    // ===================================================================
    // WRITE LOGIC - Pack line-based writes into NV format
    // ===================================================================
    // Left mantissa write - pack into NV format
    always_ff @(posedge i_clk) begin
        if (i_man_left_wr_en) begin
            // Calculate NV index and group within NV
            automatic logic [6:0] nv_idx = i_man_left_wr_addr[8:2];    // NV index (addr/4)
            automatic logic [1:0] group_idx = i_man_left_wr_addr[1:0]; // Group within NV [0-3]
            
            // Write mantissa to correct group slot in NV
            nv_man_left[nv_idx][group_idx] <= i_man_left_wr_data;
            
            // `ifdef SIMULATION
            // $display("[TILE_WR] @%0t nv_man_left[%0d][%0d] = 0x%064x (line_addr=%0d)",
            //          $time, nv_idx, group_idx, i_man_left_wr_data, i_man_left_wr_addr);
            // `endif
        end
    end

    // Right mantissa write - pack into NV format
    always_ff @(posedge i_clk) begin
        if (i_man_right_wr_en) begin
            automatic logic [6:0] nv_idx = i_man_right_wr_addr[8:2];
            automatic logic [1:0] group_idx = i_man_right_wr_addr[1:0];
            
            nv_man_right[nv_idx][group_idx] <= i_man_right_wr_data;
            
            // `ifdef SIMULATION
            // $display("[TILE_WR] @%0t nv_man_right[%0d][%0d] = 0x%064x (line_addr=%0d)",
            //          $time, nv_idx, group_idx, i_man_right_wr_data, i_man_right_wr_addr);
            // `endif
        end
    end

    // ===================================================================
    // WRITE LOGIC - EXPONENTS (packed into 32-bit words)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (i_exp_left_wr_en) begin
            automatic logic [6:0] nv_idx = i_exp_left_wr_addr[8:2];
            automatic logic [1:0] group_idx = i_exp_left_wr_addr[1:0];
            
            // Pack exponent into correct byte position in 32-bit word
            case (group_idx)
                2'd0: nv_exp_left[nv_idx][7:0]   <= i_exp_left_wr_data;
                2'd1: nv_exp_left[nv_idx][15:8]  <= i_exp_left_wr_data;
                2'd2: nv_exp_left[nv_idx][23:16] <= i_exp_left_wr_data;
                2'd3: nv_exp_left[nv_idx][31:24] <= i_exp_left_wr_data;
            endcase
            
            // `ifdef SIMULATION
            // $display("[TILE_WR] @%0t nv_exp_left[%0d][byte %0d] = 0x%02x",
            //          $time, nv_idx, group_idx, i_exp_left_wr_data);
            // `endif
        end
        
        if (i_exp_right_wr_en) begin
            automatic logic [6:0] nv_idx = i_exp_right_wr_addr[8:2];
            automatic logic [1:0] group_idx = i_exp_right_wr_addr[1:0];
            
            case (group_idx)
                2'd0: nv_exp_right[nv_idx][7:0]   <= i_exp_right_wr_data;
                2'd1: nv_exp_right[nv_idx][15:8]  <= i_exp_right_wr_data;
                2'd2: nv_exp_right[nv_idx][23:16] <= i_exp_right_wr_data;
                2'd3: nv_exp_right[nv_idx][31:24] <= i_exp_right_wr_data;
            endcase
            
            // `ifdef SIMULATION
            // $display("[TILE_WR] @%0t nv_exp_right[%0d][byte %0d] = 0x%02x",
            //          $time, nv_idx, group_idx, i_exp_right_wr_data);
            // `endif
        end
    end

    // ===================================================================
    // NV READ LOGIC - Combinational (0-latency)
    // ===================================================================
    // Left NV read - output complete Native Vector
    assign o_nv_left_exp = nv_exp_left[i_nv_left_rd_idx];
    assign o_nv_left_man = nv_man_left[i_nv_left_rd_idx];
    
    // Right NV read - output complete Native Vector
    assign o_nv_right_exp = nv_exp_right[i_nv_right_rd_idx];
    assign o_nv_right_man = nv_man_right[i_nv_right_rd_idx];
    
    // `ifdef SIMULATION
    // always @(i_nv_left_rd_idx or i_nv_right_rd_idx) begin
    //     $display("[TILE_NV_RD] @%0t Left NV[%0d]: exp=0x%08x", 
    //              $time, i_nv_left_rd_idx, o_nv_left_exp);
    //     $display("[TILE_NV_RD] @%0t Right NV[%0d]: exp=0x%08x", 
    //              $time, i_nv_right_rd_idx, o_nv_right_exp);
    // end
    // `endif

endmodule
