// Macro for ceiling division
`ifndef CEIL_DIV
`define CEIL_DIV(a, b) (((a) + (b) - 1) / (b))
`endif

package gemm_pkg;
// Simple package for GEMM module definitions

    // GFP8 mantissa width (7 bits + 1 sign bit)
    parameter int GFP8_MANTISSA_WIDTH = 8;
    
    // GFP8 shared exponent width
    parameter int GFP8_EXPONENT_WIDTH = 8;
    
    // FP16 format
    parameter int FP16_WIDTH = 16;
    parameter int FP16_MANTISSA_WIDTH = 10;
    parameter int FP16_EXPONENT_WIDTH = 5;
    parameter int FP16_BIAS = 15;
    
    // Native vector width (number of GFP8 pairs)
    parameter int NV_WIDTH = 128;
    
    // Group size for group dot product
    parameter int GROUP_SIZE = 32;
    
    // BRAM parameters
    parameter int BRAM_ADDR_WIDTH = 9;
    parameter int BRAM_DATA_WIDTH = 256;
    
    // Tile dimensions
    parameter int MAX_TILE_DIM = 256;

    // tensor block parameters
    localparam block_size_gp = 128;

    // master controller parameters
    localparam cmd_op_width_gp = 8;
    localparam cmd_id_width_gp = 8;
    localparam cmd_len_width_gp = 8;
    localparam cmd_flags_width_gp = 8;

    localparam cmd_buf_width_gp = 32;
    localparam cmd_buf_els_gp = 1024;  // Command FIFO depth (user configurable)

    // AXI parameters
    localparam axi_addr_width_gp = 64;
    localparam axi_data_width_gp = 256;
    localparam axi_id_width_gp = 7;
    localparam axi_resp_width_gp = 2;
    localparam axi_len_width_gp = 8;
    localparam axi_size_width_gp = 3;
    localparam axi_burst_width_gp = 2;

    // AXI link parameters
    localparam link_num_axi_gp = 4;
    localparam link_axi_offset_gp = 32'h2000_0000;
    localparam link_addr_width_gp = 32;
    localparam link_len_width_gp = 16;
    localparam link_data_width_gp = 4 * axi_data_width_gp;

    // GEMM tile parameters
    localparam tile_num_dots_gp = 128;
    localparam tile_num_groups_gp = 4;

    // Tile dimension widths (for dim_b, dim_c, dim_v)
    localparam tile_b_width_gp = 8;  // Batch dimension width
    localparam tile_c_width_gp = 8;  // Column dimension width
    localparam tile_v_width_gp = 8;  // Vector count width

    localparam tile_left_bias_gp = 15;
    localparam tile_right_bias_gp = 15;
    localparam tile_out_bias_gp = 15;

    localparam tile_out_fifo_els_gp = 4096;  // Result FIFO depth (increased for large tests, was 64)
    localparam tile_out_cnt_width_gp = $clog2(tile_out_fifo_els_gp+1);

    localparam tile_max_mwidth_gp = 8;
    localparam tile_max_ewidth_gp = 5;
    localparam tile_min_mwidth_gp = 4;
    localparam tile_min_ewidth_gp = 5;

    localparam tile_out_mwidth_gp = 11;
    localparam tile_out_ewidth_gp = 5;

    localparam tile_op_mwidth_gp = `CEIL_DIV(tile_max_mwidth_gp, 8) * 8;
    localparam tile_op_ewidth_gp = `CEIL_DIV(tile_max_ewidth_gp, 8) * 8;

    localparam tile_unit_mwidth_gp = (1 << $clog2(tile_min_mwidth_gp));
    localparam tile_unit_ewidth_gp = (1 << $clog2(tile_min_ewidth_gp));

    localparam tile_msel_width_gp = (tile_op_mwidth_gp == tile_unit_mwidth_gp) ? 1 : $clog2(tile_op_mwidth_gp/tile_unit_mwidth_gp);
    localparam tile_esel_width_gp = (tile_op_ewidth_gp == tile_unit_ewidth_gp) ? 1 : $clog2(tile_op_ewidth_gp/tile_unit_ewidth_gp);

    localparam tile_msize_width_gp = $clog2(tile_msel_width_gp+1);
    localparam tile_esize_width_gp = $clog2(tile_esel_width_gp+1);

    // master controller command structures
    // Aligned with MS2.0 uCode specification (MS2.0 uCode - Single Tile.csv)
    typedef enum logic [cmd_op_width_gp-1:0] {
        e_cmd_op_fetch     = 8'hF0,  // fetch_memory_block (CSV line 3)
        e_cmd_op_disp      = 8'hF1,  // vector_dispatch (CSV line 6)
        e_cmd_op_tile      = 8'hF2,  // matmul (CSV line 11) - FIXED from 0xF3
        e_cmd_op_wait_disp = 8'hF3,  // wait_dispatch (CSV line 21) - FIXED from 0xF4
        e_cmd_op_wait_tile = 8'hF4   // wait_matmul (CSV line 22) - FIXED from 0xF5
    } cmd_op_s;

    typedef struct packed {
        logic [7:0]                  reserved;
        logic [cmd_len_width_gp-1:0] len;
        logic [cmd_id_width_gp-1:0]  id;
        cmd_op_s                     op;
    } cmd_header_s;

    typedef struct packed {
        logic [cmd_flags_width_gp-4:0] reserved;
        logic       main_loop_over_left;
        logic       right_man_4b;
        logic       left_man_4b;
    } cmd_flags_s;

    typedef struct packed {
        logic [30:0]                   reserved;    // Word3[31:1]
        logic                          fetch_right; // Word3[0]: 0=left, 1=right
        logic [15:0]                   reserved2;   // Word2[31:16]
        logic [link_len_width_gp-1:0]  len;        // Word2[15:0]
        logic [link_addr_width_gp-1:0] start_addr; // Word1[31:0]
    } cmd_fetch_s;

    typedef struct packed {
        logic [23:0]  col_en;         // Word3[31:8]: Column enable mask (24 tiles max)
        logic [4:0]   col_start;      // Word3[7:3]: Distribution start column
        logic         disp_right;     // Word3[2]: Dispatch side (0=left, 1=right)
        logic         broadcast;      // Word3[1]: Distribution mode (0=distribute, 1=broadcast)
        logic         man_4b;         // Word3[0]: Mantissa width (0=8-bit, 1=4-bit)
        logic [15:0]  reserved2;      // Word2[31:16]
        logic [15:0]  tile_addr;      // Word2[15:0]: Tile destination address
        logic [7:0]   reserved3;      // Word1[31:24]
        logic [7:0]   man_nv_cnt;     // Word1[23:16]: Total NVs to dispatch
        logic [7:0]   reserved4;      // Word1[15:8]
        logic [7:0]   ugd_vec_size;   // Word1[7:0]: NVs per UGD vector
    } cmd_disp_s;

    typedef struct packed{
        logic [23:0]  col_en;         // Word3[31:8]: Column enable mask (24 tiles max)
        logic [4:0]   reserved;       // Word3[7:3]
        logic         left_4b;        // Word3[2]: Left mantissa width (0=8-bit, 1=4-bit)
        logic         right_4b;       // Word3[1]: Right mantissa width (0=8-bit, 1=4-bit)
        logic         main_loop_left; // Word3[0]: Main loop dimension (0=right first, 1=left first)
        logic [7:0]   reserved2;      // Word2[31:24]
        logic [7:0]   left_ugd_len;   // Word2[23:16]: Left UGD vectors (also dim_b)
        logic [7:0]   right_ugd_len;  // Word2[15:8]: Right UGD vectors (also dim_c)
        logic [7:0]   vec_len;        // Word2[7:0]: UGD vector size (also dim_v)
        logic [15:0]  left_addr;      // Word1[31:16]: Left start address
        logic [15:0]  right_addr;     // Word1[15:0]: Right start address
    } cmd_tile_s;

    typedef struct packed {
        logic [23:0]                reserved;
        logic [cmd_id_width_gp-1:0] wait_id;
    } cmd_wait_disp_s;

    typedef struct packed {
        logic [23:0]                reserved;
        logic [cmd_id_width_gp-1:0] wait_id;
    } cmd_wait_tile_s;

    localparam cmd_header_len_gp = $bits(cmd_header_s) / 8;
    localparam cmd_fetch_len_gp  = $bits(cmd_fetch_s) / 8;
    localparam cmd_disp_len_gp   = $bits(cmd_disp_s) / 8;
    localparam cmd_tile_len_gp   = $bits(cmd_tile_s) / 8;
    localparam cmd_wait_disp_len_gp = $bits(cmd_wait_disp_s) / 8;
    localparam cmd_wait_tile_len_gp = $bits(cmd_wait_tile_s) / 8;

    // TODO: calculate dynamically based on supported commands
    localparam cmd_max_width_gp = $bits(cmd_header_s) + $bits(cmd_tile_s);

endpackage