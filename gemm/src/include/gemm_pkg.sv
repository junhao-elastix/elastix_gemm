// Macro for ceiling division
`ifndef CEIL_DIV
`define CEIL_DIV(a, b) (((a) + (b) - 1) / (b))
`endif

package gemm_pkg;
// Simple package for GEMM module definitions
    
    // Command and link parameters (compatible with Achronix NAP)
    localparam int cmd_op_width_gp = 8;
    localparam int cmd_id_width_gp = 8;
    localparam int link_addr_width_gp = 26;  // Line address (256-bit lines)
    localparam int link_len_width_gp = 16;   // Number of lines
    
    // Command buffer parameters for cmd_fifo
    localparam int cmd_buf_width_gp = 32;    // 32-bit command words
    localparam int cmd_buf_els_gp = 64;      // 64 entries in command FIFO
    
    // FP16 format
    parameter int FP16_WIDTH = 16;
    parameter int FP16_MANTISSA_WIDTH = 10;
    parameter int FP16_EXPONENT_WIDTH = 5;
    parameter int FP16_BIAS = 15;
    
    // Native vector width (number of GFP8 pairs)
    parameter int NV_WIDTH = 128;
    
    // Group size for group dot product
    parameter int GROUP_SIZE = 32;

    // GFP8E5 number format parameters (GFP8 with 5-bit exponent)
    parameter int GFP8E5_MANTISSA_WIDTH = 8;
    parameter int GFP8E5_EXPONENT_WIDTH = 5; // pad to 8 bits for alignment {3'b000, 5'b<exponent>}
    parameter int GFP8E5_BIAS = 15;

    // GFP8E8 number format parameters (GFP8 with 8-bit exponent)
    parameter int GFP8E8_MANTISSA_WIDTH = 8;
    parameter int GFP8E8_EXPONENT_WIDTH = 8;
    parameter int GFP8E8_BIAS = 127;

    // ACCUMULATOR width
    parameter int ACCUM_MAN_WIDTH = 64;
    parameter int ACCUM_EXP_WIDTH = 5;
    parameter int ACCUM_BIAS = 15;
    
    // BRAM parameters
    parameter int BRAM_DEPTH = 512;
    parameter int BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH);
    parameter int BRAM_DATA_WIDTH = 256;
    
    // master controller command structures
    typedef enum logic [cmd_op_width_gp-1:0] {
        e_cmd_op_fetch     = 8'hF0,  // Fetch one MEMBlk
        e_cmd_op_disp      = 8'hF1,  // Dispatch to RowBram and MLPBram
        e_cmd_op_matmul    = 8'hF2,  // Compute Matrix-Multiplication 
        e_cmd_op_wait_disp = 8'hF3,  // Wait for Dispatch Command to complete
        e_cmd_op_wait_matmul = 8'hF4,  // Wait for Matmul Command to complete
        e_cmd_op_readout   = 8'hF5   // Readout results
    } cmd_op_s;

    typedef struct packed {
        logic [15:0]                    reserved;
        logic [cmd_id_width_gp-1:0]     cmd_id;
        cmd_op_s                        op;
    } cmd_header_s;

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
        logic [7:0]   left_ugd_len;   // Word2[23:16]: Left UGD vectors
        logic [7:0]   right_ugd_len;  // Word2[15:8]: Right UGD vectors
        logic [7:0]   vec_len;        // Word2[7:0]: UGD vector size
        logic [15:0]  left_addr;      // Word1[31:16]: Left start address
        logic [15:0]  right_addr;     // Word1[15:0]: Right start address
    } cmd_matmul_s;

    typedef struct packed {
        logic [23:0]                reserved;
        logic [cmd_id_width_gp-1:0] wait_id;
    } cmd_wait_disp_s;

    typedef struct packed {
        logic [23:0]                reserved;
        logic [cmd_id_width_gp-1:0] wait_id;
    } cmd_wait_matmul_s;

    // VECTOR_READOUT command structure (0xF5)
    // Aligned with SINGLE_ROW_REFERENCE.md (lines 935-995)
    typedef struct packed {
        logic [31:0] rd_len;        // Word2[31:0]: Number of FP16 results to read (total across all tiles)
        logic [23:0] reserved;      // Word1[31:8]
        logic [7:0]  start_col;     // Word1[7:0]: Starting tile index (0-23)
    } cmd_readout_s;

    localparam cmd_header_len_gp = $bits(cmd_header_s) / 8;
    localparam cmd_fetch_len_gp  = $bits(cmd_fetch_s) / 8;
    localparam cmd_disp_len_gp   = $bits(cmd_disp_s) / 8;
    localparam cmd_matmul_len_gp = $bits(cmd_matmul_s) / 8;
    localparam cmd_wait_disp_len_gp = $bits(cmd_wait_disp_s) / 8;
    localparam cmd_wait_matmul_len_gp = $bits(cmd_wait_matmul_s) / 8;
    localparam cmd_readout_len_gp = $bits(cmd_readout_s) / 8;

    // TODO: calculate dynamically based on supported commands
    localparam cmd_max_width_gp = $bits(cmd_header_s) + $bits(cmd_matmul_s);

endpackage