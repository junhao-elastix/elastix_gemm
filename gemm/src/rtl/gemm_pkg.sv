// Simple package for GEMM module definitions
package gemm_pkg;

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

endpackage















