// ------------------------------------------------------------------
// Dispatcher BRAM Module
//
// Purpose: Dual-port BRAM for GFP8 block buffering using ACX_BRAM72K
// Features:
//  - 528 entries × 256-bit (GFP8 block: 16 exp lines + 512 mantissa lines)
//  - Port A: Write from DDR (dispatcher control)
//  - Port B: Read by compute engine
//  - Asymmetric width: Both 256-bit for simplicity
//  - Based on Achronix ACX_BRAM72K primitive
//
// Reference: Speedster7t Component Library UG086, BRAM_SDP chapter p.248
//
// Author: MS2.0 Migration
// Date: Thu Oct 2 00:23:05 AM PDT 2025
// ------------------------------------------------------------------

module dispatcher_bram #(
    parameter DATA_WIDTH = 256,     // 256-bit data width
    parameter DEPTH = 1056,         // GFP8 dual block size (2×528 = 1056 lines for left+right matrices)
    parameter ADDR_WIDTH = 11       // $clog2(1056) = 11 bits
)
(
    // Port A: Write port (from Dispatcher Control)
    input  wire                     i_wr_clk,
    input  wire [DATA_WIDTH-1:0]    i_wr_data,
    input  wire [ADDR_WIDTH-1:0]    i_wr_addr,
    input  wire                     i_wr_en,

    // Port B: Read port (to Compute Engine)
    input  wire                     i_rd_clk,
    input  wire [ADDR_WIDTH-1:0]    i_rd_addr,
    input  wire                     i_rd_en,
    output wire [DATA_WIDTH-1:0]    o_rd_data
);

    // ===================================================================
    // ACX_BRAM72K Configuration
    // ===================================================================
    // Each ACX_BRAM72K supports:
    //   - 65536 bits total capacity
    //   - Configurable asymmetric widths
    //   - For 256-bit width: 65536/256 = 256 addresses per BRAM
    //   - Need 528/256 = 3 BRAMs to cover 528 addresses
    //
    // Strategy: Use 3 BRAM72K instances cascaded
    // BRAM0: addresses 0-255
    // BRAM1: addresses 256-511
    // BRAM2: addresses 512-527

    // BRAM configuration: Each BRAM72K supports 256 addresses @ 256-bit width
    // DEPTH/256 = number of BRAMs needed (rounded up)
    localparam NUM_BRAMS = (DEPTH + 255) / 256;  // Auto-calculate based on DEPTH parameter
    localparam BRAM_ADDR_WIDTH = 8;              // 256 addresses per BRAM = 8 bits

    // ===================================================================
    // Address Decoding
    // ===================================================================
    // Select which BRAM based on upper address bits
    // BRAM_sel = address / 256, BRAM_addr = address % 256
    localparam BRAM_SEL_WIDTH = $clog2(NUM_BRAMS);  // Bits needed to select BRAM

    logic [BRAM_SEL_WIDTH-1:0] wr_bram_sel;  // Which BRAM to write
    logic [BRAM_SEL_WIDTH-1:0] rd_bram_sel;  // Which BRAM to read
    logic [BRAM_ADDR_WIDTH-1:0] wr_bram_addr;  // Address within BRAM
    logic [BRAM_ADDR_WIDTH-1:0] rd_bram_addr;  // Address within BRAM

    always_comb begin
        // Dynamic BRAM selection: divide address by 256
        wr_bram_sel = i_wr_addr[ADDR_WIDTH-1:BRAM_ADDR_WIDTH];
        wr_bram_addr = i_wr_addr[BRAM_ADDR_WIDTH-1:0];

        rd_bram_sel = i_rd_addr[ADDR_WIDTH-1:BRAM_ADDR_WIDTH];
        rd_bram_addr = i_rd_addr[BRAM_ADDR_WIDTH-1:0];
    end

    // ===================================================================
    // BRAM Write Enable Generation
    // ===================================================================
    logic [NUM_BRAMS-1:0] bram_wr_en;

    always_comb begin
        bram_wr_en = '0;
        if (i_wr_en) begin
            bram_wr_en[wr_bram_sel] = 1'b1;
        end
    end

    // ===================================================================
    // BRAM Read Enable Generation
    // ===================================================================
    logic [NUM_BRAMS-1:0] bram_rd_en;

    always_comb begin
        bram_rd_en = '0;
        if (i_rd_en) begin
            bram_rd_en[rd_bram_sel] = 1'b1;
        end
    end

    // ===================================================================
    // BRAM Instance Outputs
    // ===================================================================
    wire [DATA_WIDTH-1:0] bram_rd_data [0:NUM_BRAMS-1];

    // ===================================================================
    // For Simulation: Use Inferred BRAM (Synthesis will use ACX_BRAM72K)
    // ===================================================================
    `ifdef SIMULATION
        // Simple dual-port RAM model for simulation
        // Initialize to zeros to prevent X propagation
        (* ram_style = "block" *) logic [DATA_WIDTH-1:0] mem [0:DEPTH-1] = '{default: '0};

        // Debug: print DEPTH parameter value
        initial begin
            $display("[BRAM] Instantiated with DEPTH=%0d, ADDR_WIDTH=%0d", DEPTH, ADDR_WIDTH);
        end

        // Write port
        always_ff @(posedge i_wr_clk) begin
            if (i_wr_en) begin
                mem[i_wr_addr] <= i_wr_data;
                // Debug messages for key addresses
                if (i_wr_addr == 0 || i_wr_addr == 527 || i_wr_addr == 528 || i_wr_addr == 544 || i_wr_addr == 1055) begin
                    $display("[BRAM_WRITE] @%0t addr=%0d, data=0x%h", $time, i_wr_addr, i_wr_data);
                end
            end
        end

        // Read port with 1-cycle latency (registered output)
        logic [DATA_WIDTH-1:0] rd_data_reg = '0;  // Initialize to avoid X propagation
        always_ff @(posedge i_rd_clk) begin
            if (i_rd_en) begin
                rd_data_reg <= mem[i_rd_addr];
                // Debug specific addresses only to reduce output
                if (i_rd_addr == 0 || i_rd_addr == 528 || i_rd_addr == 544 ||
                    (i_rd_addr >= 16 && i_rd_addr <= 19)) begin
                    $display("[BRAM_READ] @%0t addr=%0d, mem_data=0x%h, output_next_cycle=0x%h",
                             $time, i_rd_addr, mem[i_rd_addr], mem[i_rd_addr]);
                end
            end
            // HOLD previous value when not reading (like real BRAM output register)
        end

        assign o_rd_data = rd_data_reg;

    `else
        // ===================================================================
        // ACX_BRAM72K Instantiation for FPGA Synthesis
        // ===================================================================
        // Note: ACX_BRAM72K supports up to 144-bit data width natively
        // For 256-bit, we need 2 BRAM72K per address set cascaded
        // This requires 6 total BRAM72K (3 address sets × 2 for width)
        //
        // Alternative: Use proper inference for synthesis tools to map automatically
        // The synthesis tools should map this to ACX_BRAM72K based on attributes

        // Synthesis attribute to force block RAM inference
        (* ram_style = "block" *) logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];

        // Write port
        always_ff @(posedge i_wr_clk) begin
            if (i_wr_en) begin
                mem[i_wr_addr] <= i_wr_data;
            end
        end

        // Read port with output register
        logic [DATA_WIDTH-1:0] rd_data_int;
        always_ff @(posedge i_rd_clk) begin
            if (i_rd_en) begin
                rd_data_int <= mem[i_rd_addr];
            end
        end

        assign o_rd_data = rd_data_int;

    `endif

endmodule : dispatcher_bram
