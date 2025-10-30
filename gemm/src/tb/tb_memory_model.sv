// ------------------------------------------------------------------
// Testbench Memory Model (DDR Emulation)
//
// Purpose: Emulates DDR memory with GFP8 block structure for testing
// Features:
//  - Two 128x128 GFP8 blocks (left/activation and right/weight)
//  - GFP8 format: 8-bit mantissa + shared 8-bit exponent per 32-element group
//  - Memory layout: 528 lines x 256-bit per block
//    * Lines 0-15:   Exponents (512 total, 32 per line)
//    * Lines 16-527: Mantissas (512 lines, 32 mantissas per line)
//  - AXI4 slave interface with burst read support
//  - Configurable memory initialization
//
// Author: MS2.0 Migration
// Date: Thu Oct 2 00:14:43 AM PDT 2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module tb_memory_model
#(
    parameter DATA_WIDTH = 256,        // 256-bit AXI data width
    parameter ADDR_WIDTH = 42,         // AXI address width (42-bit for GDDR6 NoC: {Page[9], Line[26], Pad[2], Byte[5]})
    parameter LINES_PER_BLOCK = 528,   // GFP8 block size
    parameter NUM_BLOCKS = 2,          // Left and right blocks
    parameter LATENCY_CYCLES = 0       // PERFECT TEST: 0 latency to measure pure fetcher overhead
)
(
    input  logic        i_clk,
    input  logic        i_reset_n,

    // AXI4 Slave Interface
    t_AXI4.responder    axi_mem_if,

    // Debug
    output logic [31:0] o_read_count,
    output logic [31:0] o_last_addr
);

    // ===================================================================
    // Memory Array
    // ===================================================================
    // Total memory: NUM_BLOCKS x LINES_PER_BLOCK x 256-bit
    logic [DATA_WIDTH-1:0] mem_array [0:NUM_BLOCKS*LINES_PER_BLOCK-1];

    // AXI State Machine - PERFECT: arready same cycle, zero latency
    typedef enum logic [2:0] {
        AXI_IDLE    = 3'b000,
        AXI_RDATA   = 3'b011  // Skip ARREADY and LATENCY states for perfect response
    } axi_state_t;

    axi_state_t axi_state_reg, axi_state_next;

    // Latency modeling - use cycle counter instead of time
    integer latency_counter_reg;

    // ===================================================================
    // AXI Transaction Registers
    // ===================================================================
    logic [ADDR_WIDTH-1:0] ar_addr_reg;
    logic [7:0]            ar_id_reg;
    logic [7:0]            ar_len_reg;      // Burst length (0-15 for 1-16 beats)
    logic [2:0]            ar_size_reg;     // Transfer size
    logic [1:0]            ar_burst_reg;    // Burst type

    logic [7:0]            beat_count_reg;  // Current beat in burst
    logic [DATA_WIDTH-1:0] read_data_reg;
    logic                  read_valid_reg;
    logic                  read_last_reg;

    // Debug counters
    logic [31:0] read_count_reg;
    logic [31:0] last_addr_reg;

    // ===================================================================
    // Memory Initialization - Load from Hex Files
    // ===================================================================
    initial begin
        integer fd_left, fd_right;
        string line_str;
        integer line_idx, byte_idx;
        logic [7:0] byte_val;
        integer scan_result;

        $display("[TB_MEM_MODEL] Loading memory from hex files...");
        $display("[TB_MEM_MODEL] ===============================================");
        $display("[TB_MEM_MODEL] ** PERFECT ZERO-LATENCY MODE **");
        $display("[TB_MEM_MODEL] - arready: SAME cycle as arvalid");
        $display("[TB_MEM_MODEL] - First rvalid: NEXT cycle after AR");
        $display("[TB_MEM_MODEL] - rvalid: CONTINUOUS (no gaps)");
        $display("[TB_MEM_MODEL] - This measures PURE fetcher state machine overhead");
        $display("[TB_MEM_MODEL] ===============================================");

        // Initialize all memory to zero first
        for (int i = 0; i < NUM_BLOCKS*LINES_PER_BLOCK; i = i + 1) begin
            mem_array[i] = '0;
        end

        // Load Block 0: Left matrix (528 lines) from /home/workstation/elastix_gemm/hex/left.hex
        fd_left = $fopen("/home/workstation/elastix_gemm/hex/left.hex", "r");
        if (fd_left == 0) begin
            $display("[TB_MEM_MODEL] ERROR: Could not open /home/workstation/elastix_gemm/hex/left.hex");
            $display("[TB_MEM_MODEL] Using zero-initialized memory for left matrix");
        end else begin
            line_idx = 0;
            while (!$feof(fd_left) && line_idx < 528) begin
                if ($fgets(line_str, fd_left)) begin
                    // Parse hex line: expects 32 hex bytes separated by spaces
                    // Use a simpler approach - parse all values in one go
                    automatic logic [7:0] hex_bytes[0:31];
                    scan_result = $sscanf(line_str,
                        "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                        hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                        hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                        hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                        hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                        hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                        hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                        hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                        hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);

                    if (scan_result == 32) begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx = byte_idx + 1) begin
                            mem_array[line_idx][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                    line_idx = line_idx + 1;
                end
            end
            $fclose(fd_left);
            $display("[TB_MEM_MODEL] Loaded %0d lines from left.hex (Block 0)", line_idx);
        end

        // Load Block 1: Right matrix (528 lines) from /home/workstation/elastix_gemm/hex/right.hex
        // Right matrix starts at line offset 528 (LINES_PER_BLOCK)
        fd_right = $fopen("/home/workstation/elastix_gemm/hex/right.hex", "r");
        if (fd_right == 0) begin
            $display("[TB_MEM_MODEL] ERROR: Could not open /home/workstation/elastix_gemm/hex/right.hex");
            $display("[TB_MEM_MODEL] Using zero-initialized memory for right matrix");
        end else begin
            line_idx = 0;
            while (!$feof(fd_right) && line_idx < 528) begin
                if ($fgets(line_str, fd_right)) begin
                    // Parse hex line: expects 32 hex bytes separated by spaces
                    automatic logic [7:0] hex_bytes[0:31];
                    scan_result = $sscanf(line_str,
                        "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                        hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                        hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                        hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                        hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                        hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                        hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                        hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                        hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);

                    if (scan_result == 32) begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx = byte_idx + 1) begin
                            // Write to Block 1 starting at line 528
                            mem_array[LINES_PER_BLOCK + line_idx][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                    line_idx = line_idx + 1;
                end
            end
            $fclose(fd_right);
            $display("[TB_MEM_MODEL] Loaded %0d lines from right.hex (Block 1)", line_idx);
        end

        $display("[TB_MEM_MODEL] Memory initialization complete");
        $display("[TB_MEM_MODEL]   Total: %0d blocks x %0d lines = %0d lines",
                 NUM_BLOCKS, LINES_PER_BLOCK, NUM_BLOCKS*LINES_PER_BLOCK);
        $display("[TB_MEM_MODEL]   Block 0 (Left matrix):  Lines 0-%0d", LINES_PER_BLOCK-1);
        $display("[TB_MEM_MODEL]   Block 1 (Right matrix): Lines %0d-%0d", LINES_PER_BLOCK, 2*LINES_PER_BLOCK-1);

        // Display first few bytes for verification
        $display("[TB_MEM_MODEL] Left matrix first line[7:0]: 0x%02h %02h %02h %02h",
                 mem_array[0][7:0], mem_array[0][15:8], mem_array[0][23:16], mem_array[0][31:24]);
        $display("[TB_MEM_MODEL] Right matrix first line[7:0]: 0x%02h %02h %02h %02h",
                 mem_array[528][7:0], mem_array[528][15:8], mem_array[528][23:16], mem_array[528][31:24]);
    end

    // ===================================================================
    // AXI State Machine - PERFECT: No latency counter needed
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            axi_state_reg <= AXI_IDLE;
        end else begin
            axi_state_reg <= axi_state_next;
        end
    end

    always_comb begin
        axi_state_next = axi_state_reg;

        case (axi_state_reg)
            AXI_IDLE: begin
                // PERFECT: Accept AR and go directly to RDATA (data ready next cycle)
                if (axi_mem_if.arvalid) begin
                    axi_state_next = AXI_RDATA;
                end
            end

            AXI_RDATA: begin
                // PERFECT: Continuous data every cycle
                if (axi_mem_if.rvalid && axi_mem_if.rready) begin
                    if (axi_mem_if.rlast) begin
                        axi_state_next = AXI_IDLE;
                    end
                end
            end

            default: begin
                axi_state_next = AXI_IDLE;
            end
        endcase
    end

    // ===================================================================
    // AXI Read Address Channel
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_addr_reg <= '0;
            ar_id_reg <= '0;
            ar_len_reg <= '0;
            ar_size_reg <= '0;
            ar_burst_reg <= '0;
        end else begin
            if (axi_state_reg == AXI_IDLE && axi_mem_if.arvalid) begin
                ar_addr_reg <= axi_mem_if.araddr[ADDR_WIDTH-1:0];
                ar_id_reg <= axi_mem_if.arid;
                ar_len_reg <= axi_mem_if.arlen;
                ar_size_reg <= axi_mem_if.arsize;
                ar_burst_reg <= axi_mem_if.arburst;
            end
        end
    end

    // PERFECT: arready same cycle as arvalid (combinational)
    assign axi_mem_if.arready = (axi_state_reg == AXI_IDLE);

    // ===================================================================
    // AXI Read Data Channel
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            beat_count_reg <= '0;
            read_data_reg <= '0;
            read_valid_reg <= 1'b0;
            read_last_reg <= 1'b0;
            read_count_reg <= '0;
            last_addr_reg <= '0;
        end else begin
            read_valid_reg <= 1'b0;  // Default
            read_last_reg <= 1'b0;

            case (axi_state_reg)
                AXI_IDLE: begin
                    // PERFECT: Reset beat counter when accepting new AR
                    if (axi_mem_if.arvalid && axi_mem_if.arready) begin
                        beat_count_reg <= '0;
                    end
                end

                AXI_RDATA: begin
                    // PERFECT: Data available EVERY cycle (continuous rvalid)
                    if (!read_valid_reg || (read_valid_reg && axi_mem_if.rready)) begin
                        // Calculate memory address (byte address -> line address)
                        logic [ADDR_WIDTH-1:0] byte_addr;
                        logic [25:0] line_addr_26bit;  // 26-bit line address
                        logic [15:0] line_addr_16bit;  // Final 16-bit for indexing (max 65536 lines)

                        byte_addr = ar_addr_reg + (beat_count_reg << ar_size_reg);
                        
                        // Step 1: Extract bits [30:5] to get 26-bit line address
                        line_addr_26bit = byte_addr[30:5];
                        
                        // Step 2: Truncate to 16 bits for memory array indexing
                        line_addr_16bit = line_addr_26bit[15:0];

                        // Read from memory
                        if (line_addr_16bit < NUM_BLOCKS*LINES_PER_BLOCK) begin
                            read_data_reg <= mem_array[line_addr_16bit];
                            if (line_addr_16bit == 0 || line_addr_16bit == 528) begin
                                $display("[TB_MEM] @%0t Reading mem_array[%0d]: first 8 bytes=0x%02x %02x %02x %02x %02x %02x %02x %02x",
                                         $time, line_addr_16bit, 
                                         mem_array[line_addr_16bit][7:0], mem_array[line_addr_16bit][15:8], 
                                         mem_array[line_addr_16bit][23:16], mem_array[line_addr_16bit][31:24],
                                         mem_array[line_addr_16bit][39:32], mem_array[line_addr_16bit][47:40],
                                         mem_array[line_addr_16bit][55:48], mem_array[line_addr_16bit][63:56]);
                            end
                        end else begin
                            read_data_reg <= {DATA_WIDTH{1'b0}};  // Out of range
                            $warning("[TB_MEM_MODEL] Address out of range: line %0d (26-bit: %0d) >= %0d",
                                    line_addr_16bit, line_addr_26bit, NUM_BLOCKS*LINES_PER_BLOCK);
                        end

                        read_valid_reg <= 1'b1;
                        read_last_reg <= (beat_count_reg == ar_len_reg);

                        // Increment beat counter
                        if (beat_count_reg < ar_len_reg) begin
                            beat_count_reg <= beat_count_reg + 1;
                        end

                        // Debug tracking
                        read_count_reg <= read_count_reg + 1;
                        last_addr_reg <= byte_addr;
                    end
                end
            endcase
        end
    end

    // AXI Read Data Channel outputs
    assign axi_mem_if.rvalid = read_valid_reg;
    assign axi_mem_if.rid    = ar_id_reg;
    assign axi_mem_if.rdata  = read_data_reg;
    assign axi_mem_if.rresp  = 2'b00;  // OKAY
    assign axi_mem_if.rlast  = read_last_reg;

    // ===================================================================
    // AXI Write Channels (Unused - Tie Off)
    // ===================================================================
    assign axi_mem_if.awready = 1'b0;
    assign axi_mem_if.wready  = 1'b0;
    assign axi_mem_if.bvalid  = 1'b0;
    assign axi_mem_if.bid     = '0;
    assign axi_mem_if.bresp   = 2'b11;  // DECERR (not supported)

    // ===================================================================
    // Debug Outputs
    // ===================================================================
    assign o_read_count = read_count_reg;
    assign o_last_addr = last_addr_reg;

    // ===================================================================
    // Debug Display (for simulation)
    // ===================================================================

    `ifdef SIM_VERBOSE
        always @(posedge i_clk) begin
            // Debug state transitions
            if (axi_state_reg != axi_state_next) begin
                $display("[TB_MEM_MODEL] @%0t State: %0d -> %0d", $time, axi_state_reg, axi_state_next);
            end

            if (axi_state_reg == AXI_RDATA && beat_count_reg == 0) begin
                // PERFECT: Print AR info when entering RDATA for first time
                $display("[TB_MEM_MODEL] AR: addr=0x%08x, id=0x%02x, len=%0d, size=%0d, burst=%0d",
                         ar_addr_reg, ar_id_reg, ar_len_reg+1, 1<<ar_size_reg, ar_burst_reg);
            end

            if (read_valid_reg && axi_mem_if.rready) begin
                $display("[TB_MEM_MODEL] R: beat=%0d/%0d, data=0x%064x, last=%0b",
                         beat_count_reg, ar_len_reg+1, read_data_reg, read_last_reg);
            end
        end
    `endif

endmodule : tb_memory_model
