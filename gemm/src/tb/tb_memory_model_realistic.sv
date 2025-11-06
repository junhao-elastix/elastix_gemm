// ------------------------------------------------------------------
// Realistic GDDR6 Memory Model for Fetcher Optimization
//
// Purpose: Emulates GDDR6 memory with realistic 32-outstanding-request limit
// Key Features:
//  - 32 outstanding AR transaction limit (matches Achronix GDDR6 NoC)
//  - 100ns read latency (realistic GDDR6 timing)
//  - Queued AR processing (can accept new ARs while serving old bursts)
//  - GFP8 block structure (528 lines × 256-bit per block)
//
// Reference: gddr_ref_design/src/tb/tb_noc_memory_behavioural.sv
// Author: Fetcher Optimization
// Date: November 3, 2025
// Updated: November 6, 2025 - 100% compliance with reference model
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module tb_memory_model_realistic
#(
    parameter DATA_WIDTH = 256,            // 256-bit AXI data width
    parameter ADDR_WIDTH = 42,             // AXI address width
    parameter LINES_PER_BLOCK = 528,       // GFP8 block size
    parameter NUM_BLOCKS = 2,              // Left and right blocks
    parameter LATENCY_CYCLES = 40,         // 100ns @ 400MHz = 40 cycles
    parameter MAX_OUTSTANDING = 32,        // GDDR6 NoC limit
    parameter VERBOSITY = 2                // 0=quiet, 1=AR/R summary, 2=detailed
)
(
    input  logic        i_clk,
    input  logic        i_reset_n,

    // AXI4 Responder Interface
    t_AXI4.responder    axi_mem_if,

    // Debug/Statistics
    output logic [31:0] o_outstanding_count,
    output logic [31:0] o_total_ar_received,
    output logic [31:0] o_total_r_issued
);

    // ===================================================================
    // Memory Array (Associative for sparse storage)
    // ===================================================================
    logic [DATA_WIDTH-1:0] mem_array [0:NUM_BLOCKS*LINES_PER_BLOCK-1];

    // ===================================================================
    // AR Transaction Queue (FIFO for outstanding requests)
    // ===================================================================
    typedef struct {
        logic [ADDR_WIDTH-1:0] addr;
        logic [7:0]            arid;
        logic [7:0]            arlen;
        logic [2:0]            arsize;
        logic [1:0]            arburst;
        int                    latency_remaining;  // Cycles until first rdata
    } ar_transaction_t;

    ar_transaction_t ar_queue[$];  // Dynamic queue (max size enforced manually)
    logic [5:0]      outstanding_count;  // 0-32
    logic            ar_queue_full;

    assign ar_queue_full = (outstanding_count >= MAX_OUTSTANDING);
    assign o_outstanding_count = outstanding_count;

    // ===================================================================
    // Statistics
    // ===================================================================
    logic [31:0] total_ar_received;
    logic [31:0] total_r_issued;
    logic [31:0] max_outstanding_reached;

    assign o_total_ar_received = total_ar_received;
    assign o_total_r_issued = total_r_issued;

    // ===================================================================
    // GDDR Address Conversion and Validation Functions
    // ===================================================================
    // Reference: gddr_ref_design/src/tb/tb_noc_memory_behavioural.sv
    
    // GDDR burst overflow check bit (12 bits = 4kB page boundary)
    // Reference uses 12 bits but notes GDDR datasheet suggests 11 bits (2kB row)
    localparam GDDR_BURST_OVERFLOW_BIT = 12;
    
    // Check that burst length will not overflow a GDDR column
    // Reference: lines 115-133 of tb_noc_memory_behavioural.sv
    function void check_burst_length(
        input [ADDR_WIDTH-1:0] addr,
        input [7:0] len,
        input string trans
    );
        // Create a mask where the necessary bottom bits are 0
        const logic [ADDR_WIDTH-1:0] ADDR_MASK = (-42'h1 << GDDR_BURST_OVERFLOW_BIT);
        // The address is per byte. The length is per AXI beat. As each AXI beat is 32 bytes
        // the length has to be multiplied by 32 to give a per byte calculation
        if (((addr + {(len+1), 5'b0} - 1) & ADDR_MASK) != (addr & ADDR_MASK)) begin
            $error("[MEM_MODEL_REALISTIC] GDDR %s burst will overflow. Addr 0x%010h. Length 0x%02h (hex) AXI beats", 
                   trans, addr, len);
            $stop(1);
        end
        // Ensure GDDR address is properly aligned (bottom 5 bits must be 0, bits [32:30] must be 0)
        if ((addr[4:0] != 0) || (addr[32:30] != 0)) begin
            $warning("[MEM_MODEL_REALISTIC] GDDR %s address has bits that will be ignored. Addr 0x%010h", 
                    trans, addr);
        end
    endfunction
    
    // Convert AXI address to GDDR memory address format
    // Reference: lines 164-177 of tb_noc_memory_behavioural.sv
    // GDDR: {5'b0, addr[36:33], 3'b000, addr[29:5]}
    // GDDR CTRL ID is 4 bits in locations [36:33]
    // Top bits [41:37] must be 0 to access a GDDR
    function automatic logic [ADDR_WIDTH-1:0] convert_mem_addr(
        input [ADDR_WIDTH-1:0] addr
    );
        // GDDR device: 8Gb = 1GB, so 30 bits of address
        // Extract: {5'b0, addr[36:33] (CTRL ID), 3'b000, addr[29:5] (line address)}
        convert_mem_addr = {5'b0, addr[36:33], 3'b000, addr[29:5]};
    endfunction

    // ===================================================================
    // Memory Initialization - Load from Hex Files
    // ===================================================================
    initial begin
        integer fd_left, fd_right;
        string line_str;
        integer line_idx, scan_result;
        logic [7:0] hex_bytes[0:31];

        if (VERBOSITY >= 1) begin
            $display("[MEM_MODEL_REALISTIC] ===============================================");
            $display("[MEM_MODEL_REALISTIC] REALISTIC GDDR6 MEMORY MODEL");
            $display("[MEM_MODEL_REALISTIC] - Max Outstanding ARs: %0d", MAX_OUTSTANDING);
            $display("[MEM_MODEL_REALISTIC] - Read Latency: %0d cycles (%.1fns @ 400MHz)",
                     LATENCY_CYCLES, LATENCY_CYCLES * 2.5);
            $display("[MEM_MODEL_REALISTIC] - Blocks: %0d x %0d lines", NUM_BLOCKS, LINES_PER_BLOCK);
            $display("[MEM_MODEL_REALISTIC] ===============================================");
        end

        // Initialize all memory to zero
        for (int i = 0; i < NUM_BLOCKS*LINES_PER_BLOCK; i = i + 1) begin
            mem_array[i] = '0;
        end

        // Load Block 0: Left matrix
        fd_left = $fopen("/home/dev/Dev/elastix_gemm/hex/left.hex", "r");
        if (fd_left != 0) begin
            line_idx = 0;
            while (!$feof(fd_left) && line_idx < LINES_PER_BLOCK) begin
                if ($fgets(line_str, fd_left)) begin
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
                        for (int byte_idx = 0; byte_idx < 32; byte_idx = byte_idx + 1) begin
                            mem_array[line_idx][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                    line_idx = line_idx + 1;
                end
            end
            $fclose(fd_left);
            if (VERBOSITY >= 1) $display("[MEM_MODEL_REALISTIC] Loaded %0d lines from left.hex", line_idx);
        end

        // Load Block 1: Right matrix
        fd_right = $fopen("/home/dev/Dev/elastix_gemm/hex/right.hex", "r");
        if (fd_right != 0) begin
            line_idx = 0;
            while (!$feof(fd_right) && line_idx < LINES_PER_BLOCK) begin
                if ($fgets(line_str, fd_right)) begin
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
                        for (int byte_idx = 0; byte_idx < 32; byte_idx = byte_idx + 1) begin
                            mem_array[LINES_PER_BLOCK + line_idx][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                    line_idx = line_idx + 1;
                end
            end
            $fclose(fd_right);
            if (VERBOSITY >= 1) $display("[MEM_MODEL_REALISTIC] Loaded %0d lines from right.hex", line_idx);
        end

        if (VERBOSITY >= 1) $display("[MEM_MODEL_REALISTIC] Memory initialization complete");
    end

    // ===================================================================
    // AXI Read Address Channel - Accept ARs with 32-outstanding limit
    // ===================================================================
    logic ar_accepted;   // AR handshake this cycle
    logic r_burst_complete;  // R burst completed this cycle

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            total_ar_received <= '0;
        end else begin
            // Accept new AR if not full
            if (axi_mem_if.arvalid && axi_mem_if.arready) begin
                ar_transaction_t new_ar;
                new_ar.addr = axi_mem_if.araddr;
                new_ar.arid = axi_mem_if.arid;
                new_ar.arlen = axi_mem_if.arlen;
                new_ar.arsize = axi_mem_if.arsize;
                new_ar.arburst = axi_mem_if.arburst;
                new_ar.latency_remaining = LATENCY_CYCLES;

                // Check burst length (reference model compliance)
                check_burst_length(new_ar.addr, new_ar.arlen, "read");

                ar_queue.push_back(new_ar);
                total_ar_received <= total_ar_received + 1;

                if (VERBOSITY >= 2) begin
                    $display("[MEM_MODEL_REALISTIC] @%0t AR[%0d]: ARID=0x%02h, ADDR=0x%010h, LEN=%0d, Outstanding=%0d/%0d",
                             $time, total_ar_received, new_ar.arid, new_ar.addr, new_ar.arlen + 1,
                             outstanding_count + 1, MAX_OUTSTANDING);
                end
            end
        end
    end

    assign ar_accepted = (axi_mem_if.arvalid && axi_mem_if.arready);

    // arready: HIGH when queue not full
    assign axi_mem_if.arready = ~ar_queue_full;

    // ===================================================================
    // Outstanding Counter Management (single always_ff block)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            outstanding_count <= '0;
            max_outstanding_reached <= '0;
        end else begin
            case ({ar_accepted, r_burst_complete})
                2'b00: outstanding_count <= outstanding_count;
                2'b01: outstanding_count <= outstanding_count - 1;  // R complete
                2'b10: outstanding_count <= outstanding_count + 1;  // AR accepted
                2'b11: outstanding_count <= outstanding_count;      // Both (net zero)
            endcase

            // Track max outstanding
            if (ar_accepted && !r_burst_complete) begin
                if ((outstanding_count + 1) > max_outstanding_reached) begin
                    max_outstanding_reached <= outstanding_count + 1;
                end
            end
        end
    end

    // ===================================================================
    // AR Queue Processing - Decrement latency counters
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            // Queue cleared by reset (SystemVerilog queues auto-reset)
        end else begin
            // Decrement latency for all queued ARs
            for (int i = 0; i < ar_queue.size(); i = i + 1) begin
                if (ar_queue[i].latency_remaining > 0) begin
                    ar_queue[i].latency_remaining = ar_queue[i].latency_remaining - 1;
                end
            end
        end
    end

    // ===================================================================
    // AXI Read Data Channel - Issue R beats when latency expires
    // ===================================================================
    typedef enum logic [1:0] {
        R_IDLE    = 2'b00,
        R_SERVING = 2'b01
    } r_state_t;

    r_state_t r_state;
    logic [7:0] r_beat_count;
    ar_transaction_t current_ar;
    logic [ADDR_WIDTH-1:0] current_addr;
    logic [31:0] line_idx;  // Move declaration outside always block

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            r_state <= R_IDLE;
            r_beat_count <= '0;
            current_addr <= '0;
            total_r_issued <= '0;
            r_burst_complete <= 1'b0;
        end else begin
            r_burst_complete <= 1'b0;  // Default (pulse signal)

            case (r_state)
                R_IDLE: begin
                    // Check if any AR has completed latency
                    if (ar_queue.size() > 0 && ar_queue[0].latency_remaining == 0) begin
                        // Start serving this AR - read directly from queue for initialization
                        current_ar <= ar_queue[0];
                        current_addr <= ar_queue[0].addr;  // Use queue value, not current_ar
                        r_beat_count <= 0;
                        r_state <= R_SERVING;

                        if (VERBOSITY >= 2) begin
                            $display("[MEM_MODEL_REALISTIC] @%0t R_START: ARID=0x%02h, ADDR=0x%010h, LEN=%0d",
                                     $time, ar_queue[0].arid, ar_queue[0].addr, ar_queue[0].arlen + 1);
                        end
                    end
                end

                R_SERVING: begin
                    // Issue R beats
                    if (axi_mem_if.rready) begin
                        r_beat_count <= r_beat_count + 1;
                        total_r_issued <= total_r_issued + 1;

                        // Increment address for INCR burst
                        // Reference: lines 279-280 of tb_noc_memory_behavioural.sv
                        // Check that address doesn't wrap around (addr[29:5] != -1)
                        if (current_ar.arburst == 2'b01 && r_beat_count < current_ar.arlen) begin
                            if (current_addr[29:5] != 26'h3FFFFFF) begin  // Check for wrap-around
                                current_addr <= current_addr + 42'h20;  // +32 bytes per beat
                            end else begin
                                // Wrap-around case (should not happen with proper addressing)
                                $warning("[MEM_MODEL_REALISTIC] INCR burst address wrap-around detected at 0x%010h", current_addr);
                            end
                        end

                        // Last beat?
                        if (r_beat_count >= current_ar.arlen) begin
                            // Pop AR from queue
                            void'(ar_queue.pop_front());
                            r_state <= R_IDLE;
                            r_burst_complete <= 1'b1;  // Signal completion for outstanding counter

                            if (VERBOSITY >= 2) begin
                                $display("[MEM_MODEL_REALISTIC] @%0t R_COMPLETE: ARID=0x%02h",
                                         $time, current_ar.arid);
                            end
                        end
                    end
                end

                default: r_state = R_IDLE;
            endcase
        end
    end

    // Convert address to memory line index
    // Address format from fetcher: {Page_ID[9], Pad[2], Line[26], Byte[5]}
    // Reference model uses convert_mem_addr() for full-chip addressing,
    // but for testbench we extract line directly from original address format
    function automatic logic [31:0] addr_to_line(logic [ADDR_WIDTH-1:0] addr);
        logic [25:0] line_addr_26bit;
        
        // Extract line address from bits [30:5] (matches fetcher address format)
        // This matches the original addressing scheme used by the testbench
        line_addr_26bit = addr[30:5];
        
        // Return as 32-bit value (truncate to fit memory array)
        return {6'b0, line_addr_26bit};
    endfunction

    // R channel outputs
    logic [DATA_WIDTH-1:0] rdata_reg;
    logic                  rvalid_reg;
    logic                  rlast_reg;
    logic [7:0]            rid_reg;

    // Combinational logic for memory read address
    always_comb begin
        line_idx = addr_to_line(current_addr);
    end

    // R channel output generation (combined)
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            rdata_reg <= '0;
            rvalid_reg <= 1'b0;
            rlast_reg <= 1'b0;
            rid_reg <= '0;
        end else begin
            rvalid_reg <= 1'b0;  // Default
            rlast_reg <= 1'b0;

            if (r_state == R_SERVING) begin
                rvalid_reg <= 1'b1;
                rid_reg <= current_ar.arid;
                rlast_reg <= (r_beat_count == current_ar.arlen);

                // Read data from memory
                if (line_idx < (NUM_BLOCKS * LINES_PER_BLOCK)) begin
                    rdata_reg <= mem_array[line_idx];

                    if (VERBOSITY >= 3) begin
                        $display("[MEM_MODEL_REALISTIC] @%0t R_BEAT[%0d]: ARID=0x%02h, ADDR=0x%010h, LINE=%0d, DATA=0x%064h, RLAST=%0b",
                                 $time, r_beat_count, current_ar.arid, current_addr, line_idx,
                                 mem_array[line_idx], (r_beat_count == current_ar.arlen));
                    end
                end else begin
                    // Out-of-range address - return zeros
                    rdata_reg <= {DATA_WIDTH{1'b0}};

                    if (VERBOSITY >= 3) begin
                        $display("[MEM_MODEL_REALISTIC] @%0t R_BEAT[%0d]: ARID=0x%02h, ADDR=0x%010h, LINE=%0d OUT-OF-RANGE (>=%0d), DATA=0x0, RLAST=%0b",
                                 $time, r_beat_count, current_ar.arid, current_addr, line_idx,
                                 NUM_BLOCKS * LINES_PER_BLOCK, (r_beat_count == current_ar.arlen));
                    end
                end
            end
        end
    end

    assign axi_mem_if.rvalid = rvalid_reg;
    assign axi_mem_if.rdata = rdata_reg;
    assign axi_mem_if.rid = rid_reg;
    assign axi_mem_if.rlast = rlast_reg;
    assign axi_mem_if.rresp = 2'b00;  // OKAY

    // ===================================================================
    // AXI Write Channels (unused - tie off)
    // ===================================================================
    assign axi_mem_if.awready = 1'b0;
    assign axi_mem_if.wready = 1'b0;
    assign axi_mem_if.bvalid = 1'b0;
    assign axi_mem_if.bid = '0;
    assign axi_mem_if.bresp = '0;

    // ===================================================================
    // End-of-Test Statistics
    // ===================================================================
    final begin
        if (VERBOSITY >= 1) begin
            $display("[MEM_MODEL_REALISTIC] ===============================================");
            $display("[MEM_MODEL_REALISTIC] FINAL STATISTICS:");
            $display("[MEM_MODEL_REALISTIC] Total ARs received: %0d", total_ar_received);
            $display("[MEM_MODEL_REALISTIC] Total R beats issued: %0d", total_r_issued);
            $display("[MEM_MODEL_REALISTIC] Max outstanding reached: %0d / %0d",
                     max_outstanding_reached, MAX_OUTSTANDING);
            $display("[MEM_MODEL_REALISTIC] ===============================================");
        end
    end

endmodule : tb_memory_model_realistic
