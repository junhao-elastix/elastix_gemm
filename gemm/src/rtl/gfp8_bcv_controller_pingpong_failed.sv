// ------------------------------------------------------------------
// GFP8 BCV Loop Controller
//
// Purpose: Orchestrate BxCxV nested loops for matrix multiplication
// Algorithm: For each (b,c): accumulate V Native Vector dot products
//
// Matrix Dimensions:
//  - Matrix A (left): B rows x (128xV) columns -> uses BxV Native Vectors
//  - Matrix B (right): (128xV) rows x C columns -> uses CxV Native Vectors
//  - Output: B x C results (one per (b,c) pair)
//
// State Machine:
//  DUAL FSM ARCHITECTURE with Ping-Pong Buffering
//
//  FSM_FILL: Manages buffer filling (producer)
//    FILL_IDLE   -> Wait for trigger or check conditions to start fill
//    FILL_ACTIVE -> Fill PING or PONG buffer (5 cycles)
//
//  FSM_COMP: Manages computation (consumer)
//    COMP_IDLE   -> Wait for ready buffer
//    COMP_NV     -> Compute NV dot product (4 cycles)
//    COMP_ACCUM  -> Accumulate result (1 cycle)
//    COMP_RETURN -> Output final result
//
//  Handshake Protocol:
//    filling_ping : Fill FSM sets HIGH when filling PING, Compute FSM clears when starting compute
//    filling_pong : Fill FSM sets HIGH when filling PONG, Compute FSM clears when starting compute
//    ping_ready   : Fill FSM sets HIGH when PING filled, Compute FSM clears in ACCUM after compute
//    pong_ready   : Fill FSM sets HIGH when PONG filled, Compute FSM clears in ACCUM after compute
//
// Latency per output (Ping-Pong):
//   First V:  10 cycles (5 fill + 4 compute + 1 accum)
//   V>=1:     6 cycles (max(5 fill, 4 compute) overlapped + 1 accum)
//   Total:    10 + 6×(V-1) + 1 (return) ≈ 6V + 5 cycles per BxC result
//
// Author: Refactoring from compute_engine.sv
// Date: Fri Oct 10 2025
// ------------------------------------------------------------------

module gfp8_bcv_controller (
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,
    
    // TILE Command Interface
    input  logic        i_tile_en,
    input  logic [7:0]  i_dim_b,              // Output rows (batch)
    input  logic [7:0]  i_dim_c,              // Output columns
    input  logic [7:0]  i_dim_v,              // Inner dimension multiplier (V Native Vectors)
    input  logic [8:0]  i_left_base_addr,     // Base address for left matrix in tile_bram (9-bit for 512 lines)
    input  logic [8:0]  i_right_base_addr,    // Base address for right matrix in tile_bram (9-bit for 512 lines)
    output logic        o_tile_done,

    // BRAM Mantissa Read Interface (to tile_bram - 512 lines = 9-bit address)
    output logic [8:0]   o_man_left_rd_addr,
    output logic         o_man_left_rd_en,
    input  logic [255:0] i_man_left_rd_data,

    output logic [8:0]   o_man_right_rd_addr,
    output logic         o_man_right_rd_en,
    input  logic [255:0] i_man_right_rd_data,

    // Exponent Read Interface (to dispatcher_bram exp ports)
    output logic [8:0]   o_exp_left_rd_addr,
    output logic         o_exp_left_rd_en,
    input  logic [7:0]   i_exp_left_rd_data,

    output logic [8:0]   o_exp_right_rd_addr,
    output logic         o_exp_right_rd_en,
    input  logic [7:0]   i_exp_right_rd_data,
    
    // Result Interface
    output logic signed [31:0] o_result_mantissa,
    output logic signed [7:0]  o_result_exponent,
    output logic               o_result_valid
);

    // ===================================================================
    // Dual State Machine Definition
    // ===================================================================
    
    // Fill FSM
    typedef enum logic {
        FILL_IDLE   = 1'b0,
        FILL_ACTIVE = 1'b1
    } fill_state_t;
    fill_state_t fill_state_reg, fill_state_next;
    
    // Compute FSM
    typedef enum logic [2:0] {
        COMP_IDLE   = 3'd0,
        COMP_NV     = 3'd1,
        COMP_ACCUM  = 3'd2,
        COMP_RETURN = 3'd3,
        COMP_DONE   = 3'd4
    } comp_state_t;
    comp_state_t comp_state_reg, comp_state_next;
    
    // ===================================================================
    // Loop Indices (B, C, V nested loops)
    // ===================================================================
    logic [7:0] b_idx;  // Batch index (0 to B-1)
    logic [7:0] c_idx;  // Column index (0 to C-1)
    logic [7:0] v_idx;  // Vector index (0 to V-1)
    
    // Dimension registers
    logic [7:0] dim_b_reg, dim_c_reg, dim_v_reg;
    logic [8:0] left_base_reg, right_base_reg;  // 9-bit for 512-line tile_bram
    
    // Rising edge detection for i_tile_en
    logic i_tile_en_prev;
    logic i_tile_en_rising;
    
    assign i_tile_en_rising = i_tile_en && !i_tile_en_prev;
    
    // ===================================================================
    // Ping-Pong Handshake Signals
    // ===================================================================
    logic filling_ping, filling_pong;  // Producer (Fill FSM) sets, Consumer (Comp FSM) clears at start
    logic ping_ready, pong_ready;      // Producer sets, Consumer clears after done
    
    // ===================================================================
    // Native Vector Buffers - PING-PONG (Double Buffering)
    // ===================================================================
    
    // PING buffers
    logic [31:0]  nv_left_exp_ping;
    logic [255:0] nv_left_man_ping [0:3];
    logic [31:0]  nv_right_exp_ping;
    logic [255:0] nv_right_man_ping [0:3];
    
    // PONG buffers
    logic [31:0]  nv_left_exp_pong;
    logic [255:0] nv_left_man_pong [0:3];
    logic [31:0]  nv_right_exp_pong;
    logic [255:0] nv_right_man_pong [0:3];
    
    // Active buffer selection (for compute FSM)
    logic use_pong;  // 0=use PING, 1=use PONG
    logic [31:0]  nv_left_exp_active;
    logic [255:0] nv_left_man_active [0:3];
    logic [31:0]  nv_right_exp_active;
    logic [255:0] nv_right_man_active [0:3];
    
    // Buffer mux
    always_comb begin
        if (use_pong) begin
            nv_left_exp_active = nv_left_exp_pong;
            nv_right_exp_active = nv_right_exp_pong;
            for (int i = 0; i < 4; i++) begin
                nv_left_man_active[i] = nv_left_man_pong[i];
                nv_right_man_active[i] = nv_right_man_pong[i];
            end
        end else begin
            nv_left_exp_active = nv_left_exp_ping;
            nv_right_exp_active = nv_right_exp_ping;
            for (int i = 0; i < 4; i++) begin
                nv_left_man_active[i] = nv_left_man_ping[i];
                nv_right_man_active[i] = nv_right_man_ping[i];
            end
        end
    end
    
    // Fill FSM control
    logic fill_target;  // 0=fill PING, 1=fill PONG
    logic [2:0] fill_cycle;  // Fill cycle counter (0-4)
    
    // ===================================================================
    // NV Dot Product Instance
    // ===================================================================
    logic signed [31:0] nv_dot_mantissa;
    logic signed [7:0]  nv_dot_exponent;
    
    // Enable signal: pulse high when entering COMP_NV
    logic nv_dot_input_valid;
    assign nv_dot_input_valid = (comp_state_reg != COMP_NV) && (comp_state_next == COMP_NV);
    
    gfp8_nv_dot u_nv_dot (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        .i_input_valid      (nv_dot_input_valid),
        .i_exp_left         (nv_left_exp_active),
        .i_man_left         (nv_left_man_active),
        .i_exp_right        (nv_right_exp_active),
        .i_man_right        (nv_right_man_active),
        .o_result_mantissa  (nv_dot_mantissa),
        .o_result_exponent  (nv_dot_exponent)
    );
    
    // ===================================================================
    // V-Loop Accumulator
    // ===================================================================
    logic signed [31:0] accum_mantissa;
    logic signed [7:0]  accum_exponent;
    
    // Compute pipeline counter (track 4-cycle latency)
    logic [2:0] compute_wait;
    
    // ===================================================================
    // Fill FSM - Next State Logic
    // ===================================================================
    always_comb begin
        fill_state_next = fill_state_reg;
        
        case (fill_state_reg)
            FILL_IDLE: begin
                // Start filling if:
                // 1. PING needs filling (not ready AND not currently filling it)
                // 2. PONG needs filling (not ready AND not currently filling it)
                // Priority: PING first
                if ((!filling_ping && !ping_ready) || (!filling_pong && !pong_ready)) begin
                    fill_state_next = FILL_ACTIVE;
                end
            end
            
            FILL_ACTIVE: begin
                // Fill complete when cycle reaches 4 (captured all 4 groups)
                if (fill_cycle == 3'd4) begin
                    fill_state_next = FILL_IDLE;
                end
            end
        endcase
    end
    
    // ===================================================================
    // Compute FSM - Next State Logic
    // ===================================================================
    always_comb begin
        comp_state_next = comp_state_reg;
        
        case (comp_state_reg)
            COMP_IDLE: begin
                // Wait for either buffer to be ready
                if (ping_ready || pong_ready) begin
                    comp_state_next = COMP_NV;
                end
            end
            
            COMP_NV: begin
                // Wait for gfp8_nv_dot 4-cycle pipeline
                if (compute_wait == 3'd3) begin
                    comp_state_next = COMP_ACCUM;
                end
            end
            
            COMP_ACCUM: begin
                // Check if V loop is complete
                if (v_idx >= dim_v_reg - 1) begin
                    comp_state_next = COMP_RETURN;
                end else begin
                    // More V iterations needed, wait for next buffer
                    comp_state_next = COMP_IDLE;
                end
            end
            
            COMP_RETURN: begin
                // Check if all BxC outputs are complete
                if (c_idx >= dim_c_reg - 1 && b_idx >= dim_b_reg - 1) begin
                    comp_state_next = COMP_DONE;
                end else begin
                    // Start next output element, wait for buffer
                    comp_state_next = COMP_IDLE;
                end
            end
            
            COMP_DONE: begin
                comp_state_next = COMP_IDLE;
            end
        endcase
    end
    
    // ===================================================================
    // Dual FSM - Sequential Logic
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            fill_state_reg <= FILL_IDLE;
            comp_state_reg <= COMP_IDLE;
        end else begin
            fill_state_reg <= fill_state_next;
            comp_state_reg <= comp_state_next;
        end
    end
    
    // ===================================================================
    // BRAM Read Address Generation - DIRECT (COMBINATIONAL) CONNECTION
    // ===================================================================
    // TRUE 1-cycle latency: Address generated combinationally, data back next cycle
    // No registered outputs - direct wire connection to tile_bram
    //
    // Pipeline:
    //   Cycle N:   Generate address (comb) → BRAM input
    //   Cycle N+1: BRAM output ready → Capture data, generate next address
    
    // Ping-pong fill V index: tracks which V iteration the fill FSM is on
    logic [7:0] fill_v_idx;
    
    always_comb begin
        // Default: no reads
        o_man_left_rd_addr = 9'd0;
        o_man_right_rd_addr = 9'd0;
        o_exp_left_rd_addr = 9'd0;
        o_exp_right_rd_addr = 9'd0;
        o_man_left_rd_en = 1'b0;
        o_man_right_rd_en = 1'b0;
        o_exp_left_rd_en = 1'b0;
        o_exp_right_rd_en = 1'b0;
        
        if (fill_state_reg == FILL_ACTIVE && fill_cycle < 4'd4) begin
            // Calculate NV indices for the FILL operation
            // The fill FSM needs to read ahead of the compute FSM
            automatic logic [15:0] left_nv_index;
            automatic logic [15:0] right_nv_index;
            automatic logic [15:0] left_base_nv;
            automatic logic [15:0] right_base_nv;
            automatic logic [8:0] left_line_addr;
            automatic logic [8:0] right_line_addr;
            
            // Convert base addresses from line units to NV units (divide by 4)
            left_base_nv = {9'd0, left_base_reg[8:2]};
            right_base_nv = {9'd0, right_base_reg[8:2]};
            
            // Calculate NV index based on loop counters and fill V index
            left_nv_index = left_base_nv + ({8'd0, b_idx} * {8'd0, dim_v_reg} + {8'd0, fill_v_idx});
            right_nv_index = right_base_nv + ({8'd0, c_idx} * {8'd0, dim_v_reg} + {8'd0, fill_v_idx});
            
            // Convert NV index to line address and add group offset
            // fill_cycle 0→G0, 1→G1, 2→G2, 3→G3
            left_line_addr = {left_nv_index[6:0], 2'b00} + {7'd0, fill_cycle[1:0]};
            right_line_addr = {right_nv_index[6:0], 2'b00} + {7'd0, fill_cycle[1:0]};
            
            // Combinational assignment - direct to BRAM (no registers!)
            o_man_left_rd_addr = left_line_addr;
            o_man_right_rd_addr = right_line_addr;
            o_exp_left_rd_addr = left_line_addr;
            o_exp_right_rd_addr = right_line_addr;
            o_man_left_rd_en = 1'b1;
            o_man_right_rd_en = 1'b1;
            o_exp_left_rd_en = 1'b1;
            o_exp_right_rd_en = 1'b1;
        end
    end
    
    // ===================================================================
    // Dual FSM: Fill FSM + Compute FSM (in one always_ff block)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            // Fill FSM signals
            fill_cycle <= 3'd0;
            fill_target <= 1'b0;
            fill_v_idx <= 8'd0;
            filling_ping <= 1'b0;
            filling_pong <= 1'b0;
            ping_ready <= 1'b0;
            pong_ready <= 1'b0;
            
            // Compute FSM signals
            compute_wait <= 3'd0;
            use_pong <= 1'b0;
            
            // Initialize PING buffers
            nv_left_exp_ping <= 32'd0;
            nv_right_exp_ping <= 32'd0;
            for (int i = 0; i < 4; i++) begin
                nv_left_man_ping[i] <= 256'd0;
                nv_right_man_ping[i] <= 256'd0;
            end
            
            // Initialize PONG buffers
            nv_left_exp_pong <= 32'd0;
            nv_right_exp_pong <= 32'd0;
            for (int i = 0; i < 4; i++) begin
                nv_left_man_pong[i] <= 256'd0;
                nv_right_man_pong[i] <= 256'd0;
            end
        end else begin
            // ============================================================
            // FILL FSM LOGIC
            // ============================================================
            
            // Startup trigger: Kickstart fill on i_tile_en rising edge
            // Only reset fill_v_idx if we're starting a brand new tile (both FSMs idle)
            if (i_tile_en_rising) begin
                filling_ping <= 1'b1;
                fill_v_idx <= 8'd0;  // Always reset for new tile
                `ifdef SIMULATION
                $display("[PINGPONG] @%0t STARTUP: filling_ping=1, fill_v_idx=0", $time);
                `endif
            end
            
            case (fill_state_reg)
                FILL_IDLE: begin
                    // Determine which buffer to fill next
                    // Priority: PING first, then PONG (must match next-state logic!)
                    // Check V limit only if dimensions are valid (dim_v_reg > 0)
                    if (!filling_ping && !ping_ready && (dim_v_reg == 0 || fill_v_idx < dim_v_reg)) begin
                        // Start filling PING
                        fill_target <= 1'b0;
                        filling_ping <= 1'b1;
                        fill_cycle <= 3'd0;
                        `ifdef SIMULATION
                        $display("[PINGPONG] @%0t FILL_IDLE: Start filling PING (fill_v_idx=%0d, v_idx=%0d, dim_v=%0d)", 
                                 $time, fill_v_idx, v_idx, dim_v_reg);
                        `endif
                    end else if (!filling_pong && !pong_ready && (dim_v_reg == 0 || fill_v_idx < dim_v_reg)) begin
                        // Start filling PONG
                        fill_target <= 1'b1;
                        filling_pong <= 1'b1;
                        fill_cycle <= 3'd0;
                        `ifdef SIMULATION
                        $display("[PINGPONG] @%0t FILL_IDLE: Start filling PONG (fill_v_idx=%0d, v_idx=%0d, dim_v=%0d)", 
                                 $time, fill_v_idx, v_idx, dim_v_reg);
                        `endif
                    end else if (dim_v_reg > 0 && fill_v_idx >= dim_v_reg && !filling_ping && !filling_pong) begin
                        `ifdef SIMULATION
                        $display("[PINGPONG] @%0t FILL_IDLE: All V filled (fill_v_idx=%0d >= dim_v=%0d), waiting...", 
                                 $time, fill_v_idx, dim_v_reg);
                        `endif
                    end
                end
                
                FILL_ACTIVE: begin
                    // Fill the target buffer (5 cycles: 0-4)
                    if (fill_cycle == 3'd1) begin
                        // Cycle 1: Capture G0
                        if (fill_target == 1'b0) begin
                            // Filling PING
                            nv_left_exp_ping[7:0] <= i_exp_left_rd_data;
                            nv_right_exp_ping[7:0] <= i_exp_right_rd_data;
                            nv_left_man_ping[0] <= i_man_left_rd_data;
                            nv_right_man_ping[0] <= i_man_right_rd_data;
                        end else begin
                            // Filling PONG
                            nv_left_exp_pong[7:0] <= i_exp_left_rd_data;
                            nv_right_exp_pong[7:0] <= i_exp_right_rd_data;
                            nv_left_man_pong[0] <= i_man_left_rd_data;
                            nv_right_man_pong[0] <= i_man_right_rd_data;
                        end
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 3'd2) begin
                        // Cycle 2: Capture G1
                        if (fill_target == 1'b0) begin
                            nv_left_exp_ping[15:8] <= i_exp_left_rd_data;
                            nv_right_exp_ping[15:8] <= i_exp_right_rd_data;
                            nv_left_man_ping[1] <= i_man_left_rd_data;
                            nv_right_man_ping[1] <= i_man_right_rd_data;
                        end else begin
                            nv_left_exp_pong[15:8] <= i_exp_left_rd_data;
                            nv_right_exp_pong[15:8] <= i_exp_right_rd_data;
                            nv_left_man_pong[1] <= i_man_left_rd_data;
                            nv_right_man_pong[1] <= i_man_right_rd_data;
                        end
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 3'd3) begin
                        // Cycle 3: Capture G2
                        if (fill_target == 1'b0) begin
                            nv_left_exp_ping[23:16] <= i_exp_left_rd_data;
                            nv_right_exp_ping[23:16] <= i_exp_right_rd_data;
                            nv_left_man_ping[2] <= i_man_left_rd_data;
                            nv_right_man_ping[2] <= i_man_right_rd_data;
                        end else begin
                            nv_left_exp_pong[23:16] <= i_exp_left_rd_data;
                            nv_right_exp_pong[23:16] <= i_exp_right_rd_data;
                            nv_left_man_pong[2] <= i_man_left_rd_data;
                            nv_right_man_pong[2] <= i_man_right_rd_data;
                        end
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 3'd4) begin
                        // Cycle 4: Capture G3, set ready flag, clear filling flag
                        if (fill_target == 1'b0) begin
                            nv_left_exp_ping[31:24] <= i_exp_left_rd_data;
                            nv_right_exp_ping[31:24] <= i_exp_right_rd_data;
                            nv_left_man_ping[3] <= i_man_left_rd_data;
                            nv_right_man_ping[3] <= i_man_right_rd_data;
                            ping_ready <= 1'b1;    // PRODUCER sets ready
                            filling_ping <= 1'b0;   // PRODUCER clears filling (job done)
                            `ifdef SIMULATION
                            $display("[PINGPONG] @%0t FILL_ACTIVE: PING ready (fill_v_idx=%0d)", $time, fill_v_idx);
                            `endif
                        end else begin
                            nv_left_exp_pong[31:24] <= i_exp_left_rd_data;
                            nv_right_exp_pong[31:24] <= i_exp_right_rd_data;
                            nv_left_man_pong[3] <= i_man_left_rd_data;
                            nv_right_man_pong[3] <= i_man_right_rd_data;
                            pong_ready <= 1'b1;    // PRODUCER sets ready
                            filling_pong <= 1'b0;   // PRODUCER clears filling (job done)
                            `ifdef SIMULATION
                            $display("[PINGPONG] @%0t FILL_ACTIVE: PONG ready (fill_v_idx=%0d)", $time, fill_v_idx);
                            `endif
                        end
                        fill_cycle <= 3'd0;
                        // Advance fill V index for next iteration
                        fill_v_idx <= fill_v_idx + 1;
                        `ifdef SIMULATION
                        $display("[PINGPONG] @%0t FILL_ACTIVE: Advancing fill_v_idx %0d->%0d", 
                                 $time, fill_v_idx, fill_v_idx + 1);
                        `endif
                    end else begin
                        // Cycle 0: Just increment
                        fill_cycle <= fill_cycle + 1;
                    end
                end
            endcase
            
            // ============================================================
            // COMPUTE FSM LOGIC
            // ============================================================
            
            case (comp_state_reg)
                COMP_IDLE: begin
                    compute_wait <= 3'd0;
                    // Select which buffer to use when transitioning to COMP_NV
                    if (comp_state_next == COMP_NV) begin
                        use_pong <= pong_ready ? 1'b1 : 1'b0;  // Prefer PONG if both ready
                        `ifdef SIMULATION
                        $display("[PINGPONG] @%0t COMP_IDLE: Selecting %s buffer (ping_ready=%0d, pong_ready=%0d, v_idx=%0d)", 
                                 $time, pong_ready ? "PONG" : "PING", ping_ready, pong_ready, v_idx);
                        `endif
                    end
                end
                
                COMP_NV: begin
                    if (compute_wait < 3'd3) begin
                        compute_wait <= compute_wait + 1;
                    end
                end
                
                COMP_ACCUM: begin
                    // CONSUMER clears ready flag after consuming buffer
                    if (use_pong) begin
                        pong_ready <= 1'b0;
                        `ifdef SIMULATION
                        $display("[PINGPONG] @%0t COMP_ACCUM: Clearing pong_ready (v_idx=%0d)", $time, v_idx);
                        `endif
                    end else begin
                        ping_ready <= 1'b0;
                        `ifdef SIMULATION
                        $display("[PINGPONG] @%0t COMP_ACCUM: Clearing ping_ready (v_idx=%0d)", $time, v_idx);
                        `endif
                    end
                end
                
                COMP_RETURN: begin
                    // Reset fill_v_idx for next B,C pair
                    fill_v_idx <= 8'd0;
                    `ifdef SIMULATION
                    $display("[PINGPONG] @%0t COMP_RETURN: Resetting fill_v_idx to 0 for next B,C pair", $time);
                    `endif
                end
                
                default: begin
                    compute_wait <= 3'd0;
                end
            endcase
        end
    end
    
    // ===================================================================
    // V-Loop Accumulation (with Exponent Alignment) - Compute FSM
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            accum_mantissa <= 32'sd0;
            accum_exponent <= 8'sd0;
        end else begin
            case (comp_state_reg)
                COMP_IDLE: begin
                    // Only reset accumulator when starting a new B,C pair (v_idx==0 from COMP_RETURN)
                    if (v_idx == 8'd0 && comp_state_reg != comp_state_next) begin
                        accum_mantissa <= 32'sd0;
                        accum_exponent <= 8'sd0;
                    end
                end
                
                COMP_ACCUM: begin
                    // Accumulate the result
                    if (v_idx == 8'd0) begin
                        // First V iteration - initialize accumulator
                        accum_mantissa <= nv_dot_mantissa;
                        accum_exponent <= nv_dot_exponent;
                        `ifdef SIMULATION
                        $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d INIT: mant=%0d (0x%08x), exp=%0d",
                                 $time, b_idx, c_idx, v_idx, nv_dot_mantissa, nv_dot_mantissa, nv_dot_exponent);
                        `endif
                    end else begin
                        // Accumulate with exponent alignment
                        automatic logic signed [7:0] max_exp;
                        automatic logic [7:0] exp_diff_accum, exp_diff_dot;
                        automatic logic signed [31:0] aligned_accum, aligned_dot;
                        automatic logic signed [31:0] sum_mantissa;
                        
                        // Find maximum exponent
                        if ($signed(accum_exponent) > $signed(nv_dot_exponent)) begin
                            max_exp = accum_exponent;
                        end else begin
                            max_exp = nv_dot_exponent;
                        end
                        
                        // Align mantissas to maximum exponent
                        exp_diff_accum = max_exp - accum_exponent;
                        exp_diff_dot = max_exp - nv_dot_exponent;
                        
                        // Align accumulated mantissa with underflow check
                        if (exp_diff_accum > 31) begin
                            aligned_accum = 32'sd0;
                        end else begin
                            aligned_accum = $signed(accum_mantissa) >>> exp_diff_accum;
                        end
                        
                        // Align dot product mantissa with underflow check
                        if (exp_diff_dot > 31) begin
                            aligned_dot = 32'sd0;
                        end else begin
                            aligned_dot = $signed(nv_dot_mantissa) >>> exp_diff_dot;
                        end
                        
                        // Sum aligned mantissas
                        sum_mantissa = aligned_accum + aligned_dot;
                        
                        // Update accumulator
                        accum_mantissa <= sum_mantissa;
                        accum_exponent <= max_exp;
                        `ifdef SIMULATION
                        $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d ADD: accum_m=%0d(exp=%0d), dot_m=%0d(exp=%0d) -> aligned_a=%0d, aligned_d=%0d -> sum=%0d(exp=%0d)",
                                 $time, b_idx, c_idx, v_idx, accum_mantissa, accum_exponent, nv_dot_mantissa, nv_dot_exponent,
                                 aligned_accum, aligned_dot, sum_mantissa, max_exp);
                        `endif
                    end
                end
                
                COMP_RETURN: begin
                    // Reset accumulator for next BxC output
                    accum_mantissa <= 32'sd0;
                    accum_exponent <= 8'sd0;
                end
            endcase
        end
    end
    
    // ===================================================================
    // Loop Index Control (B, C, V nested loops) - Compute FSM
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            b_idx <= 8'd0;
            c_idx <= 8'd0;
            v_idx <= 8'd0;
            dim_b_reg <= 8'd0;
            dim_c_reg <= 8'd0;
            dim_v_reg <= 8'd0;
            left_base_reg <= 9'd0;
            right_base_reg <= 9'd0;
            i_tile_en_prev <= 1'b0;
        end else begin
            // Update previous value for edge detection
            i_tile_en_prev <= i_tile_en;
            
            if (i_tile_en_rising) begin
                // Capture dimensions on tile start
                dim_b_reg <= i_dim_b;
                dim_c_reg <= i_dim_c;
                dim_v_reg <= i_dim_v;
                left_base_reg <= i_left_base_addr;
                right_base_reg <= i_right_base_addr;
                // Initialize indices
                b_idx <= 8'd0;
                c_idx <= 8'd0;
                v_idx <= 8'd0;
                $display("[BCV_LOOP] @%0t NEW TILE: B=%0d, C=%0d, V=%0d, left_base=%0d, right_base=%0d", 
                         $time, i_dim_b, i_dim_c, i_dim_v, i_left_base_addr, i_right_base_addr);
            end
            
            case (comp_state_reg)
                COMP_ACCUM: begin
                    // Advance V index within current (b,c) pair
                    v_idx <= v_idx + 1;
                    $display("[BCV_LOOP] ACCUM: b=%0d, c=%0d, v=%0d -> v=%0d", 
                             b_idx, c_idx, v_idx, v_idx + 1);
                end
                
                COMP_RETURN: begin
                    // V loop complete, advance C and B indices
                    v_idx <= 8'd0;  // Reset V for next (b,c) pair
                    
                    $display("[BCV_LOOP] RETURN: b=%0d, c=%0d completed V loop, advancing indices", 
                             b_idx, c_idx);
                    
                    // Only advance indices if NOT done with all outputs
                    if (!(c_idx >= dim_c_reg - 1 && b_idx >= dim_b_reg - 1)) begin
                        // Advance C index
                        if (c_idx >= dim_c_reg - 1) begin
                            c_idx <= 8'd0;
                            // Advance B index
                            b_idx <= b_idx + 1;
                            $display("[BCV_LOOP]   -> Next: b=%0d, c=0", b_idx + 1);
                        end else begin
                            c_idx <= c_idx + 1;
                            $display("[BCV_LOOP]   -> Next: b=%0d, c=%0d", b_idx, c_idx + 1);
                        end
                    end else begin
                        $display("[BCV_LOOP]   -> DONE (all BxC outputs complete)");
                    end
                end
            endcase
        end
    end
    
    // ===================================================================
    // Output Control - Compute FSM
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_result_mantissa <= 32'sd0;
            o_result_exponent <= 8'sd0;
            o_result_valid <= 1'b0;
            o_tile_done <= 1'b0;
        end else begin
            // Default
            o_result_valid <= 1'b0;
            o_tile_done <= 1'b0;
            
            case (comp_state_reg)
                COMP_RETURN: begin
                    // Output accumulated result for this (b,c) pair
                    o_result_mantissa <= accum_mantissa;
                    o_result_exponent <= accum_exponent;
                    o_result_valid <= 1'b1;
                    `ifdef SIMULATION
                    $display("[BCV_ACCUM] @%0t [B%0d,C%0d] RETURN: Final GFP result = mant=%0d (0x%08x), exp=%0d",
                             $time, b_idx, c_idx, accum_mantissa, accum_mantissa, accum_exponent);
                    `endif
                    
                    // Check if this was the last output
                    if (c_idx >= dim_c_reg - 1 && b_idx >= dim_b_reg - 1) begin
                        o_tile_done <= 1'b1;
                    end
                end
            endcase
        end
    end

endmodule


