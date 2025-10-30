// ------------------------------------------------------------------
// GFP8 BCV Loop Controller - Dual-FSM Ping-Pong v2
//
// Purpose: Orchestrate BxCxV nested loops with overlapped fill and compute
// Algorithm: For each (b,c): accumulate V Native Vector dot products
//
// Architecture: Dual FSM with Ping-Pong Buffering
//   Fill FSM:    Manages buffer filling (producer)
//   Compute FSM: Manages computation (consumer)
//   Handshake:   Simple 2-flag protocol (ping_ready, pong_ready)
//
// Performance:
//   First V:     10 cycles (5 fill + 4 compute + 1 accum)
//   Subsequent:  6 cycles (overlapped: max(5 fill, 4 compute) + 1 accum)
//   Total:       6V + 4 cycles per BxC result (~40% faster than single-FSM)
//
// Key Improvements over v1:
//   - Explicit state sharing (comp_b_idx, comp_c_idx shared with Fill FSM)
//   - Simple 2-flag handshake (removed filling_ping/pong flags)
//   - Backpressure protection (fill_v_idx limited to comp_v_idx + 1)
//   - B,C transition sync (new_bc_pair_flag for explicit coordination)
//
// Author: v2 redesign based on v1 failure analysis
// Date: Thu Oct 30 2025
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
    input  logic [8:0]  i_left_base_addr,     // Base address for left matrix in tile_bram
    input  logic [8:0]  i_right_base_addr,    // Base address for right matrix in tile_bram
    output logic        o_tile_done,

    // BRAM Mantissa Read Interface (to tile_bram)
    output logic [8:0]   o_man_left_rd_addr,
    output logic         o_man_left_rd_en,
    input  logic [255:0] i_man_left_rd_data,

    output logic [8:0]   o_man_right_rd_addr,
    output logic         o_man_right_rd_en,
    input  logic [255:0] i_man_right_rd_data,

    // Exponent Read Interface
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
    // Dual State Machine Definitions
    // ===================================================================
    
    // Fill FSM: Producer
    typedef enum logic {
        FILL_IDLE   = 1'b0,
        FILL_ACTIVE = 1'b1
    } fill_state_t;
    fill_state_t fill_state_reg, fill_state_next;
    
    // Compute FSM: Consumer
    typedef enum logic [2:0] {
        COMP_IDLE   = 3'd0,
        COMP_NV     = 3'd1,
        COMP_ACCUM  = 3'd2,
        COMP_RETURN = 3'd3,
        COMP_DONE   = 3'd4
    } comp_state_t;
    comp_state_t comp_state_reg, comp_state_next;
    
    // ===================================================================
    // Loop Indices - Shared between FSMs
    // ===================================================================
    
    // Compute FSM's loop counters (shared with Fill FSM for address generation)
    logic [7:0] comp_b_idx;  // Current batch index
    logic [7:0] comp_c_idx;  // Current column index
    logic [7:0] comp_v_idx;  // Current vector index
    
    // Fill FSM's independent V counter (always comp_v_idx or comp_v_idx+1)
    logic [7:0] fill_v_idx;  // Which V iteration Fill FSM is working on
    
    // Dimension registers
    logic [7:0] dim_b_reg, dim_c_reg, dim_v_reg;
    logic [8:0] left_base_reg, right_base_reg;
    
    // Tile enable edge detection
    logic i_tile_en_prev;
    logic i_tile_en_rising;
    assign i_tile_en_rising = i_tile_en && !i_tile_en_prev;
    
    // ===================================================================
    // Ping-Pong Handshake (Simple 2-flag protocol)
    // ===================================================================
    logic ping_ready;  // Producer sets, Consumer clears
    logic pong_ready;  // Producer sets, Consumer clears
    
    // Synchronization flag for B,C transitions
    logic new_bc_pair_flag;  // Pulsed when Compute FSM starts new (b,c) pair
    
    // ===================================================================
    // Ping-Pong Buffer Storage
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
    
    // Active buffer mux (selected by Compute FSM)
    logic use_pong;  // 0=use PING, 1=use PONG
    logic [31:0]  nv_left_exp_active;
    logic [255:0] nv_left_man_active [0:3];
    logic [31:0]  nv_right_exp_active;
    logic [255:0] nv_right_man_active [0:3];
    
    // Buffer selection mux (combinational based on ready flags and state)
    // CRITICAL: Must select buffer combinationally when entering COMP_NV
    logic use_pong_comb;
    always_comb begin
        // Select buffer based on current state and ready flags
        if (comp_state_reg == COMP_IDLE && comp_state_next == COMP_NV) begin
            // Transitioning to COMP_NV - select based on ready flags
            use_pong_comb = pong_ready ? 1'b1 : 1'b0;
        end else begin
            // Already computing - use registered selection
            use_pong_comb = use_pong;
        end
        
        if (use_pong_comb) begin
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
    
    // Fill control
    logic fill_target;  // 0=fill PING, 1=fill PONG
    logic [2:0] fill_cycle;  // 0-4 for 5-cycle fill
    
    // ===================================================================
    // NV Dot Product Instance
    // ===================================================================
    logic signed [31:0] nv_dot_mantissa;
    logic signed [7:0]  nv_dot_exponent;
    
    // Enable signal: pulse when entering COMP_NV
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
    
    // Compute pipeline counter
    logic [2:0] compute_wait;
    
    // Tile completion flag
    logic tile_complete;
    
    // ===================================================================
    // Fill FSM - Next State Logic
    // ===================================================================
    always_comb begin
        fill_state_next = fill_state_reg;
        
        case (fill_state_reg)
            FILL_IDLE: begin
                // Start filling if:
                // 1. Have more V iterations to fill (fill_v_idx < dim_v_reg)
                // 2. Not too far ahead (fill_v_idx <= comp_v_idx + 1)
                // 3. Target buffer is not ready (has been consumed or never filled)
                
                automatic logic can_fill_ping;
                automatic logic can_fill_pong;
                automatic logic should_fill;
                
                can_fill_ping = !ping_ready && (fill_v_idx < dim_v_reg) && (fill_v_idx <= comp_v_idx + 1);
                can_fill_pong = !pong_ready && (fill_v_idx < dim_v_reg) && (fill_v_idx <= comp_v_idx + 1);
                should_fill = can_fill_ping || can_fill_pong;
                
                if (should_fill) begin
                    fill_state_next = FILL_ACTIVE;
                end
            end
            
            FILL_ACTIVE: begin
                // Fill completes after cycle 4
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
                // Wait for ready buffer (but not if tile is complete)
                if ((ping_ready || pong_ready) && !tile_complete) begin
                    comp_state_next = COMP_NV;
                end
            end
            
            COMP_NV: begin
                // Wait for 4-cycle pipeline
                if (compute_wait == 3'd3) begin
                    comp_state_next = COMP_ACCUM;
                end
            end
            
            COMP_ACCUM: begin
                // Check if V loop complete
                if (comp_v_idx >= dim_v_reg - 1) begin
                    comp_state_next = COMP_RETURN;
                end else begin
                    comp_state_next = COMP_IDLE;
                end
            end
            
            COMP_RETURN: begin
                // Calculate next B,C indices to check for completion
                logic [7:0] next_b_idx, next_c_idx;
                if (comp_c_idx >= dim_c_reg - 1) begin
                    next_c_idx = 8'd0;
                    next_b_idx = comp_b_idx + 1;
                end else begin
                    next_c_idx = comp_c_idx + 1;
                    next_b_idx = comp_b_idx;
                end
                
                // Check if we've processed all BxC pairs
                // Current indices (comp_b_idx, comp_c_idx) were just processed
                // If we're at the last pair, we're done
                if (comp_b_idx >= dim_b_reg - 1 && comp_c_idx >= dim_c_reg - 1) begin
                    comp_state_next = COMP_DONE;
                end else begin
                    comp_state_next = COMP_IDLE;
                end
            end
            
            COMP_DONE: begin
                $display("[BCV_LOOP] COMP_DONE state reached!");
                comp_state_next = COMP_IDLE;
            end
        endcase
    end
    
    // ===================================================================
    // Dual FSM Sequential Logic
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
    // BRAM Read Address Generation (Fill FSM)
    // ===================================================================
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
        
        // BRAM reads for filling buffers
        if (fill_state_reg == FILL_ACTIVE && fill_cycle <= 3'd3) begin
            // Calculate NV indices using COMPUTE FSM's b,c and FILL FSM's v
            automatic logic [15:0] left_nv_index;
            automatic logic [15:0] right_nv_index;
            automatic logic [15:0] left_base_nv;
            automatic logic [15:0] right_base_nv;
            automatic logic [8:0] left_line_addr;
            automatic logic [8:0] right_line_addr;
            
            // Convert base from line to NV units (divide by 4)
            left_base_nv = {9'd0, left_base_reg[8:2]};
            right_base_nv = {9'd0, right_base_reg[8:2]};
            
            // CRITICAL: Use comp_b_idx, comp_c_idx (not fill's own)
            // This ensures addresses are correct during B,C transitions
            left_nv_index = left_base_nv + ({8'd0, comp_b_idx} * {8'd0, dim_v_reg} + {8'd0, fill_v_idx});
            right_nv_index = right_base_nv + ({8'd0, comp_c_idx} * {8'd0, dim_v_reg} + {8'd0, fill_v_idx});
            
            // Convert to line address
            left_line_addr = {left_nv_index[6:0], 2'b00} + {7'd0, fill_cycle[1:0]};
            right_line_addr = {right_nv_index[6:0], 2'b00} + {7'd0, fill_cycle[1:0]};
            
            // Combinational assignment
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
    // Combined Fill + Compute FSM Logic (Single always_ff to avoid multiple drivers)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            // Fill FSM signals
            fill_cycle <= 3'd0;
            fill_target <= 1'b0;
            fill_v_idx <= 8'd0;
            ping_ready <= 1'b0;
            pong_ready <= 1'b0;
            
            // Compute FSM signals
            compute_wait <= 3'd0;
            use_pong <= 1'b0;
            new_bc_pair_flag <= 1'b0;
            
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
            // Sync with Compute FSM on B,C transitions (CHECK BEFORE CLEARING FLAG!)
            if (new_bc_pair_flag) begin
                fill_v_idx <= 8'd0;  // Reset for new (b,c) pair
                `ifdef SIMULATION
                $display("[PINGPONG_FILL] @%0t BC_SYNC: fill_v_idx reset to 0 (new b=%0d, c=%0d)", 
                         $time, comp_b_idx, comp_c_idx);
                `endif
            end
            
            // Startup trigger
            if (i_tile_en_rising) begin
                fill_v_idx <= 8'd0;
                ping_ready <= 1'b0;
                pong_ready <= 1'b0;
                `ifdef SIMULATION
                $display("[PINGPONG_FILL] @%0t TILE_START: Resetting all", $time);
                `endif
            end
            
            // ============================================================
            // FILL FSM LOGIC
            // ============================================================
            case (fill_state_reg)
                FILL_IDLE: begin
                    // Determine target buffer (prefer PING for determinism)
                    if (!ping_ready && fill_v_idx < dim_v_reg && fill_v_idx <= comp_v_idx + 1) begin
                        fill_target <= 1'b0;  // Fill PING
                        fill_cycle <= 3'd0;
                        `ifdef SIMULATION
                        $display("[PINGPONG_FILL] @%0t IDLE: Starting PING fill (V=%0d, comp_v=%0d)", 
                                 $time, fill_v_idx, comp_v_idx);
                        `endif
                    end else if (!pong_ready && fill_v_idx < dim_v_reg && fill_v_idx <= comp_v_idx + 1) begin
                        fill_target <= 1'b1;  // Fill PONG
                        fill_cycle <= 3'd0;
                        `ifdef SIMULATION
                        $display("[PINGPONG_FILL] @%0t IDLE: Starting PONG fill (V=%0d, comp_v=%0d)", 
                                 $time, fill_v_idx, comp_v_idx);
                        `endif
                    end
                end
                
                FILL_ACTIVE: begin
                    // 5-cycle fill (cycles 0→1→2→3→4)
                    if (fill_cycle == 3'd0) begin
                        // Cycle 0: Start BRAM reads (data arrives next cycle)
                        fill_cycle <= fill_cycle + 1;
                        `ifdef SIMULATION
                        $display("[PINGPONG_FILL] @%0t Cycle 0: Starting BRAM reads for %s (V=%0d)", 
                                 $time, fill_target ? "PONG" : "PING", fill_v_idx);
                        `endif
                    end else if (fill_cycle == 3'd1) begin
                        // Capture G0
                        if (fill_target == 1'b0) begin
                            nv_left_exp_ping[7:0] <= i_exp_left_rd_data;
                            nv_right_exp_ping[7:0] <= i_exp_right_rd_data;
                            nv_left_man_ping[0] <= i_man_left_rd_data;
                            nv_right_man_ping[0] <= i_man_right_rd_data;
                            `ifdef SIMULATION
                            $display("[PINGPONG_FILL] @%0t Cycle 1: Captured PING[0]=%h", 
                                     $time, i_man_left_rd_data[255:224]);
                            `endif
                        end else begin
                            nv_left_exp_pong[7:0] <= i_exp_left_rd_data;
                            nv_right_exp_pong[7:0] <= i_exp_right_rd_data;
                            nv_left_man_pong[0] <= i_man_left_rd_data;
                            nv_right_man_pong[0] <= i_man_right_rd_data;
                            `ifdef SIMULATION
                            $display("[PINGPONG_FILL] @%0t Cycle 1: Captured PONG[0]=%h", 
                                     $time, i_man_left_rd_data[255:224]);
                            `endif
                        end
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 3'd2) begin
                        // Capture G1
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
                        // Capture G2
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
                        // Capture G3, set ready flag, advance fill_v_idx
                        if (fill_target == 1'b0) begin
                            nv_left_exp_ping[31:24] <= i_exp_left_rd_data;
                            nv_right_exp_ping[31:24] <= i_exp_right_rd_data;
                            nv_left_man_ping[3] <= i_man_left_rd_data;
                            nv_right_man_ping[3] <= i_man_right_rd_data;
                            ping_ready <= 1'b1;  // PRODUCER sets ready
                            `ifdef SIMULATION
                            $display("[PINGPONG_FILL] @%0t ACTIVE: PING ready (V=%0d)", $time, fill_v_idx);
                            `endif
                        end else begin
                            nv_left_exp_pong[31:24] <= i_exp_left_rd_data;
                            nv_right_exp_pong[31:24] <= i_exp_right_rd_data;
                            nv_left_man_pong[3] <= i_man_left_rd_data;
                            nv_right_man_pong[3] <= i_man_right_rd_data;
                            pong_ready <= 1'b1;  // PRODUCER sets ready
                            `ifdef SIMULATION
                            $display("[PINGPONG_FILL] @%0t ACTIVE: PONG ready (V=%0d)", $time, fill_v_idx);
                            `endif
                        end
                        fill_cycle <= 3'd0;
                        // Advance fill V index (only if not at BC transition boundary)
                        if (!new_bc_pair_flag) begin
                            fill_v_idx <= fill_v_idx + 1;
                        end
                    end
                end
            endcase
            
            // ============================================================
            // COMPUTE FSM LOGIC (in same always_ff block)
            // ============================================================
            case (comp_state_reg)
                COMP_IDLE: begin
                    compute_wait <= 3'd0;
                    // Select buffer when transitioning to COMP_NV
                    if (comp_state_next == COMP_NV) begin
                        // Prefer PONG if both ready (but either is fine)
                        use_pong <= pong_ready ? 1'b1 : 1'b0;
                        `ifdef SIMULATION
                        $display("[PINGPONG_COMP] @%0t IDLE: Select %s (ping=%b, pong=%b, V=%0d)", 
                                 $time, pong_ready ? "PONG" : "PING", ping_ready, pong_ready, comp_v_idx);
                        `endif
                    end
                end
                
                COMP_NV: begin
                    // Clear ready flag on FIRST cycle when starting compute
                    if (compute_wait == 3'd0) begin
                        if (use_pong) begin
                            pong_ready <= 1'b0;
                            `ifdef SIMULATION
                            $display("[PINGPONG_COMP] @%0t NV START: Clear pong_ready (V=%0d)", $time, comp_v_idx);
                            `endif
                        end else begin
                            ping_ready <= 1'b0;
                            `ifdef SIMULATION
                            $display("[PINGPONG_COMP] @%0t NV START: Clear ping_ready (V=%0d)", $time, comp_v_idx);
                            `endif
                        end
                    end
                    if (compute_wait < 3'd3) begin
                        compute_wait <= compute_wait + 1;
                    end
                end
                
                COMP_ACCUM: begin
                    // Reset compute wait for next iteration
                    compute_wait <= 3'd0;
                end
                
                COMP_RETURN: begin
                    // Signal new (b,c) pair to Fill FSM (only if not done)
                    if (comp_state_next == COMP_IDLE) begin
                        new_bc_pair_flag <= 1'b1;
                        `ifdef SIMULATION
                        $display("[PINGPONG_COMP] @%0t RETURN: New BC pair signal (b=%0d, c=%0d)", 
                                 $time, comp_b_idx, comp_c_idx);
                        `endif
                    end
                end
                
                default: begin
                    compute_wait <= 3'd0;
                end
            endcase
            
            // Clear BC sync flag at the END (after both FSMs have seen it)
            if (comp_state_reg != COMP_RETURN) begin
                new_bc_pair_flag <= 1'b0;
            end
        end
    end
    
    // ===================================================================
    // V-Loop Accumulation (Compute FSM)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            accum_mantissa <= 32'sd0;
            accum_exponent <= 8'sd0;
        end else begin
            case (comp_state_reg)
                COMP_IDLE: begin
                    // Reset accumulator when starting new (b,c) pair
                    if (comp_v_idx == 8'd0 && comp_state_next == COMP_NV) begin
                        accum_mantissa <= 32'sd0;
                        accum_exponent <= 8'sd0;
                    end
                end
                
                COMP_ACCUM: begin
                    if (comp_v_idx == 8'd0) begin
                        // First V iteration: initialize
                        accum_mantissa <= nv_dot_mantissa;
                        accum_exponent <= nv_dot_exponent;
                        `ifdef SIMULATION
                        $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d INIT: mant=%0d, exp=%0d",
                                 $time, comp_b_idx, comp_c_idx, comp_v_idx, nv_dot_mantissa, nv_dot_exponent);
                        `endif
                    end else begin
                        // Accumulate with exponent alignment
                        automatic logic signed [7:0] max_exp;
                        automatic logic [7:0] exp_diff_accum, exp_diff_dot;
                        automatic logic signed [31:0] aligned_accum, aligned_dot;
                        automatic logic signed [31:0] sum_mantissa;
                        
                        // Find max exponent
                        max_exp = ($signed(accum_exponent) > $signed(nv_dot_exponent)) ? 
                                  accum_exponent : nv_dot_exponent;
                        
                        // Align mantissas
                        exp_diff_accum = max_exp - accum_exponent;
                        exp_diff_dot = max_exp - nv_dot_exponent;
                        
                        aligned_accum = (exp_diff_accum > 31) ? 32'sd0 : 
                                       ($signed(accum_mantissa) >>> exp_diff_accum);
                        aligned_dot = (exp_diff_dot > 31) ? 32'sd0 : 
                                     ($signed(nv_dot_mantissa) >>> exp_diff_dot);
                        
                        sum_mantissa = aligned_accum + aligned_dot;
                        
                        accum_mantissa <= sum_mantissa;
                        accum_exponent <= max_exp;
                        `ifdef SIMULATION
                        $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d ADD: sum=%0d, exp=%0d",
                                 $time, comp_b_idx, comp_c_idx, comp_v_idx, sum_mantissa, max_exp);
                        `endif
                    end
                end
                
                COMP_RETURN: begin
                    // Reset for next (b,c) pair
                    accum_mantissa <= 32'sd0;
                    accum_exponent <= 8'sd0;
                end
            endcase
        end
    end
    
    // ===================================================================
    // Loop Index Control (Compute FSM)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            comp_b_idx <= 8'd0;
            comp_c_idx <= 8'd0;
            comp_v_idx <= 8'd0;
            dim_b_reg <= 8'd0;
            dim_c_reg <= 8'd0;
            dim_v_reg <= 8'd0;
            left_base_reg <= 9'd0;
            right_base_reg <= 9'd0;
            i_tile_en_prev <= 1'b0;
            tile_complete <= 1'b0;
        end else begin
            i_tile_en_prev <= i_tile_en;
            
            if (i_tile_en_rising) begin
                // Capture dimensions
                dim_b_reg <= i_dim_b;
                dim_c_reg <= i_dim_c;
                dim_v_reg <= i_dim_v;
                left_base_reg <= i_left_base_addr;
                right_base_reg <= i_right_base_addr;
                // Initialize indices
                comp_b_idx <= 8'd0;
                comp_c_idx <= 8'd0;
                comp_v_idx <= 8'd0;
                // Clear tile complete flag for new tile
                tile_complete <= 1'b0;
                $display("[BCV_LOOP] @%0t NEW TILE: B=%0d, C=%0d, V=%0d", 
                         $time, i_dim_b, i_dim_c, i_dim_v);
            end
            
            case (comp_state_reg)
                COMP_ACCUM: begin
                    // Advance V index
                    comp_v_idx <= comp_v_idx + 1;
                    $display("[BCV_LOOP] ACCUM: b=%0d, c=%0d, v=%0d -> v=%0d", 
                             comp_b_idx, comp_c_idx, comp_v_idx, comp_v_idx + 1);
                end
                
                COMP_RETURN: begin
                    // Reset V, advance C and B
                    comp_v_idx <= 8'd0;
                    
                    $display("[BCV_LOOP] RETURN: b=%0d, c=%0d complete (dim_b=%0d, dim_c=%0d)", 
                             comp_b_idx, comp_c_idx, dim_b_reg, dim_c_reg);
                    
                    if (!(comp_c_idx >= dim_c_reg - 1 && comp_b_idx >= dim_b_reg - 1)) begin
                        if (comp_c_idx >= dim_c_reg - 1) begin
                            comp_c_idx <= 8'd0;
                            comp_b_idx <= comp_b_idx + 1;
                            $display("[BCV_LOOP]   -> Next: b=%0d, c=0", comp_b_idx + 1);
                        end else begin
                            comp_c_idx <= comp_c_idx + 1;
                            $display("[BCV_LOOP]   -> Next: b=%0d, c=%0d", comp_b_idx, comp_c_idx + 1);
                        end
                    end else begin
                        $display("[BCV_LOOP]   -> DONE (should transition to COMP_DONE)");
                    end
                end
            endcase
        end
    end
    
    // ===================================================================
    // Output Control (Compute FSM)
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
                    // Output result
                    o_result_mantissa <= accum_mantissa;
                    o_result_exponent <= accum_exponent;
                    o_result_valid <= 1'b1;
                    `ifdef SIMULATION
                    $display("[BCV_RESULT] @%0t [B%0d,C%0d] RETURN: mant=%0d, exp=%0d",
                             $time, comp_b_idx, comp_c_idx, accum_mantissa, accum_exponent);
                    `endif
                end
                
                COMP_DONE: begin
                    o_tile_done <= 1'b1;
                    tile_complete <= 1'b1;
                    // Clear ready flags to prevent restart
                    ping_ready <= 1'b0;
                    pong_ready <= 1'b0;
                    // Indices will reset on next tile_en rising edge
                end
            endcase
        end
    end

endmodule

