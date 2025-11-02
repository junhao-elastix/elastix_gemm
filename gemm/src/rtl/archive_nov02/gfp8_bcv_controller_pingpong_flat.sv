// gfp8_bcv_controller_pingpong_flat.sv
//
// BCV Loop Controller with Ping-Pong Buffering and FLATTENED loops
// 
// Instead of nested B, C, V loops, uses a single flat counter and derives indices
// This simplifies the state machine and removes the need for complex loop management
//
// Key improvements:
//   - Single flat counter for all iterations
//   - Derived B, C, V indices using division/modulo
//   - Simplified state machine (no COMP_RETURN needed)
//   - Cleaner ping-pong buffer management

module gfp8_bcv_controller_pingpong_flat #(
    parameter NV_WIDTH = 128  // Native Vector width (pairs of GFP8 values)
)(
    input  logic        i_clk,
    input  logic        i_reset_n,
    
    // TILE Command Interface
    input  logic        i_tile_en,
    input  logic [7:0]  i_dim_b,              // Output rows (batch)
    input  logic [7:0]  i_dim_c,              // Output columns
    input  logic [7:0]  i_dim_v,              // V dimension (contracting)
    input  logic [8:0]  i_left_base_addr,     // Base address for left matrix in tile_bram
    input  logic [8:0]  i_right_base_addr,    // Base address for right matrix in tile_bram
    output logic        o_tile_done,

    // Native Vector Read Interface (to tile_bram)
    output logic [6:0]   o_nv_left_rd_idx,      // NV index [0-127]
    input  logic [31:0]  i_nv_left_exp,         // Packed exponents
    input  logic [255:0] i_nv_left_man [0:3],   // 4 mantissa groups
    
    output logic [6:0]   o_nv_right_rd_idx,     // NV index [0-127]
    input  logic [31:0]  i_nv_right_exp,        // Packed exponents
    input  logic [255:0] i_nv_right_man [0:3],  // 4 mantissa groups

    // Output Result Interface
    output logic signed [31:0] o_result_mantissa,
    output logic signed [7:0]  o_result_exponent,
    output logic               o_result_valid
);

    // ===================================================================
    // State Machine Definitions
    // ===================================================================
    
    // Fill FSM states (simplified)
    typedef enum logic [1:0] {
        FILL_IDLE,
        FILL_ACTIVE
    } fill_state_t;
    
    // Compute FSM states (simplified - no COMP_RETURN needed!)
    typedef enum logic [2:0] {
        COMP_IDLE,
        COMP_NV,       // 4-cycle compute
        COMP_ACCUM,    // Accumulate and advance
        COMP_DONE      // All iterations complete
    } comp_state_t;
    
    fill_state_t fill_state_reg, fill_state_next;
    comp_state_t comp_state_reg, comp_state_next;
    
    // ===================================================================
    // Flattened Loop Management
    // ===================================================================
    
    // Single flat counter for all iterations
    logic [23:0] flat_idx;        // Current flattened index (up to 256*256*256)
    logic [23:0] total_iters;      // Total iterations = B * C * V
    
    // Dimension registers
    logic [7:0] dim_b_reg, dim_c_reg, dim_v_reg;
    logic [8:0] left_base_reg, right_base_reg;
    
    // Derived indices (combinational)
    logic [7:0] comp_b_idx, comp_c_idx, comp_v_idx;
    logic [15:0] bc_product;  // B * C for division
    
    // Flatten index derivation (combinational)
    always_comb begin
        // flat_idx = b * (C * V) + c * V + v  (B-outer, C-inner, row-major)
        // To extract: 
        //   v = flat_idx % V
        //   c = (flat_idx / V) % C
        //   b = flat_idx / (C * V)
        
        automatic logic [23:0] temp_idx = flat_idx;
        automatic logic [15:0] cv_product = {8'd0, dim_c_reg} * {8'd0, dim_v_reg};
        
        // Extract indices
        comp_v_idx = temp_idx % dim_v_reg;
        temp_idx = temp_idx / dim_v_reg;
        comp_c_idx = temp_idx % dim_c_reg;
        comp_b_idx = temp_idx / dim_c_reg;
    end
    
    // Fill FSM's flat index (can be ahead by 1)
    logic [23:0] fill_flat_idx;
    logic [7:0] fill_b_idx, fill_c_idx, fill_v_idx;
    
    // Derive fill indices
    always_comb begin
        automatic logic [23:0] temp_idx = fill_flat_idx;
        
        fill_v_idx = temp_idx % dim_v_reg;
        temp_idx = temp_idx / dim_v_reg;
        fill_c_idx = temp_idx % dim_c_reg;
        fill_b_idx = temp_idx / dim_c_reg;
    end
    
    // ===================================================================
    // Ping-Pong Buffer Storage
    // ===================================================================
    
    // PING buffer (256-bit * 4 for mantissas, 32-bit for exponents)
    logic [31:0]  nv_left_exp_ping;
    logic [255:0] nv_left_man_ping [0:3];
    logic [31:0]  nv_right_exp_ping;
    logic [255:0] nv_right_man_ping [0:3];
    
    // PONG buffer
    logic [31:0]  nv_left_exp_pong;
    logic [255:0] nv_left_man_pong [0:3];
    logic [31:0]  nv_right_exp_pong;
    logic [255:0] nv_right_man_pong [0:3];
    
    // Buffer ready flags
    logic ping_ready, pong_ready;
    
    // Buffer selection for compute
    logic use_pong;  // 0=use PING, 1=use PONG
    logic [31:0]  nv_left_exp_active;
    logic [255:0] nv_left_man_active [0:3];
    logic [31:0]  nv_right_exp_active;
    logic [255:0] nv_right_man_active [0:3];
    
    // Buffer selection mux (combinational based on ready flags and state)
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
    
    // ===================================================================
    // NV Dot Product Instance
    // ===================================================================
    logic nv_dot_input_valid;
    logic signed [31:0] nv_dot_mantissa;
    logic signed [7:0]  nv_dot_exponent;
    
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
    
    // V-Loop Accumulator
    logic signed [31:0] accum_mantissa;
    logic signed [7:0]  accum_exponent;
    
    // Compute pipeline counter
    logic [2:0] compute_wait;
    
    // Tile completion flag
    logic tile_complete;
    
    // Tile enable edge detection
    logic i_tile_en_prev;
    logic i_tile_en_rising;
    assign i_tile_en_rising = i_tile_en && !i_tile_en_prev;
    
    // ===================================================================
    // Fill FSM - Next State Logic
    // ===================================================================
    always_comb begin
        // Force reset on tile enable rising edge
        if (i_tile_en_rising) begin
            fill_state_next = FILL_IDLE;
        end else begin
            fill_state_next = fill_state_reg;
            
            case (fill_state_reg)
            FILL_IDLE: begin
                // Start filling if:
                // 1. Have more iterations to fill
                // 2. Not too far ahead (at most 1 ahead of compute)
                // 3. Target buffer is not ready
                
                automatic logic can_fill_ping;
                automatic logic can_fill_pong;
                automatic logic should_fill;
                
                can_fill_ping = !ping_ready && (fill_flat_idx < total_iters) && 
                               (fill_flat_idx <= flat_idx + 1);
                can_fill_pong = !pong_ready && (fill_flat_idx < total_iters) && 
                               (fill_flat_idx <= flat_idx + 1);
                should_fill = can_fill_ping || can_fill_pong;
                
                if (should_fill) begin
                    fill_state_next = FILL_ACTIVE;
                end
            end
            
            FILL_ACTIVE: begin
                // Single-cycle fill - immediately return to IDLE
                fill_state_next = FILL_IDLE;
            end
            endcase
        end
    end
    
    // ===================================================================
    // Compute FSM - Next State Logic (Simplified!)
    // ===================================================================
    always_comb begin
        // Force reset on tile enable rising edge
        if (i_tile_en_rising) begin
            comp_state_next = COMP_IDLE;
        end else begin
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
                // Check if all iterations complete
                if (flat_idx >= total_iters - 1) begin
                    comp_state_next = COMP_DONE;
                end else begin
                    comp_state_next = COMP_IDLE;
                end
            end
            
            COMP_DONE: begin
                // $display("[BCV_FLAT] COMP_DONE state reached!");
                comp_state_next = COMP_IDLE;
            end
            endcase
        end
    end
    
    // ===================================================================
    // Dual FSM Sequential Logic (Combined in single always_ff)
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
    // NV Index Generation (Combinational)
    // ===================================================================
    logic [6:0] fill_left_nv_idx;
    logic [6:0] fill_right_nv_idx;
    
    always_comb begin
        // Convert base addresses from line to NV units (divide by 4)
        automatic logic [6:0] left_base_nv = left_base_reg[8:2];
        automatic logic [6:0] right_base_nv = right_base_reg[8:2];
        
        // Calculate NV indices for current fill iteration
        fill_left_nv_idx = left_base_nv + (fill_b_idx * dim_v_reg + fill_v_idx);
        fill_right_nv_idx = right_base_nv + (fill_c_idx * dim_v_reg + fill_v_idx);
        
        // Output NV indices to tile_bram (combinational read)
        o_nv_left_rd_idx = fill_left_nv_idx;
        o_nv_right_rd_idx = fill_right_nv_idx;
        
        // `ifdef SIMULATION
        // if (fill_state_reg == FILL_ACTIVE) begin
        //     $display("[NV_IDX] @%0t Left NV[%0d], Right NV[%0d] for B=%0d, C=%0d, V=%0d", 
        //              $time, fill_left_nv_idx, fill_right_nv_idx, fill_b_idx, fill_c_idx, fill_v_idx);
        // end
        // `endif
    end
    
    // ===================================================================
    // Main Sequential Logic
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            // Reset all state
            flat_idx <= 24'd0;
            fill_flat_idx <= 24'd0;
            total_iters <= 24'd0;
            
            fill_target <= 1'b0;
            
            ping_ready <= 1'b0;
            pong_ready <= 1'b0;
            
            compute_wait <= 3'd0;
            use_pong <= 1'b0;
            
            // Initialize buffers
            nv_left_exp_ping <= 32'd0;
            nv_right_exp_ping <= 32'd0;
            for (int i = 0; i < 4; i++) begin
                nv_left_man_ping[i] <= 256'd0;
                nv_right_man_ping[i] <= 256'd0;
            end
            
            nv_left_exp_pong <= 32'd0;
            nv_right_exp_pong <= 32'd0;
            for (int i = 0; i < 4; i++) begin
                nv_left_man_pong[i] <= 256'd0;
                nv_right_man_pong[i] <= 256'd0;
            end
            
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
                // Capture dimensions and reset state for new tile
                dim_b_reg <= i_dim_b;
                dim_c_reg <= i_dim_c;
                dim_v_reg <= i_dim_v;
                left_base_reg <= i_left_base_addr;
                right_base_reg <= i_right_base_addr;
                
                // Calculate total iterations
                total_iters <= {8'd0, i_dim_b} * {8'd0, i_dim_c} * {8'd0, i_dim_v};
                
                // Reset indices
                flat_idx <= 24'd0;
                fill_flat_idx <= 24'd0;
                
                // Clear tile complete flag for new tile
                tile_complete <= 1'b0;
                
                // Note: FSM state reset is handled in combinational next-state logic
                // via i_tile_en_rising signal
                
                // Reset buffers
                ping_ready <= 1'b0;
                pong_ready <= 1'b0;
                
                // `ifdef SIMULATION
                // $display("[BCV_FLAT] @%0t NEW TILE: B=%0d, C=%0d, V=%0d (total=%0d iters)", 
                //          $time, i_dim_b, i_dim_c, i_dim_v, 
                //          {8'd0, i_dim_b} * {8'd0, i_dim_c} * {8'd0, i_dim_v});
                // `endif
            end
            
            // No BC synchronization needed in flattened loop
            // Fill just continues ahead of compute by at most 1
            
            // ============================================================
            // FILL FSM LOGIC
            // ============================================================
            case (fill_state_reg)
                FILL_IDLE: begin
                    // Determine target buffer (prefer PING for determinism)
                    if (!ping_ready && fill_flat_idx < total_iters && 
                        fill_flat_idx <= flat_idx + 1) begin
                        fill_target <= 1'b0;  // Fill PING
                        // `ifdef SIMULATION
                        // $display("[PINGPONG_FILL] @%0t IDLE: Starting PING fill (flat=%0d)", 
                        //          $time, fill_flat_idx);
                        // `endif
                    end else if (!pong_ready && fill_flat_idx < total_iters && 
                                fill_flat_idx <= flat_idx + 1) begin
                        fill_target <= 1'b1;  // Fill PONG
                        // `ifdef SIMULATION
                        // $display("[PINGPONG_FILL] @%0t IDLE: Starting PONG fill (flat=%0d)", 
                        //          $time, fill_flat_idx);
                        // `endif
                    end
                end
                
                FILL_ACTIVE: begin
                    // SINGLE-CYCLE FILL - Read complete NV from tile_bram
                    if (fill_target == 1'b0) begin  // Fill PING
                        // Read complete NV from tile_bram in one cycle
                        nv_left_exp_ping <= i_nv_left_exp;     // From tile_bram NV port
                        nv_left_man_ping <= i_nv_left_man;     // From tile_bram NV port
                        nv_right_exp_ping <= i_nv_right_exp;
                        nv_right_man_ping <= i_nv_right_man;
                        ping_ready <= 1'b1;
                        
                        // `ifdef SIMULATION
                        // $display("[PINGPONG_FILL] @%0t SINGLE-CYCLE: PING ready (flat=%0d)", 
                        //          $time, fill_flat_idx);
                        // $display("  Left NV[%0d]: exp=0x%08x", fill_left_nv_idx, i_nv_left_exp);
                        // $display("  Right NV[%0d]: exp=0x%08x", fill_right_nv_idx, i_nv_right_exp);
                        // `endif
                    end else begin  // Fill PONG
                        nv_left_exp_pong <= i_nv_left_exp;
                        nv_left_man_pong <= i_nv_left_man;
                        nv_right_exp_pong <= i_nv_right_exp;
                        nv_right_man_pong <= i_nv_right_man;
                        pong_ready <= 1'b1;
                        
                        // `ifdef SIMULATION
                        // $display("[PINGPONG_FILL] @%0t SINGLE-CYCLE: PONG ready (flat=%0d)", 
                        //          $time, fill_flat_idx);
                        // $display("  Left NV[%0d]: exp=0x%08x", fill_left_nv_idx, i_nv_left_exp);
                        // $display("  Right NV[%0d]: exp=0x%08x", fill_right_nv_idx, i_nv_right_exp);
                        // `endif
                    end
                    
                    // Advance to next iteration immediately
                    fill_flat_idx <= fill_flat_idx + 1;
                    // Return to IDLE (no more multi-cycle wait)
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
                        // `ifdef SIMULATION
                        // $display("[PINGPONG_COMP] @%0t IDLE: Select %s (ping=%b, pong=%b, flat=%0d)", 
                        //          $time, pong_ready ? "PONG" : "PING", ping_ready, pong_ready, flat_idx);
                        // `endif
                    end
                end
                
                COMP_NV: begin
                    // Clear ready flag on FIRST cycle when starting compute
                    if (compute_wait == 3'd0) begin
                        if (use_pong) begin
                            pong_ready <= 1'b0;
                            // `ifdef SIMULATION
                            // $display("[PINGPONG_COMP] @%0t NV START: Clear pong_ready (flat=%0d)", 
                            //          $time, flat_idx);
                            // `endif
                        end else begin
                            ping_ready <= 1'b0;
                            // `ifdef SIMULATION
                            // $display("[PINGPONG_COMP] @%0t NV START: Clear ping_ready (flat=%0d)", 
                            //          $time, flat_idx);
                            // `endif
                        end
                    end
                    compute_wait <= compute_wait + 1;
                end
                
                COMP_ACCUM: begin
                    // Advance flat index
                    flat_idx <= flat_idx + 1;
                    // Reset compute wait for next iteration
                    compute_wait <= 3'd0;
                    // `ifdef SIMULATION
                    // $display("[BCV_FLAT] ACCUM: flat=%0d -> %0d (b=%0d, c=%0d, v=%0d)", 
                    //          flat_idx, flat_idx + 1, comp_b_idx, comp_c_idx, comp_v_idx);
                    // `endif
                end
                
                COMP_DONE: begin
                    tile_complete <= 1'b1;
                    // Clear ready flags to prevent restart
                    ping_ready <= 1'b0;
                    pong_ready <= 1'b0;
                    // Reset indices
                    flat_idx <= 24'd0;
                    fill_flat_idx <= 24'd0;
                end
            endcase
        end
    end
    
    // ===================================================================
    // NV Dot Control
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            nv_dot_input_valid <= 1'b0;
        end else begin
            // Assert valid during first cycle of COMP_NV
            nv_dot_input_valid <= (comp_state_reg == COMP_NV && compute_wait == 3'd0);
            
            `ifdef SIMULATION
            if (comp_state_reg == COMP_NV && compute_wait == 3'd0) begin
                // $display("[NV_DOT_CAPTURE] @%0t Captured: man_left[0]=0x%064x", 
                //          $time, nv_left_man_active[0]);
            end
            `endif
        end
    end
    
    // ===================================================================
    // V-Loop Accumulator
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            accum_mantissa <= 32'sd0;
            accum_exponent <= 8'sd0;
        end else begin
            case (comp_state_reg)
                COMP_IDLE: begin
                    // Reset accumulator when starting new V=0 iteration
                    if (comp_v_idx == 8'd0 && comp_state_next == COMP_NV) begin
                        accum_mantissa <= 32'sd0;
                        accum_exponent <= 8'sd0;
                    end
                end
                
                COMP_ACCUM: begin
                    // Calculate accumulation result (combinational)
                    automatic logic signed [31:0] new_mantissa;
                    automatic logic signed [7:0] new_exponent;
                    
                    if (comp_v_idx == 8'd0) begin
                        // First V iteration: initialize
                        new_mantissa = nv_dot_mantissa;
                        new_exponent = nv_dot_exponent;
                        
                        accum_mantissa <= new_mantissa;
                        accum_exponent <= new_exponent;
                        
                        // `ifdef SIMULATION
                        // $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d INIT: mant=%0d, exp=%0d",
                        //          $time, comp_b_idx, comp_c_idx, comp_v_idx, 
                        //          new_mantissa, new_exponent);
                        // `endif
                    end else begin
                        // Accumulate with exponent alignment
                        automatic logic signed [7:0] max_exp;
                        automatic logic [7:0] exp_diff_accum, exp_diff_dot;
                        automatic logic signed [31:0] aligned_accum, aligned_dot;
                        
                        // Find larger exponent
                        max_exp = (accum_exponent > nv_dot_exponent) ? 
                                  accum_exponent : nv_dot_exponent;
                        
                        // Calculate shifts needed
                        exp_diff_accum = max_exp - accum_exponent;
                        exp_diff_dot = max_exp - nv_dot_exponent;
                        
                        // Align mantissas (right shift smaller one)
                        aligned_accum = (exp_diff_accum < 32) ? 
                                       (accum_mantissa >>> exp_diff_accum) : 32'sd0;
                        aligned_dot = (exp_diff_dot < 32) ? 
                                     (nv_dot_mantissa >>> exp_diff_dot) : 32'sd0;
                        
                        // Add aligned mantissas
                        new_mantissa = aligned_accum + aligned_dot;
                        new_exponent = max_exp;
                        
                        accum_mantissa <= new_mantissa;
                        accum_exponent <= new_exponent;
                        
                        // `ifdef SIMULATION
                        // $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d ACCUM: mant=%0d + %0d = %0d, exp=%0d",
                        //          $time, comp_b_idx, comp_c_idx, comp_v_idx,
                        //          aligned_accum, aligned_dot, new_mantissa, new_exponent);
                        // `endif
                    end
                end
            endcase
        end
    end
    
    // ===================================================================
    // Output Generation  
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
                COMP_ACCUM: begin
                    // Output result when V loop completes (v reaches V-1)
                    if (comp_v_idx == dim_v_reg - 1) begin
                        // Calculate final accumulated value combinationally
                        automatic logic signed [31:0] final_mantissa;
                        automatic logic signed [7:0] final_exponent;
                        
                        if (comp_v_idx == 8'd0) begin
                            // V=1 or first and last V: use nv_dot directly
                            final_mantissa = nv_dot_mantissa;
                            final_exponent = nv_dot_exponent;
                        end else begin
                            // V>1, last iteration: accumulate current nv_dot with accumulator
                            automatic logic signed [7:0] max_exp;
                            automatic logic [7:0] exp_diff_accum, exp_diff_dot;
                            automatic logic signed [31:0] aligned_accum, aligned_dot;
                            
                            max_exp = (accum_exponent > nv_dot_exponent) ? 
                                      accum_exponent : nv_dot_exponent;
                            
                            exp_diff_accum = max_exp - accum_exponent;
                            exp_diff_dot = max_exp - nv_dot_exponent;
                            
                            aligned_accum = (exp_diff_accum < 32) ? 
                                           (accum_mantissa >>> exp_diff_accum) : 32'sd0;
                            aligned_dot = (exp_diff_dot < 32) ? 
                                         (nv_dot_mantissa >>> exp_diff_dot) : 32'sd0;
                            
                            final_mantissa = aligned_accum + aligned_dot;
                            final_exponent = max_exp;
                        end
                        
                        o_result_mantissa <= final_mantissa;
                        o_result_exponent <= final_exponent;
                        o_result_valid <= 1'b1;
                        
                        // `ifdef SIMULATION
                        // $display("[BCV_RESULT] @%0t [B%0d,C%0d] OUTPUT: mant=%0d, exp=%0d",
                        //          $time, comp_b_idx, comp_c_idx, final_mantissa, final_exponent);
                        // `endif
                    end
                end
                
                COMP_DONE: begin
                    o_tile_done <= 1'b1;
                end
            endcase
        end
    end

endmodule
