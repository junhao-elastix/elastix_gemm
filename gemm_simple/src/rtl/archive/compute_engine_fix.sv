// FIX for compute_engine.sv - Result Write Issue
// Problem: Results are never written because v_idx is reset on the same clock edge
// that the result write logic checks for v_idx == dim_v_reg - 1

// Original problematic code (lines 910-924):
/*
ST_OUTPUT: begin
    if (!i_result_afull) begin
        // Handle V-loop iteration or advance to next dot product
        if (v_idx < dim_v_reg - 1) begin
            // More V iterations - increment v_idx and loop back
            v_idx <= v_idx + 1;
            $display("[CE_DEBUG] V-loop: incrementing v_idx from %0d to %0d", v_idx, v_idx + 1);
        end else begin
            // Completed all V - output result and reset v_idx
            result_count_reg <= result_count_reg + 1;
            v_idx <= '0;  // ← PROBLEM: Reset happens same cycle as check!
            $display("[CE_DEBUG] V-loop COMPLETE: outputting result, resetting v_idx to 0");
        end
    end
end
*/

// And the result write logic (lines 957):
/*
if (state_reg == ST_OUTPUT && !i_result_afull && (v_idx == dim_v_reg - 1)) begin
    // ← This check happens AFTER v_idx is already reset to 0!
    result_valid_reg <= 1'b1;
end
*/

// SOLUTION 1: Use a flag to indicate result is ready
// Add this signal declaration around line 170:
logic result_ready_reg;  // Flag to indicate result should be written

// In the state machine (replace lines 910-924):
ST_OUTPUT: begin
    if (!i_result_afull) begin
        // Handle V-loop iteration or advance to next dot product
        if (v_idx < dim_v_reg - 1) begin
            // More V iterations - increment v_idx and loop back
            v_idx <= v_idx + 1;
            result_ready_reg <= 1'b0;
            $display("[CE_DEBUG] V-loop: incrementing v_idx from %0d to %0d", v_idx, v_idx + 1);
        end else begin
            // Completed all V - set flag for result output
            result_count_reg <= result_count_reg + 1;
            result_ready_reg <= 1'b1;  // Set flag BEFORE resetting v_idx
            v_idx <= '0;
            $display("[CE_DEBUG] V-loop COMPLETE: outputting result, resetting v_idx to 0");
        end
    end
end

// And modify the result write logic (replace line 957):
if (state_reg == ST_OUTPUT && !i_result_afull && result_ready_reg) begin
    // Now we check the flag, not v_idx
    result_valid_reg <= 1'b1;
    // ... rest of conversion logic ...
end

// Don't forget to initialize and clear the flag:
// In reset (around line 810):
result_ready_reg <= 1'b0;

// In ST_IDLE (around line 822):
result_ready_reg <= 1'b0;

// In ST_NEXT_DOT (after line 937):
result_ready_reg <= 1'b0;  // Clear flag when moving to next dot product

// ALTERNATIVE SOLUTION 2: Delay v_idx reset by registering the condition
// This would involve creating a "v_idx_last" register that holds the previous value

// ALTERNATIVE SOLUTION 3: Write result in ST_CONVERT instead
// Move the result write to ST_CONVERT when v_idx == dim_v_reg - 1
// This avoids the race condition entirely