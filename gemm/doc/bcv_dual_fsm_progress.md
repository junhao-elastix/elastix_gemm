# Dual-FSM Ping-Pong Implementation Progress

## Status: IN PROGRESS (60% complete)

### Completed ✅
1. Updated header documentation with dual-FSM architecture
2. Added dual FSM state definitions (fill_state_t, comp_state_t)
3. Added ping-pong buffers (nv_*_ping, nv_*_pong)
4. Added handshake signals (filling_ping/pong, ping_ready/pong_ready)
5. Added buffer mux logic (use_pong, nv_*_active)
6. Updated NV dot product to use active buffers
7. Implemented Fill FSM next-state logic
8. Implemented Compute FSM next-state logic
9. Implemented dual FSM sequential logic
10. Updated BRAM address generation to use fill_state_reg

### TODO ❌
1. **Implement handshake signal management** (CRITICAL)
   - Fill FSM: Set filling_ping/pong when starting fill, set ping_ready/pong_ready when done
   - Compute FSM: Clear filling_ping/pong when starting compute, clear ping_ready/pong_ready in ACCUM
   
2. **Implement buffer filling logic** (ping-pong aware)
   - Use fill_target to select which buffer to fill
   - Update fill_target based on conditions
   - Fill cycle counter management
   
3. **Implement startup trigger**
   - On i_tile_en_rising: set filling_ping = 1 to kickstart
   
4. **Update use_pong selection**
   - In COMP_IDLE→COMP_NV transition: Select which buffer to use
   
5. **Update compute_wait counter**
   - Should run in COMP_NV state
   
6. **Update loop index control**
   - Should work with COMP_ACCUM instead of ST_ACCUM
   
7. **Update accumulator logic**
   - Should trigger in COMP_ACCUM state
   
8. **Update output logic**
   - o_tile_done should be set in COMP_RETURN
   - o_result_valid should be set in COMP_RETURN

### File Locations

**Current file**: `src/rtl/gfp8_bcv_controller.sv` (partially updated)
**Backup**: `src/rtl/gfp8_bcv_controller_single_fsm_backup.sv` (working single-FSM version)
**Documentation**: `doc/bcv_pingpong.md` (complete protocol specification)

### Next Steps

Continue implementation starting at line ~342 (Buffer Filling Logic section)

Key sections to update:
1. Lines 342-420: Buffer filling (needs ping-pong logic + handshake)
2. Lines 421-450: Compute pipeline control (update for COMP_NV state)  
3. Lines 451-550: Loop index control (update for COMP_ACCUM)
4. Lines 551-600: Accumulator logic (update for COMP_ACCUM)
5. Lines 601-650: Output logic (update for COMP_RETURN/COMP_DONE)

### Testing Strategy

Once implementation is complete:
1. Test BCV standalone (sim/gfp8_bcv_controller)
2. Test compute engine (sim/compute_engine_test)
3. Compare cycle counts vs. single-FSM version
4. Expected: V=128 should be ~830 cycles (vs. 1411 single-FSM)

### Notes

The dual-FSM approach is significantly more complex but provides clean separation of concerns.
The handshake protocol is the key to correctness - Fill sets, Compute clears.



