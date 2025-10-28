
## Development Phases

### ✅ Phase 1: Multi-Tile Infrastructure (COMPLETE)

**Goal**: Create foundational multi-tile components with backward compatibility

**Deliverables**:
- [x] tile_bram_wrapper.sv (512×256-bit dual-port BRAM per tile)
- [x] compute_tile_array.sv (NUM_TILES instantiation wrapper)
- [x] engine_top.sv integration (replace single engine with tile array)
- [x] DISPATCH FSM skeleton in dispatcher_control.sv
- [x] Single-tile mode (column_enable = 16'h0001)

**Status**: ✅ **COMPLETE** (Mon Oct 20 14:03:19 PDT 2025)

**Validation**: Compiles successfully, 0 Errors, 19 Warnings

---

### ⚠️ Phase 2: DISPATCH Data Copy Implementation (IN PROGRESS)

**Goal**: Implement L2→L1 data distribution for tile-local execution

**Phase 2.1**: Minimal DISPATCH (Single-Tile Mode) ✅ DONE
- [x] Data copy logic: dispatcher_bram → tile_bram[0]
- [x] Address generation (disp_cnt_reg counter)
- [x] Write enable generation (tile_wr_en_mask = 16'h0001)
- [x] All 4 data paths (left/right × mantissa/exponent)
- [x] Testbench update (disp_len = 528)

**Status**: ✅ Data copy working (5290 cycles for 528 lines verified)

**Phase 2.2**: Synchronization Debug ✅ COMPLETE
- [x] Fix duplicate parameter assignment bug
- [x] Fix testbench DISPATCH length (0 → 528)
- [x] Fix wait_id header location bug (bits [31:24] → [15:8])
- [x] Add ID tracking debug prints
- [x] Verify WAIT_DISPATCH synchronization working

**Phase 1.6**: Result Correctness Debug ✅ COMPLETE
- [x] WAIT_DISPATCH unblocked, results received (16/16)
- [x] Architecture understanding aligned (memory block format, FETCH/DISPATCH flow)
- [x] Fix DISPATCH addressing (source always 0, dest from command, length = NV_count×4)
- [x] Fix testbench disp_len from 528 to 512
- [x] Single-tile data path validated (broadcast/distribute logic deferred to Phase 2.3)
- [x] **ALL 16 results match golden values perfectly!** 🎉

**Phase 2.3**: Full Multi-Tile DISPATCH (PENDING)
- [ ] Broadcast mode: Left activation to all tiles (tile_wr_en_left = column_enable)
- [ ] Distribute mode: Right weights split across tiles
- [ ] Configurable tile count via column_enable parameter
- [ ] Address offset calculation per tile

---

### 🔲 Phase 3: Master Control Updates (PENDING)

**Goal**: Update command processing for multi-tile MATMUL and result collection

**Deliverables**:
- [ ] MATMUL command: Enable N tiles via column_enable
- [ ] Tile enable logic: o_ce_tile_en[15:0] from column_enable
- [ ] Result size calculation: (dim_b × dim_c) × num_enabled_tiles
- [ ] VECTOR_READOUT command: Support tile-interleaved results
- [ ] Wait condition updates for N-tile completion

**Dependencies**: Phase 2 DISPATCH complete

---

### 🔲 Phase 4: Result Collector Implementation (PENDING)

**Goal**: Aggregate results from multiple tiles with proper ordering

**Deliverables**:
- [ ] result_collector.sv module (new file)
- [ ] Tile-major result ordering (tile0_results, tile1_results, ...)
- [ ] FIFO arbitration across N tiles
- [ ] Tile ID tagging for debug
- [ ] Integration with result_bram_writer

**Architecture**:
```systemverilog
result_collector #(
    .NUM_TILES(16),
    .RESULT_WIDTH(16)  // FP16
) u_result_collector (
    .i_tile_result_valid[15:0],   // Per-tile valid signals
    .i_tile_result_data[15:0],     // Per-tile FP16 results
    .i_tile_id[15:0],              // Tile ID for ordering
    .o_result_valid,               // Aggregated output
    .o_result_data,
    .o_tile_id                     // Pass-through for debug
);
```

**Dependencies**: Phase 3 complete

---

### 🔲 Phase 5: Validation and Testing (PENDING)

**Goal**: Comprehensive testing of multi-tile functionality

**Test Configurations**:
- [ ] 1-tile mode (column_enable = 0x0001) - Backward compatibility
- [ ] 2-tile mode (column_enable = 0x0003) - Basic parallelism
- [ ] 4-tile mode (column_enable = 0x000F) - Quadrant test
- [ ] 8-tile mode (column_enable = 0x00FF) - Half capacity
- [ ] 16-tile mode (column_enable = 0xFFFF) - Full capacity

**Validation Metrics**:
- [ ] Functional correctness vs single-tile reference
- [ ] Performance scaling (linear with tile count)
- [ ] Resource utilization (BRAM, LUTs, FFs)
- [ ] Timing closure at target clock frequency

**Test Matrix** (B×C×V configurations):
| Config | Tiles | Expected Speedup | Status |
|--------|-------|------------------|--------|
| B4_C4_V32 | 1 | 1× (baseline) | ❌ Blocked |
| B4_C4_V32 | 4 | 4× | Pending |
| B8_C8_V64 | 8 | 8× | Pending |
| B16_C16_V128 | 16 | 16× | Pending |

**Dependencies**: Phase 4 complete

---

## Current Status (As of Oct 20, 2025 Late Evening)

### ✅ WAIT_DISPATCH Synchronization - FIXED!

**Root Cause Found**: Testbench was placing `wait_id` in wrong header location
- **Wrong**: `cmd[0] = {wait_id, 8'd0, id, e_cmd_op_wait_disp}` → wait_id in bits [31:24]
- **Correct**: `cmd[0] = {16'd4, wait_id, e_cmd_op_wait_disp}` → wait_id in bits [15:8]
- master_control.sv reads ID from bits [15:8], so it was capturing wrong value

**Fix Applied** (tb_engine_top.sv):
1. Fixed `generate_wait_disp_command` task signature (removed `id` parameter)
2. Put `wait_id` directly in header bits [15:8] per MS2.0 spec
3. Updated call site from `(3, 2, cmd)` to `(2, cmd)`

**Verification** (sim.log):
```
@ 20295000: DISPATCH completed: last_disp_id_reg <= 2
@ 20355000: WAIT command decoded: wait_id_reg <= 2
@ 20355000: WAIT_DISP satisfied: last_disp_id=2 >= wait_id=2
```

**Results**: 16/16 results received in 18895 cycles (was 0/16 with timeout)

---

### ⚠️ Current Issue: Result Data Correctness

**Symptom**: All 16 results mismatch golden values

**Evidence** (test_results.log):
```
[0]: hw=0x0000 golden=0xb6ae diff=46766  ← Zero (very wrong)
[1]: hw=0x0000 golden=0xb811 diff=47121  ← Zero (very wrong)
[5]: hw=0x3b48 golden=0x3af5 diff=83     ← Close!
[6]: hw=0xb652 golden=0xb6ec diff=154    ← Close!
[7]: hw=0x381f golden=0x3828 diff=9      ← Very close!
```

**Pattern Analysis**:
- Some results are zero → suggests missing data or wrong addresses
- Some results are close → suggests partial data correctness
- Mixed results → likely address generation or alignment issue

**Hypotheses**:
1. DISPATCH may not be copying all data correctly from dispatcher_bram → tile_bram
2. Compute engine address generation for tile_bram reads may be incorrect
3. Mantissa/exponent data alignment issues between L2 and L1
4. Left vs right data routing problems

**Debug Plan** (Phase 1.6):
1. ~~Add tile_bram write monitoring in dispatcher_control~~ ✓ Done
2. ~~Add tile_bram read monitoring in compute_engine_modular~~
3. ~~Compare dispatcher_bram contents vs tile_bram contents after DISPATCH~~
4. ~~Verify compute engine generates correct tile_bram addresses~~
5. ~~Check exponent data copy (currently tied to mantissa addressing)~~

**Architecture Understanding Breakthrough** (Oct 21, 2025):

After detailed discussion, identified fundamental misalignment in DISPATCH implementation:

**Root Cause Discovery:**
- **Wrong**: DISPATCH was copying 528 lines (packed memory block format) with source address from command
- **Correct**: DISPATCH should copy 512 lines (aligned buffer format) with source ALWAYS at address 0

**Key Insights Documented**:
1. Memory block format: 16 packed exp lines + 512 mantissa lines (528 total)
2. FETCH unpacks exponents → creates aligned buffers (512 exp + 512 man)
3. DISPATCH operates on aligned buffers, NOT packed blocks
4. Source address is implicit (always 0), destination address is explicit (from command)
5. Four parallel data paths (exp_left, man_left, exp_right, man_right) operate simultaneously

**Implementation Fixes Required**:
1. Fix addressing: `disp_addr_reg` = tile_bram WRITE destination (not dispatcher_bram READ source)
2. Fix length: `disp_len = NV_count × 4 = 512` (not 528)
3. Fix counter: Source reads [0:511], destination writes [dest_addr : dest_addr+511]
4. Implement broadcast/distribute modes (Phase 1: broadcast to tile[0] only)

See "Hardware Architecture Details" section above for complete documentation.

---

## Key Design Decisions

### Memory Organization

**L1 Tile BRAM Size**: 512×256-bit per tile
- Stores 128 Native Vectors (NV) per tile
- Each NV = 4 lines × 256-bit = 1KB
- Total per tile: 128 NV × 1KB = 128KB

**L2 Dispatcher BRAM Size**: 2048×256-bit shared
- Left matrix space: [0-527] (528 lines)
- Right matrix space: [528-1055] (528 lines)
- Reserved: [1056-2047] for future expansion

### Tile Enable Encoding

**column_enable[15:0]**: Bitmask for tile activation
- Bit 0 = Tile 0, Bit 1 = Tile 1, ..., Bit 15 = Tile 15
- Phase 1: 0x0001 (tile 0 only)
- Phase 2+: Runtime configurable (1-16 tiles)

### Data Distribution Strategy

**Left Matrix (Activations)**: Broadcast mode
- Same data written to all enabled tiles
- Write enable: `tile_wr_en_left = column_enable`

**Right Matrix (Weights)**: Distribute mode
- Different data to each tile (weight sharding)
- Write enable: `tile_wr_en_right[i] = column_enable[i]`
- Address offset per tile for weight distribution

---

## Success Criteria

### Phase 1 Success ✅ COMPLETE
- [x] DISPATCH data copy verified (5290 cycles measured)
- [x] WAIT_DISPATCH synchronization working
- [x] Single-tile MATMUL executes after DISPATCH (16/16 results received)
- [x] **B4_C4_V32 test passes with ALL results correct!**
- [x] tile_bram data correctness verified (DISPATCH addressing fixed)

### Overall Project Success
- [ ] All 5 phases complete
- [ ] 16-tile mode functional and validated
- [ ] Linear performance scaling demonstrated
- [ ] Timing closure maintained
- [ ] No regression in single-tile mode

---

## Technical Debt / Known Issues

1. **Exponent Handling in DISPATCH**: Currently tied to mantissa logic, needs separate alignment addressing
2. **State Monitoring**: Limited visibility into tile-level state machines
3. **Debug Infrastructure**: Need per-tile debug outputs for parallel debugging
4. **Makefile Cleanup**: Simulation database (.asdb) locking issues persist
5. **Documentation**: Some Phase 2+ details need RTL-level specification

---

## References

**Related Documentation**:
- [CHANGELOG.md](CHANGELOG.md) - Detailed change history
- [CLAUDE.md](CLAUDE.md) - Project overview and context
- [README.md](README.md) - User-facing documentation

**Key RTL Files**:
- [tile_bram_wrapper.sv](src/rtl/tile_bram_wrapper.sv) - Per-tile L1 cache
- [compute_tile_array.sv](src/rtl/compute_tile_array.sv) - Tile instantiation
- [dispatcher_control.sv](src/rtl/dispatcher_control.sv) - FETCH + DISPATCH FSM
- [master_control.sv](src/rtl/master_control.sv) - Command orchestration
- [engine_top.sv](src/rtl/engine_top.sv) - Top-level integration

**Simulation**:
- [tb_engine_top.sv](sim/vector_system_test/tb_engine_top.sv) - Testbench
- [test_results.log](sim/vector_system_test/test_results.log) - Latest results
- [Makefile](sim/vector_system_test/Makefile) - Build configuration

---

## Version History

| Date | Phase | Status | Notes |
|------|-------|--------|-------|
| 2025-10-20 14:03 | Phase 1.1-1.3 | ✅ Complete | Infrastructure created |
| 2025-10-20 19:46 | Phase 1.4 | ✅ Complete | DISPATCH bugs fixed |
| 2025-10-20 19:46 | Phase 2.1 | ✅ Complete | Data copy working |
| 2025-10-20 20:34 | Phase 2.2 | ✅ Complete | WAIT_DISPATCH sync fixed |
| 2025-10-20 20:34 | Phase 1.5 | ✅ Complete | ID tracking working, 16/16 results |
| 2025-10-20 20:34 | Phase 1.6 | ⚠️ In Progress | Result correctness debugging |
| 2025-10-21 02:17 | Phase 1.6 | ✅ Complete | **ALL 16 results match! Phase 1 COMPLETE!** |

---

**Phase 1 Complete!** 🎉 All single-tile infrastructure validated. Ready for Phase 2.3 (Full Multi-Tile DISPATCH) when needed.
