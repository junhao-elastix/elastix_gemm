# CLAUDE.md - Elastix GEMM Engine Project

**Project Status**: ✅ **PHASE 1 COMPLETE** - Single-Row Multi-Tile Architecture Validated
**Last Updated**: Tue Oct 21 02:17:21 PDT 2025
**Current Focus**: All 16 results matching golden values! Ready for Phase 2 multi-tile DISPATCH
**Top-Level Module**: `engine_top.sv`

---

## Quick Start

### Development (Simulation Only - Hardware Not Ready)

```bash
# Run simulation tests
cd /home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test
make clean && make run

# Check results
cat test_results.log

# View detailed logs
less sim.log
```

⚠️ **Hardware builds are currently disabled** - Single-row multi-tile architecture migration in progress. See [SINGLE_ROW_PLAN.md](SINGLE_ROW_PLAN.md) for development status.

---

## Project Overview

FPGA-based GEMM (General Matrix Multiply) engine for Achronix AC7t1500 Speedster7t, currently undergoing migration to scalable multi-tile architecture.

**Target Platform**:
- FPGA: Achronix AC7t1500 Speedster7t
- Board: VectorPath 815 (VP815)
- Memory: 8× GDDR6 channels (16GB total)
- Interface: PCIe Gen5 x16

**Development Goal**: Migrate from single compute engine to 1-16 parallel compute tiles with three-level memory hierarchy (L3: GDDR6 → L2: dispatcher_bram → L1: tile_bram).

---

## 🚧 Active Development: Multi-Tile Architecture Migration

**📋 See [SINGLE_ROW_PLAN.md](SINGLE_ROW_PLAN.md)** for comprehensive development plan including:
- Overall architecture and goals
- 5-phase development plan with detailed status
- Current blockers and debugging steps
- Design decisions and technical details

**Quick Status** (Oct 21, 2025):
- ✅ **Phase 1**: Single-row multi-tile infrastructure COMPLETE! 🎉
  - tile_bram_wrapper.sv, compute_tile_array.sv created
  - engine_top.sv updated for tile array integration
  - DISPATCH data copy working (512 aligned lines, addressing fixed)
  - WAIT_DISPATCH synchronization working (10ns blocking, ID tracking fixed)
  - **ALL 16 results match golden values perfectly!**
- ✅ **Phase 1.6**: Result correctness COMPLETE
  - Fixed DISPATCH addressing (source always 0, dest from command)
  - Fixed testbench DISPATCH length (528 → 512 aligned lines)
  - Architecture documentation added to SINGLE_ROW_PLAN.md
- 🔲 **Phases 2-5**: Multi-tile DISPATCH, master control, result collection, validation (PENDING)

**Achievement**: Phase 1 validated! Single-tile functionality fully working. Ready for Phase 2.3 multi-tile DISPATCH implementation when needed.

---

## Build System

### Simulation (Current Development)

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test

# Build and run
make clean && make run          # Full compile + simulate

# Debug mode (with GUI)
make debug                      # Requires X11/display

# Clean
make clean                      # Remove all generated files
```

**Outputs**:
- `test_results.log` - Pass/fail summary
- `sim.log` - Detailed simulation output
- `compile.log` - Compilation messages

### Hardware Build (Currently Disabled)

⚠️ Hardware builds will be re-enabled after multi-tile validation completes.

```bash
# DISABLED - For reference only
# cd /home/dev/Dev/elastix_gemm/gemm/build
# make clean && make run
```

---

## Key RTL Files (Multi-Tile Architecture)

### Active Development Modules

**Multi-Tile Infrastructure** (Phase 1 Complete):
- `tile_bram_wrapper.sv` - Per-tile L1 cache (512×256-bit dual-port)
- `compute_tile_array.sv` - Tile instantiation wrapper (NUM_TILES parameter)
- `engine_top.sv` - Top-level integration with tile array
- `compute_engine_modular.sv` - Individual tile compute engine

**Memory & Control** (Phase 2 In Progress):
- `dispatcher_control.sv` - FETCH + DISPATCH FSM (L3→L2→L1 data flow)
- `dispatcher_bram_dual_read.sv` - L2 shared BRAM (2048×256-bit)
- `master_control.sv` - Command parsing and orchestration

**Result Path** (Phase 4 Pending):
- `result_bram.sv` - Result buffer (256×16-bit FP16)
- `result_collector.sv` - **TODO**: Multi-tile result aggregation

**Compute Pipeline**:
- `gfp8_bcv_controller.sv` - BCV loop orchestration
- `gfp8_nv_dot.sv` - Native Vector dot product
- `gfp8_group_dot_mlp.sv` - Group dot product with MLP
- `gfp8_to_fp16.sv` - GFP8 to FP16 conversion

### Package & Interfaces

- `gemm_pkg.sv` - Global parameters, types, constants
- `nap_interfaces.svh` - AXI4 interface definitions

### Location

All RTL files: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/`

---

## Simulation Testbench

**Main Testbench**: `sim/vector_system_test/tb_engine_top.sv`

**Test Configurations** (currently testing B4_C4_V32 only):
- B4_C4_V32: 4 batches × 4 columns × 32 vector length
- Other tests commented out during multi-tile debug

**Memory Models**:
- `src/tb/tb_memory_model.sv` - GDDR6 behavioral model

---

## Command Architecture (Multi-Tile)

### 5-Stage Pipeline

1. **FETCH (0xF0)**: GDDR6 → dispatcher_bram (L3 → L2)
   - Loads 528 lines via AXI4 burst reads
   - Separate left/right matrix spaces in L2

2. **DISPATCH (0xF1)**: dispatcher_bram → tile_bram (L2 → L1)
   - **NEW BEHAVIOR** (Phase 2): Copies data to tile-local L1 caches
   - Broadcast mode: Left activations to all tiles
   - Distribute mode: Right weights split across tiles
   - **Status**: Data copy working, synchronization blocked

3. **WAIT_DISPATCH (0xF3)**: Synchronization barrier
   - Waits for all DISPATCH operations to complete
   - **Status**: BLOCKED - MC stuck in ST_WAIT_DISP

4. **MATMUL (0xF2)**: Parallel tile computation
   - **Status**: Not yet reached due to WAIT_DISPATCH block

5. **WAIT_MATMUL (0xF4)**: Result ready
   - **Status**: Not yet implemented (Phase 4)

### Memory Hierarchy

```
L3: GDDR6 (8 channels, 16GB total)
     ↓ FETCH (AXI4)
L2: dispatcher_bram (2048×256-bit, shared)
     ↓ DISPATCH (parallel copy)
L1: tile_bram[0..15] (512×256-bit each, private)
     ↓ MATMUL
Compute Tile[0..15]
```

See [SINGLE_ROW_PLAN.md](SINGLE_ROW_PLAN.md#command-flow-5-stage-pipeline) for detailed command specifications.

---

## Development Guidelines

### Critical Rules (MANDATORY from main CLAUDE.md)

1. **Always clean before building**: `make clean && make <target>`
2. **Python environment**: `conda activate elastix` before running Python tools
3. **Documentation**: Update CHANGELOG.md with `date` timestamp after significant changes
4. **State machines**: Explicit control signal assignments, separate transitions from controls
5. **SystemVerilog**: Use `logic`, `always_comb`, `always_ff` (modern style)

### When Modifying RTL

1. Read [SINGLE_ROW_PLAN.md](SINGLE_ROW_PLAN.md) to understand current phase
2. Check if changes affect single-row multi-tile architecture
3. Update simulation testbench if needed
4. Run `make clean && make run` in sim/vector_system_test/
5. Update CHANGELOG.md with findings

### Current Development Focus

**Phase 1 Complete!** ✅ (Previously Phase 1.6 - Now Resolved):
- Fixed DISPATCH addressing in `dispatcher_control.sv` (source always 0, dest from command)
- Fixed testbench DISPATCH length (528 → 512 aligned lines)
- All 16 results now match golden values perfectly
- See [SINGLE_ROW_PLAN.md](SINGLE_ROW_PLAN.md) for complete Phase 1 documentation and next steps

---

## References

### Project Documentation

- **⭐ Single-Row Development Plan**: [SINGLE_ROW_PLAN.md](SINGLE_ROW_PLAN.md) - **ACTIVE DEVELOPMENT**
- **Project History**: [CHANGELOG.md](CHANGELOG.md) - Detailed change history with timestamps
- **Current File**: [CLAUDE.md](CLAUDE.md) - This project guide
- **Main Project Root**: `/home/dev/Dev/elastix_gemm/CLAUDE.md` - Top-level overview

### Technical Documentation

- **Achronix Documentation**: `~/Dev/elastix_gemm/doc/` (NoC, GDDR6, Component Library, Soft IP)
- **Reference Projects**:
  - `~/Dev/elastix_gemm/llm_vp_demo_pcie_orig/` - Original single-tile reference (READ-ONLY)
  - `~/Dev/elastix_gemm/shell_demo/` - Hardware abstraction examples
  - `~/Dev/elastix_gemm/gddr_ref_design/` - GDDR6 integration reference

### Related Projects

- **EUS Framework**: `/home/dev/Dev/eus/@CLAUDE.md` - Hardware abstraction layer
- **ACX SDK**: `/home/dev/Dev/acxsdk/CLAUDE.md` - PCIe communication SDK
- **Compute Engine**: `/home/dev/Dev/compute_engine_w8a8/` - Original single-engine implementation

---

## Known Issues & Limitations

**✅ Phase 1 Complete!** (Oct 21, 2025):
- All previous issues RESOLVED!
- DISPATCH addressing fixed (source always 0, dest from command)
- Testbench DISPATCH length corrected (528 → 512 aligned lines)
- ALL 16 results match golden values perfectly

**Single-Row Multi-Tile Status**:
- ✅ Phase 1 infrastructure complete
- ✅ Phase 1.5 DISPATCH data copy working (512 aligned lines)
- ✅ Phase 1.5 WAIT_DISPATCH synchronization working (ID tracking fixed)
- ✅ **Phase 1.6 Result correctness COMPLETE!**
- ✅ Single-tile functionality fully validated
- 🔲 Phases 2-5 not yet started (multi-tile DISPATCH, result collection)

**Technical Debt**:
- Exponent handling in DISPATCH needs separate addressing logic
- Limited per-tile debug visibility
- Result collector module not yet implemented
- Need tile_bram read/write monitoring for debugging

See [SINGLE_ROW_PLAN.md](SINGLE_ROW_PLAN.md#technical-debt--known-issues) for complete list.

---

## Emergency Recovery (If Needed)

If simulation hangs or fails:

```bash
# Kill stuck simulators
killall -9 vsim vlog

# Clean everything
cd /home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test
make clean
rm -rf dataset.asdb* work/

# Fresh rebuild
make clean && make run
```

---

## Version History

| Date | Milestone | Status |
|------|-----------|--------|
| 2025-10-20 14:03 | Phase 1.1-1.3: Infrastructure | ✅ Complete |
| 2025-10-20 19:46 | Phase 1.4: DISPATCH bugs fixed | ✅ Complete |
| 2025-10-20 19:46 | Phase 2.1: DISPATCH data copy | ✅ Working |
| 2025-10-20 20:34 | Phase 2.2/1.5: WAIT_DISPATCH sync | ✅ Fixed |
| 2025-10-20 20:34 | Phase 1.6: Result correctness | ⚠️ In Progress |
| 2025-10-21 02:17 | Phase 1.6: Result correctness | ✅ **COMPLETE!** |

See [CHANGELOG.md](CHANGELOG.md) for detailed history with timestamps.

---

**Maintained by**: Claude Code (claude.ai/code)
**Last Validation**: Tue Oct 21 02:17:21 PDT 2025 - **Phase 1 COMPLETE! All 16 results match golden values**
