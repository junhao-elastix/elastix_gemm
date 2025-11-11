# CLAUDE.md - Elastix GEMM Engine Project

This file provides high-level guidance for the GEMM engine sub-project.

**IMPORTANT**: Read the Critical Terminology section below at the beginning of every conversation to ensure correct understanding of the architecture.

## Project Overview

The **gemm/** directory contains the production MS2.0 GEMM (General Matrix Multiply) engine for the Achronix AC7t1500 Speedster7t FPGA. This is the primary active development project focused on high-performance matrix multiplication acceleration.

## Core Philosophy

- **Production-Ready Code**: This is the main production GEMM engine - all code should be robust and validated
- **Modular Architecture**: MS2.0 design with clear module boundaries and interfaces
- **Incremental Development**: Build, test, and validate incrementally - never make large untested changes
- **Reference-Based Design**: Always consult SINGLE_ROW_REFERENCE.md and STATE_TRANSITIONS_REFERENCE.md

## Critical Terminology (MUST READ)

**GFP Number Formats:**
- **GFP8**: Group Floating-Point with 8-bit mantissa, 5-bit exponent
- **GFP4**: Group Floating-Point with 4-bit mantissa, 5-bit exponent
- **Group Size**: Number of GFP numbers sharing one exponent (default: 32)

**Vector Concepts:**
- **Native Vector (NV)**: A vector of GFP numbers, may contain multiple groups
  - Default size: 128 GFP numbers (128 bytes mantissa, 4 bytes exponent)
  - Hardware atomic unit for data movement
- **Grouped Dimension (GD)**: Matrix dimension along which GFP numbers are grouped (usually inner dimension in GEMM)
- **UnGrouped Dimension (UGD)**: Matrix dimension that is not grouped (usually outer dimensions: batch, column)

**Dispatcher-Specific Terms:**
- **man_nv_cnt**: Total number of Native Vectors to distribute
- **ugd_vec_size**: Number of NVs dispatched to a column before switching to next column
  - Example: ugd_vec_size=8 means dispatch 8×4=32 lines to one tile, then switch to next

**MATMUL Command Dimensions:**
- **Left UGD length (B/batch/dim_b/left_ugd_len)**: Number of UGD vectors to process on left
- **Right UGD length (C/column/dim_c/right_ugd_len)**: Number of UGD vectors to process on right
- **UGD vector length (V/inner dimension/dim_v/vec_len)**: Number of Native Vectors per UGD

**Architecture Terms:**
- **Row**: A row of compute engine tiles in 2-D architecture (mapped to one DDR channel)
- **Column**: A single compute tile (in single-row architecture) or column of tiles (in 2-D architecture)
  - CRITICAL: In single-row mode, "column" = "compute tile" = one compute engine

**Memory Management Rule:**
- **Maximum safe back-to-back FETCH-DISPATCH operations = Number of Columns**
  - Each tile BRAM holds 128 NVs
  - Each FETCH brings 128 NVs to distribute
  - With N columns: N dispatches × 128 NVs = N columns × 128 NV capacity

**Key Understanding:**
- Dispatcher distributes Native Vectors in round-robin fashion with batches of ugd_vec_size
- Each column tracks its own write pointer for multi-batch address management
- C (right_ugd_len) is NOT the number of columns, it's the number of Native Vectors to distribute

## Key Integration Points

### Model Converter Integration
The GEMM hardware is actively used by the **model_converter** project (`/home/workstation/ElastiCore/projects/model_converter/`):
- Shared command interface (5-opcode microcode: 0xF0-0xF4)
- Common API through `elastiapi.hpp`
- Coordinated testing patterns

### Critical Operational Notes

- **Build Process**: Always use `./build_and_flash.sh` for automated workflow
- **Recovery First**: Keep recovery procedures ready - device hangs are recoverable
- **Validation Required**: After any change, run `test_registers` to verify device health
- **No Hardcoded Results**: All tests must use golden references or computed values

## Development Workflow

1. **Make Changes**: Edit RTL or software following modular design principles
2. **Build**: Use `make clean && make` (never skip clean)
3. **Program**: Use `./build_and_flash.sh` script
4. **Validate**: Run test suite starting with `test_registers`
5. **Document**: Update README.md for technical changes, CHANGELOG.md for fixes

## Architecture Philosophy

### Memory System Design
- **Dual-Memory Architecture**:
  - BRAM: Low-latency result storage and command buffering
  - GDDR6: High-bandwidth matrix data storage
  - Clear separation of control and data paths
- **Circular Buffer Pattern**: Dual-pointer management (rd_ptr/wr_ptr) for streaming results
- **Hierarchical Buffering**: Multiple BRAM levels to decouple processing stages

### MS2.0 Design Principles
- **Modular Compute Engine**: Hierarchical components with clear interfaces
- **Multi-Tile Architecture**: Supports 1-24 parallel compute tiles (currently 2 tiles instantiated)
  - Single-tile mode (col_en=0x000001): Works as original single compute engine
  - Multi-tile mode (col_en=0x000003): Distributes work across 2 tiles
  - Incremental fallback: Setting col_en=0x000001 seamlessly falls back to single-tile
- **Command-Driven Architecture**: 5-opcode microcode for flexible matrix operations
- **Dual BRAM Interface**: Parallel left/right matrix reads for improved throughput
- **Pipeline Decoupling**: Each stage can operate independently with FIFO interfaces

### State Machine Philosophy
- **Master Control FSM**: Centralized command parsing and orchestration
- **Dispatcher Control FSM**: Autonomous GDDR6 fetch management
- **Compute Engine FSM**: Independent matrix computation pipeline
- **Clear Handshaking**: Ready/valid signals between all FSMs

### Data Flow Architecture
- **Streaming Design**: Continuous data flow from GDDR6 → BRAM → Compute → Results
- **No Blocking Operations**: All stages can operate concurrently
- **Automatic Flow Control**: Back-pressure handling through FIFO status

## File Organization Philosophy

- **src/rtl/**: Core RTL modules - keep modular and parameterized
- **src/rtl/archive/**: Obsolete modules - do not use
- **sw_test/**: Essential tests only - archive obsolete tests
- **sim/**: Simulation environment - maintain clean test suites
- **doc/**: Reference documentation - consult frequently

## Testing Philosophy

- **Incremental Testing**: Start with basic health checks, build complexity
- **Golden Reference**: Python model → SystemVerilog reference → Hardware
- **Result Validation**: Never assume - always verify against references
- **Sanity Checks**: Run `test_registers` after every hardware operation

### Multi-Tile Testing Status (Nov 10, 2025)
- **Current Implementation**: 2 tiles instantiated (NUM_TILES=2 in engine_top.sv)
- **Verified Modes**:
  - Single-tile (col_en=0x000001): All 10 standard tests passing with golden comparison
  - Two-tile (col_en=0x000003): B2_C4_V2_2T test passing (result count verified)
- **Dispatcher Modes Working**:
  - BROADCAST: Replicates data to all enabled tiles (for left matrix/activations)
  - DISTRIBUTE: Round-robin distribution at batch granularity (for right matrix/weights)
- **Note**: Multi-tile tests currently skip golden comparison (no reference files generated yet)

## When to Update This File

Update CLAUDE.md only for:
- Major architectural shifts (e.g., MS1.0 → MS2.0 migration)
- Changes in development philosophy or workflow
- New integration points with other projects
- Critical operational procedure changes

For technical details, specifications, and implementation notes, update README.md instead.

## References

- **Technical Details**: See [README.md](README.md)
- **Change History**: See [CHANGELOG.md](CHANGELOG.md)
- **Technical Documentation**: See [REFERENCES.md](REFERENCES.md)

### Key Reference Documents
- **[STATE_TRANSITIONS_REFERENCE.md](STATE_TRANSITIONS_REFERENCE.md)**: FSM state transitions and command flow
- **[SINGLE_ROW_REFERENCE.md](SINGLE_ROW_REFERENCE.md)**: Multi-tile architecture specification (24-tile expansion plan)
- **[RESULT_BUFFER_REFERENCE.md](RESULT_BUFFER_REFERENCE.md)**: Result buffering and arbitration
- **[MULTI_TILE_DISPATCH_REFERENCE.md](MULTI_TILE_DISPATCH_REFERENCE.md)**: Tile dispatch mechanisms

---

**Remember**: This is production hardware. Think rigorously, test thoroughly, document clearly.