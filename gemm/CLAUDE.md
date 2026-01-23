# CLAUDE.md - Elastix GEMM Engine Project

This file provides high-level guidance for the GEMM engine sub-project.

**IMPORTANT**: Read the Critical Terminology section below at the beginning of every conversation to ensure correct understanding of the architecture.

## Project Overview

The **gemm/** directory contains the production MS2.0 GEMM (General Matrix Multiply) engine for the Achronix AC7t1500 Speedster7t FPGA.

**Current Objective: 2-D MultiRow GEMM Architecture**

The project is transitioning from single-row multi-tile to a full 2-D array architecture:
- **Target**: 16 rows × 16 columns (256 compute tiles)
- **Memory**: Each row connected to one GDDR6 channel (8 channels total, 2 rows per channel)
- **Compute**: ACX_MLP72 primitives for GFP8 dot products
- **Reference Design**: AMD GEMM architecture patterns adapted for Achronix hardware

## Core Philosophy

- **Production-Ready Code**: This is the main production GEMM engine - all code should be robust and validated
- **Modular Architecture**: MS2.0 design with clear module boundaries and interfaces
- **Incremental Development**: Build, test, and validate incrementally - never make large untested changes
- **Reference-Based Design**: Always consult MULTI_ROW_REFERENCE.md and AMD_GEMM_REFERENCE.md for architectural patterns
- **AMD Design Patterns**: Adopt ready-valid handshaking, FIFO decoupling, and coding conventions from AMD reference

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

**Architecture Terms (2-D MultiRow):**
- **Row**: A row of compute tiles, each row has its own row_bram for activations (mapped to GDDR6 channel)
- **Column**: A column of compute tiles, all columns share weight data from mlp_bram
- **Tile**: Single compute unit at intersection of row and column
- **num_rows_gp**: Number of rows in the array (default: 16)
- **num_cols_gp**: Number of columns in the array (default: 16)

**Memory Block (128 NVs):**
- **Format**: 16 exponent lines + 512 mantissa lines = 528 lines total (256-bit wide)
- **Exponent**: 128 NVs × 4 bytes = 512 bytes → 16 lines
- **Mantissa**: 128 NVs × 128 bytes = 16384 bytes → 512 lines

**V/C Distribution (Work Partitioning):**
- **V across rows**: First (V % num_rows) rows get (V / num_rows + 1) NVs
- **C across columns**: First (C % num_cols) columns get (C / num_cols + 1) NVs
- **Pattern**: Distribute evenly, remainder goes to lower-indexed partitions

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

### MS2.0 → 2-D MultiRow Design Principles
- **2-D Tile Array**: 16×16 compute tiles with row/column organization
- **Separate Memory Paths**:
  - **row_bram**: Per-row activation storage (left matrix), one per row
  - **mlp_bram**: Shared weight storage (right matrix), broadcast to all columns
- **Ready-Valid Handshaking**: All inter-module communication uses ready/valid protocol
- **FIFO Decoupling**: FIFOs between pipeline stages for flow control and timing isolation
- **V/C Work Distribution**: Automatic partitioning across rows (V) and columns (C)
- **Column Adder Tree**: FP accumulation across rows within each column
- **Output Buffer**: Synchronizes results from all columns before output

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

## When to Update This File

Update CLAUDE.md only for:
- Major architectural shifts (e.g., MS2.0 → 2-D MultiRow migration)
- Changes in development philosophy or workflow
- New integration points with other projects
- Critical operational procedure changes

**Current Status**: Transitioning from single-row multi-tile to 2-D MultiRow architecture. Reference manuals (MULTI_ROW_REFERENCE.md, AMD_GEMM_REFERENCE.md) define target architecture.

For technical details, specifications, and implementation notes, update README.md instead.

## References

- **Technical Details**: See [README.md](README.md)
- **Change History**: See [CHANGELOG.md](CHANGELOG.md)
- **Technical Documentation**: See [REFERENCES.md](REFERENCES.md)

### Key Reference Documents

**Primary References (2-D MultiRow):**
- **[MULTI_ROW_REFERENCE.md](MULTI_ROW_REFERENCE.md)**: Complete 2-D array architecture, memory layout, data flow, ready-valid patterns
- **[AMD_GEMM_REFERENCE.md](AMD_GEMM_REFERENCE.md)**: AMD reference design analysis, reusable patterns, coding conventions to adopt

**Legacy References (Single-Row):**
- **[STATE_TRANSITIONS_REFERENCE.md](STATE_TRANSITIONS_REFERENCE.md)**: FSM state transitions and command flow
- **[SINGLE_ROW_REFERENCE.md](SINGLE_ROW_REFERENCE.md)**: Single-row multi-tile architecture (basis for 2-D expansion)
- **[RESULT_BUFFER_REFERENCE.md](RESULT_BUFFER_REFERENCE.md)**: Result buffering and arbitration
- **[MULTI_TILE_DISPATCH_REFERENCE.md](MULTI_TILE_DISPATCH_REFERENCE.md)**: Tile dispatch mechanisms

**External References:**
- **AMD GEMM RTL**: `/home/dev/Dev/elastix_gemm/amd_gemm/ip/` - Reference implementation (READ-ONLY)
- **AMD Common IP**: `/home/dev/Dev/elastix_gemm/amd_gemm/ip/common/` - Reusable FIFO, adapter, BRAM modules

---

**Remember**: This is production hardware. Think rigorously, test thoroughly, document clearly.