# Dispatcher Testbench

**Purpose**: Unit test for `dispatcher.sv` module with configurable tile count
**Status**: ✅ **Ready for Testing**
**DUT**: `dispatcher.sv`

## Quick Start

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/dispatcher_test
make clean && make run     # Run simulation
make debug                 # Run with GUI for waveform analysis
```

## Overview

This testbench validates the **dispatcher module** in isolation with configurable number of tiles. The dispatcher handles DISPATCH operations, transferring data from dispatcher_bram to tile_bram with support for broadcast and distribute modes.

### Key Features

- **Configurable NUM_TILES**: Default 8, supports 2-24 tiles
- **BROADCAST Mode**: Replicates data to all enabled tiles
- **DISTRIBUTE Mode**: Round-robin distribution across enabled tiles
- **Per-Tile Write Enable Verification**: Validates tile selection logic
- **Multi-Tile Testing**: Tests 1, 4, and 8 tile configurations

## Architecture

### Design Under Test (DUT)
- **Module**: `gemm/src/rtl/dispatcher.sv`
- **Dispatcher BRAM**: Source data storage (512 deep)
- **Tile BRAM**: Per-tile destination storage (512 deep per tile)

### Test Sequence

1. **Initialize dispatcher_bram** with test pattern data
2. **Issue DISPATCH commands** with various configurations:
   - BROADCAST to 1 tile
   - BROADCAST to 4 tiles
   - DISTRIBUTE to 4 tiles
   - DISTRIBUTE to 8 tiles
3. **Verify per-tile writes** via debug messages

## Makefile Targets

| Target | Description |
|--------|-------------|
| `make` or `make run` | Clean, compile, and run simulation |
| `make compile` | Compile only (no simulation) |
| `make debug` | Run simulation with GUI |
| `make clean` | Remove generated files |
| `make help` | Show help message |

## Configuration

### NUM_TILES Parameter

The testbench supports configurable tile count (default 8):

```systemverilog
parameter NUM_TILES = 8;  // Change to 2-24 as needed
```

To test with different tile counts, edit `tb_dispatcher.sv` and recompile.

## Test Cases

### Test 1: BROADCAST to 1 tile
- **col_en**: 0x000001 (Tile 0 only)
- **man_nv_cnt**: 4 NVs
- **Mode**: BROADCAST
- **Expected**: Data replicated to Tile 0

### Test 2: BROADCAST to 4 tiles
- **col_en**: 0x00000F (Tiles 0-3)
- **man_nv_cnt**: 4 NVs
- **Mode**: BROADCAST
- **Expected**: Same data replicated to all 4 tiles

### Test 3: DISTRIBUTE to 4 tiles
- **col_en**: 0x00000F (Tiles 0-3)
- **man_nv_cnt**: 8 NVs
- **ugd_vec_size**: 2 NVs per batch
- **Mode**: DISTRIBUTE
- **Expected**: Data distributed round-robin across tiles

### Test 4: DISTRIBUTE to 8 tiles
- **col_en**: 0x0000FF (Tiles 0-7)
- **man_nv_cnt**: 16 NVs
- **ugd_vec_size**: 2 NVs per batch
- **Mode**: DISTRIBUTE
- **Expected**: Data distributed round-robin across all 8 tiles

## Debug Output

The testbench provides detailed debug output for each tile write:

```
[TILE0] @175 LEFT_MAN Write: addr=0, data=0x...
[TILE1] @185 LEFT_MAN Write: addr=0, data=0x...
```

## Success Criteria

✅ **PASS Conditions**:
1. All 4 test cases complete without errors
2. Dispatcher state transitions correctly (IDLE → DISP_BUSY → DISP_DONE)
3. Per-tile write enables match expected col_en mask
4. No watchdog timeouts

## Files

- **tb_dispatcher.sv** - Main testbench module
- **Makefile** - Build and simulation control
- **README.md** - This documentation
- **library.cfg** - Riviera-PRO library configuration

## Source Dependencies

- **DUT**: `../../src/rtl/dispatcher.sv`
- **Package**: `../../src/include/gemm_pkg.sv`

---

**Created**: Nov 19, 2025
**Status**: ✅ Ready for testing with configurable NUM_TILES
