# Obsolete Debug Tests Archive

**Archived**: Thu Oct 9 22:42:22 PDT 2025
**Reason**: Project cleanup - removed development/debug tests after MS2.0 GEMM engine completion

## Contents

This directory contains 32+ test files and executables that were created during the MS2.0 GEMM engine development and debugging process. These tests served their purpose during development but are no longer needed for production validation.

### Categories of Archived Tests

#### 1. Bypass Feature Tests (7+ files)
**Obsolete Reason**: Bypass feature was completely removed during Oct 7, 2025 architecture cleanup
- `test_bypass_check.cpp`
- `test_bypass_data.cpp`
- `test_bypass_debug.cpp`
- `test_bypass_reg_only.cpp`
- `test_bypass_stage1.cpp`
- `test_bypass_stage2b.cpp`
- `test_verify_bypass.cpp`

#### 2. Debug/Diagnostic Utilities (10+ files)
**Obsolete Reason**: One-time debugging tools for specific issues during development
- `check_bypass_status.cpp`
- `check_engine_regs.cpp`
- `check_engine_state.cpp`
- `check_execution.cpp`
- `check_mc_state.cpp`
- `test_engine_status_debug.cpp`
- `test_mc_debug.cpp`
- `test_nap_status.cpp`
- `test_cmd_debug.cpp`
- `test_cmd_queue.cpp`

#### 3. Intermediate Development Tests (10+ files)
**Obsolete Reason**: Replaced by test_ms2_gemm_full.cpp comprehensive test
- `test_dispatcher_bram.cpp`
- `test_dispatcher_path.cpp`
- `test_end_to_end_deadbeef.cpp`
- `test_fetch_debug.cpp`
- `test_fetch_minimal.cpp`
- `test_state_machine_only.cpp`
- `test_matmul_params.cpp`
- `test_tile_enable.cpp`
- `test_v_idx_debug.cpp`
- `test_fifo_signals.cpp`
- `test_full_seq.cpp`

#### 4. Feature-Specific Tests (5+ files)
**Obsolete Reason**: Features tested are now integrated into comprehensive tests
- `test_engine_clock.cpp`
- `test_write_gddr6_ch1.cpp`

## Essential Tests (Kept in sw_test/)

The following 8 tests remain as the production test suite:

1. **DMA_simple_example.cpp** - Basic DMA round-trip validation
2. **DMA_example.cpp** - Advanced DMA with performance metrics
3. **test_registers.cpp** - Device health and register interface
4. **test_gddr6.cpp** - GDDR6 channel status monitoring
5. **test_ms2_gemm_full.cpp** - Complete MS2.0 GEMM engine test
6. **scan_registers.cpp** - Register address space diagnostic
7. **test_mem_endpoints.cpp** - Memory address space validation
8. **test_bram.cpp** - BRAM DMA functionality validation

## Recovery

If any of these archived tests are needed for reference:

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sw_test/obsolete_debug_tests
# Copy specific test back to sw_test/ if needed
```

## Build System

These tests were removed from the Makefile BINS list. To rebuild any archived test:

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sw_test
g++ -std=c++14 -O2 -Wall -Wextra -DDRIVER_ACX \
  -I/home/dev/Dev/acxsdk/include \
  -I/home/dev/Dev/eus/shell/devices/acx/vp815/api \
  obsolete_debug_tests/<test_name>.cpp \
  /home/dev/Dev/eus/shell/devices/acx/vp815/api/vp815.cpp \
  -L/home/dev/Dev/acxsdk/lib \
  -lacxsdk -lacxdev \
  -o <test_name>
```

## Documentation

For development history and rationale behind these tests, see:
- CLAUDE.md - Project evolution notes (Oct 7, 2025 cleanup)
- CHANGELOG.md - Detailed development timeline
- Git history for test-specific development context
