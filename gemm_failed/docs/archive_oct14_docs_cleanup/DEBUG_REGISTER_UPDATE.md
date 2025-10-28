# Debug Register Addition - Register Map Update

**Date**: October 13, 2025  
**Purpose**: Added dispatcher debug registers to diagnose FETCH data path issues

## New Debug Registers Added

| Register | Address | Offset | Description |
|----------|---------|--------|-------------|
| DC_BRAM_WR_COUNT | 24 | 0x60 | Dispatcher BRAM write count {22'h0, count[9:0]} |
| DC_DEBUG | 25 | 0x64 | Dispatcher state debug {28'h0, dc_state[3:0]} |

## Register Map Changes

Adding 2 new debug registers shifted all subsequent registers by +8 bytes:

### Before (NUM_USER_REGS = 137):
| Register | Old Reg# | Old Offset |
|----------|----------|------------|
| LTSSM_STATE_REG | 129 | 0x204 |
| ADM_STATUS_REG | 130 | 0x208 |
| BITSTREAM_ID | 131 | 0x20C |
| SCRATCH_REG | 132 | 0x210 |
| RESULT_REG_0 | 133 | 0x214 |
| RESULT_REG_1 | 134 | 0x218 |
| RESULT_REG_2 | 135 | 0x21C |
| RESULT_REG_3 | 136 | 0x220 |

### After (NUM_USER_REGS = 139):
| Register | New Reg# | New Offset | Change |
|----------|----------|------------|--------|
| LTSSM_STATE_REG | 131 | 0x20C | +8 bytes |
| ADM_STATUS_REG | 132 | 0x210 | +8 bytes |
| BITSTREAM_ID | 133 | 0x214 | +8 bytes |
| SCRATCH_REG | 134 | 0x218 | +8 bytes |
| RESULT_REG_0 | 135 | 0x21C | +8 bytes |
| RESULT_REG_1 | 136 | 0x220 | +8 bytes |
| RESULT_REG_2 | 137 | 0x224 | +8 bytes |
| RESULT_REG_3 | 138 | 0x228 | +8 bytes |

## Files Updated

### RTL Files:
- `src/rtl/elastix_gemm_top.sv`:
  - Added DC_BRAM_WR_COUNT and DC_DEBUG register definitions
  - Updated IRQ_GEN_REGS_BASE from 24 to 26
  - Updated NUM_USER_REGS from 137 to 139
  - Updated all register number calculations
  - Connected bram_wr_count signal (was unused)
  - Added register read assignments for new debug registers

### Software Test Files:
All register offset updates from 0x204-0x220 → 0x20C-0x228:

1. `test_registers.cpp` - System register test
2. `test_ms2_gemm_full.cpp` - Full GEMM test
3. `test_dma_access.cpp` - DMA verification test
4. `test_simple_bcv2.cpp` - BCV test
5. `test_bcv2_correct_encoding.cpp` - BCV encoding test
6. `test_bcv2_debug.cpp` - BCV debug test
7. `test_bcv_2_fixed.cpp` - BCV fixed test
8. `check_engine_debug.cpp` - Engine debug utility
9. `test_result_regs.cpp` - Result register test
10. `test_gddr6.cpp` - GDDR6 status test
11. `debug_result_capture.cpp` - Result capture debug
12. `DMA_simple_example.cpp` - Fixed typo (ACX_GDDR6cd → ACX_GDDR6_SPACE)

## Usage - New Debug Registers

### DC_BRAM_WR_COUNT (0x60)
```cpp
uint32_t bram_wr_count = device.mmioRead32(0, 0x60);
uint32_t count = bram_wr_count & 0x3FF;  // Extract [9:0]
cout << "Dispatcher BRAM write count: " << count << endl;
```

**Purpose**: Verify that FETCH commands actually write data to internal BRAMs
- Should be 528 after fetching left matrix
- Should be 1056 after fetching both left and right matrices

### DC_DEBUG (0x64)
```cpp
uint32_t dc_debug = device.mmioRead32(0, 0x64);
uint32_t dc_state = dc_debug & 0xF;  // Extract [3:0]
cout << "Dispatcher state: " << dc_state << endl;
```

**Purpose**: Monitor dispatcher control FSM state
- 0 = IDLE (ready for FETCH)
- Non-zero = Active fetching/dispatching

## Testing Status

- ✅ RTL updated and builds successfully
- ✅ All software tests compiled successfully
- ⏳ Hardware not yet flashed with new bitstream
- ⏳ New debug registers not yet tested

## Next Steps

1. Flash FPGA with new bitstream (build completed at 23:27)
2. Run test_ms2_gemm_full to reproduce inf/-inf/0 results
3. Read DC_BRAM_WR_COUNT after FETCH to verify data loading
4. Read DC_DEBUG to monitor dispatcher state
5. Determine if FETCH is actually populating the internal BRAMs

This will help identify whether the problem is:
- GDDR6 → Dispatcher (FETCH not working)
- Dispatcher → Compute Engine (data path broken)
- Compute Engine itself (producing garbage output)
