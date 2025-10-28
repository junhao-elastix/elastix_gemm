# DMA Access Verification Guide

**Date**: October 13, 2025  
**Purpose**: Verify DMA read/write to Result BRAM and GDDR6 before integrating result adapter

---

## Hardware Configuration

### NAP[3][4] - Co-located Resources

**1. Result BRAM** (`i_axi_bram_rsp_dma`)
- **Module**: `dma_bram_bridge` (lines 406-426)
- **Location**: NAP[3][4] - Co-located with engine
- **Purpose**: Stores FP16 computation results from engine
- **Access**: PCIe DMA via BAR1 (verify BAR configuration)
- **Internal writes**: Connected to `result_fifo_to_bram` adapter

**2. GDDR6 NAP Wrapper** (`i_axi_responder_wrapper`)
- **Module**: `nap_responder_wrapper` (lines 502-514)
- **Location**: NAP[3][4] - Same location as BRAM
- **Purpose**: Connects engine to GDDR6 Channel 1 via NoC
- **Access**: Engine FETCH/DISPATCH commands (not direct DMA)
- **Route**: Engine → NAP → NoC → GDDR6_1

---

## Pre-Test Checklist

### 1. **FPGA Status**
```bash
# Check FPGA is programmed
sudo lspci -d 1b59: -vv | grep "Memory at"

# Check ADM status (should be 0x3 = GDDR6 trained)
cd /home/dev/Dev/elastix_gemm/gemm/sw_test
./test_registers | grep "ADM Status"
# Expected: ADM Status: 0x00000003 (GDDR6 trained)
```

### 2. **Verify PCIe BARs**
```bash
sudo lspci -d 1b59: -vv | grep "Region"
```

Expected output (example):
```
Region 0: Memory at ... (32-bit, non-prefetchable) [size=4K]   # Register BAR
Region 1: Memory at ... (32-bit, non-prefetchable) [size=128K] # Result BRAM BAR
Region 2: Memory at ... (64-bit, prefetchable) [size=XXX]      # Other BARs
```

**CRITICAL**: Verify which BAR maps to the result BRAM!
- Check `dma_bram_bridge` instantiation for BAR mapping
- May need to adjust `RESULT_BRAM_BAR` in `test_dma_access.cpp`

### 3. **Build Test**
```bash
cd /home/dev/Dev/elastix_gemm/gemm/sw_test
make test_dma_access
```

---

## Running the Test

### Basic Execution
```bash
# Run DMA access verification
./test_dma_access
```

### Expected Output (Success)

```
========================================
DMA Access Test - Result BRAM & GDDR6
========================================

[Device Health Check]
  ADM Status:    0x00000003 (GDDR6 trained) [OK]
  Test Status:   0x000000XX
  Bitstream ID:  0xXXXXXXXX
  Scratch test:  [PASS]

========================================
Test 1: Result BRAM DMA Access
========================================
[BRAM] Preparing test pattern (256 bytes)...
[BRAM] Writing to Result BRAM via DMA...
[BRAM] Write complete: 256 bytes
[BRAM] Reading back from Result BRAM via DMA...
[BRAM] Read complete: 256 bytes
[BRAM] Verifying data...
[BRAM] Verification: [PASS] All data matches!

========================================
Test 2: Result Register Access
========================================
[REG] Reading result registers...
[REG] Result registers:
      RESULT_0: 0x00000000 (FP16: 0x0000)
      RESULT_1: 0x00000000 (FP16: 0x0000)
      RESULT_2: 0x00000000 (FP16: 0x0000)
      RESULT_3: 0x00000000 (FP16: 0x0000)
[REG] [PASS] Registers accessible

========================================
Test 3: GDDR6 Access Sanity Check
========================================
[GDDR6] ADM Status: 0x00000003 (trained) [OK]
[GDDR6] [PASS] GDDR6 ready for engine access
[GDDR6] Note: Full GDDR6 DMA test requires engine FETCH command

========================================
Test Summary
========================================
Tests passed: 3 / 3

[OVERALL] ALL TESTS PASSED
Ready to integrate result adapter!
```

---

## Troubleshooting

### Issue 1: Device Not Found
```
Failed to initialize device
```

**Solution**:
```bash
# Check device visibility
sudo lspci -d 1b59:

# If not visible, reprogram FPGA
/home/dev/Dev/hex.sh
source /home/dev/rescan
```

### Issue 2: BRAM Write/Read Failed
```
[BRAM] Write failed: wrote 0 bytes, expected 256
```

**Possible Causes**:
1. **Wrong BAR number** - Check PCIe BAR configuration
   ```bash
   sudo lspci -d 1b59: -vv | grep "Region"
   ```
   Update `RESULT_BRAM_BAR` in `test_dma_access.cpp`

2. **BAR not mapped** - DMA BRAM bridge may not be accessible via BAR
   - Check `dma_bram_bridge` module for AXI interface exposure
   - Verify PCIe-to-AXI bridge configuration

3. **Permission denied** - Need root/sudo for BAR access
   ```bash
   sudo ./test_dma_access
   ```

### Issue 3: Data Mismatch
```
[BRAM] Mismatch at word 0: wrote 0xdeadbeef, read 0xffffffff
```

**Possible Causes**:
1. **Device hung** - All 0xFFFFFFFF indicates PCIe link down
   ```bash
   /home/dev/Dev/hex.sh
   source /home/dev/rescan
   ```

2. **BRAM addressing issue** - Check offset/alignment
   - Verify `RESULT_BRAM_BASE` is correct
   - Try different base addresses

3. **Clock domain issues** - BRAM and PCIe on different clocks
   - Check `i_clk` connection in `dma_bram_bridge`
   - Should be `i_nap_clk` (lines 415)

### Issue 4: ADM Status Not 0x3
```
[GDDR6] ADM Status: 0x00000001 (GDDR6 not ready) [WARN]
```

**Solution**: Wait for GDDR6 training or reboot
```bash
# Check if training is in progress
watch -n 1 './test_registers | grep ADM'

# If stuck, reboot system
sudo reboot
```

---

## What This Test Verifies

### ✅ Verified by Test
1. **Result BRAM accessible via DMA write**
   - Host can write test data to result BRAM
   - Confirms PCIe → BRAM path works

2. **Result BRAM accessible via DMA read**
   - Host can read back data from result BRAM  
   - Confirms BRAM → PCIe path works

3. **Result registers accessible**
   - Can read first 4 result registers
   - Confirms register interface works

4. **GDDR6 trained and ready**
   - ADM status shows GDDR6 channels trained
   - Engine can access GDDR6 for FETCH operations

### ⚠️ NOT Verified by Test
1. **Engine writing to result BRAM**
   - This test writes via DMA, not via engine
   - Engine write path verified separately in simulation

2. **GDDR6 read/write via engine**
   - Requires engine FETCH/DISPATCH commands
   - Tested separately with `test_ms2_gemm_full`

---

## Next Steps After Test Passes

### 1. Integrate Result Adapter into Hardware

Update `elastix_gemm_top.sv` line 631:
```systemverilog
// Replace:
result_fifo_to_bram i_result_adapter (

// With:
result_fifo_to_simple_bram i_result_adapter (
```

Add to file list (wherever RTL is compiled):
```makefile
$(GEMM_RTL_DIR)/result_fifo_to_simple_bram.sv
```

### 2. Rebuild and Reflash
```bash
cd /home/dev/Dev/eus/shell_hw/vec_add/build
make clean && make all
/home/dev/Dev/hex.sh
source /home/dev/rescan
```

### 3. Verify Results via DMA
After running a GEMM operation:
```bash
# Run computation
./test_ms2_gemm_full

# Read results via DMA (using updated test)
./test_dma_access  # Should show actual FP16 results in registers
```

### 4. Test End-to-End Flow
```cpp
// Pseudocode for full test:
1. Write matrices to GDDR6 (via engine or DMA)
2. Issue GEMM command (FETCH, DISPATCH, TILE)
3. Wait for completion
4. Read results from result BRAM via DMA
5. Verify against golden reference
```

---

## Important Notes

⚠️ **BAR Configuration Critical**
- The test assumes Result BRAM is accessible via BAR1
- **You MUST verify** the correct BAR number for your PCIe configuration
- Check hardware synthesis logs or PCIe configuration

⚠️ **GDDR6 Access**
- Direct DMA to GDDR6 may not be possible
- Engine FETCH commands route through NoC to GDDR6
- For GDDR6 verification, use engine commands, not raw DMA

⚠️ **Clock Domains**
- Result BRAM runs on `i_nap_clk` (line 415)
- PCIe interface may run on `i_reg_clk`
- Ensure proper clock domain crossing in `dma_bram_bridge`

---

## Success Criteria

Before integrating the result adapter, you need:
- ✅ All 3 tests passing
- ✅ BRAM DMA write/read working correctly
- ✅ Result registers accessible
- ✅ GDDR6 trained (ADM status = 0x3)
- ✅ No device hangs or PCIe errors

Once all verified → **Ready to integrate `result_fifo_to_simple_bram`!**

