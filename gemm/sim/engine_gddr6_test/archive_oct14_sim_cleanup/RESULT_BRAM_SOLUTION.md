# Result BRAM Solution - Simple 1:1 Mapping

**Date**: October 13, 2025  
**Status**: ✅ **SIMULATION PASSING** - All tests pass  
**Test Results**: B=2, C=2, V=2 → 4 results captured correctly

---

## Problem Statement

The original `result_fifo_to_bram` adapter packed 16 FP16 results into each 256-bit BRAM line. This caused issues in simulation:
- Adapter read from FIFO faster than compute engine produced results
- Complex packing logic made debugging difficult
- Results were captured incorrectly (register values getting stale data)

---

## Solution: Simple 1:1 Result to BRAM Line Mapping

**New module**: `result_fifo_to_simple_bram.sv`

### Key Features

1. **One result per BRAM line** (simple addressing)
   - BRAM line format: `{240'h0, fp16_result[15:0]}`
   - FP16 result in LSB 16 bits, zero-padded to 256 bits

2. **Edge-triggered FIFO reading** (avoids double-reads)
   - Detects `empty → !empty` transition (new data arrival)
   - Throttles reads to prevent spurious accesses
   - Clean flow control for simulation and hardware

3. **First 4 results exposed to registers** (quick access)
   - `o_result_0`, `o_result_1`, `o_result_2`, `o_result_3`
   - Host can read these directly without DMA for small results

4. **Sequential addressing** (easy host readback)
   - Result 0 → BRAM address 0
   - Result 1 → BRAM address 1
   - Result N → BRAM address N

---

## Simulation Results

### Configuration
- **Matrix sizes**: B=2, C=2, V=2
- **Expected results**: 4 (B × C)
- **Test status**: **PASS** ✅

### Actual Results
| Index | HW Result | Golden  | Status | Notes |
|-------|-----------|---------|--------|-------|
| 0     | 0xb414    | 0xb414  | MATCH  | ✅    |
| 1     | 0x2ecb    | 0x2ecb  | MATCH  | ✅    |
| 2     | 0x3344    | 0x3345  | MATCH  | ✅ 1 LSB FP16 rounding |
| 3     | 0x326b    | 0x326b  | MATCH  | ✅    |

### Timing
- **Compute engine latency**: ~134 cycles per result
- **Adapter throttle**: 3-cycle wait between reads
- **Total simulation time**: 13.8µs for 4 results

---

## Host Access Methods

### Method 1: Register Read (Fast, for ≤ 4 results)

For small result sets (B × C ≤ 4), the host can read directly from registers:

```cpp
// Read first 4 results from dedicated registers
uint16_t result_0 = read_register(RESULT_0_REG);  // Address TBD
uint16_t result_1 = read_register(RESULT_1_REG);  // Address TBD
uint16_t result_2 = read_register(RESULT_2_REG);  // Address TBD
uint16_t result_3 = read_register(RESULT_3_REG);  // Address TBD
```

**Advantages**:
- Very fast (single PCIe read per result)
- No DMA setup required
- Good for inference/real-time applications

**Limitations**:
- Only works for ≤ 4 results
- Results must fit in register space

---

### Method 2: DMA from BRAM (Scalable, for > 4 results)

For larger result sets, use DMA to read from result BRAM:

#### Step 1: Setup DMA Transfer
```cpp
// Configure DMA to read from result BRAM
// Each result occupies one 256-bit (32-byte) BRAM line
size_t num_results = B * C;
size_t bytes_per_result = 32;  // 256 bits per BRAM line
size_t total_bytes = num_results * bytes_per_result;

// Setup DMA from result BRAM base address
dma_read(result_bram_base_addr, host_buffer, total_bytes);
```

#### Step 2: Extract Results from Host Buffer
```cpp
// Each BRAM line contains one FP16 result in LSB 16 bits
for (int i = 0; i < num_results; i++) {
    // Read 256-bit line from host buffer
    uint8_t* line_ptr = host_buffer + (i * 32);
    
    // Extract FP16 result from LSB 16 bits
    uint16_t fp16_result = *(uint16_t*)line_ptr;
    
    results[i] = fp16_result;
}
```

#### Alternative: Efficient Packing (Optional)
If bandwidth is critical, you can pack results in software:
```cpp
// Pack 16 FP16 results per DMA line (post-processing)
for (int i = 0; i < num_results; i += 16) {
    uint8_t* packed_line = packed_buffer + (i / 16) * 32;
    for (int j = 0; j < 16 && (i + j) < num_results; j++) {
        uint16_t* result_ptr = (uint16_t*)(packed_line + j * 2);
        *result_ptr = results[i + j];
    }
}
```

---

## BRAM Address Map

| Address Range | Content | Format |
|---|---|---|
| 0x0000 - 0x0FFF | Results 0-4095 | One FP16 per 256-bit line |

**Per-line structure**:
```
Bits [255:16] = 0 (zero-padding)
Bits [15:0]   = FP16 result
```

---

## Hardware Integration Path

### Current Status (Simulation)
- ✅ `engine_top` produces correct results
- ✅ `result_fifo_to_simple_bram` captures all results
- ✅ Results available in BRAM and registers
- ✅ Testbench validates against golden reference

### Next Steps for Hardware

1. **Integrate into `elastix_gemm_top`** (replace existing adapter)
   ```systemverilog
   result_fifo_to_simple_bram i_result_adapter (
       .i_clk(i_nap_clk),
       .i_reset_n(engine_reset_n),
       .i_fifo_rdata(result_fifo_rdata),
       .o_fifo_ren(result_fifo_ren),
       .i_fifo_empty(result_fifo_empty),
       // ... connect to result BRAM and registers
   );
   ```

2. **Map result registers to CSR space** (for Method 1 access)
   ```systemverilog
   assign user_regs_read[RESULT_0] = {16'h0, result_0};
   assign user_regs_read[RESULT_1] = {16'h0, result_1};
   assign user_regs_read[RESULT_2] = {16'h0, result_2};
   assign user_regs_read[RESULT_3] = {16'h0, result_3};
   ```

3. **Connect result BRAM to DMA bridge** (for Method 2 access)
   - Use existing `dma_bram_bridge` infrastructure
   - Configure DMA to read from result BRAM base address

4. **Test on hardware**
   ```cpp
   // Small test (B=2, C=2)
   issue_tile_command(B=2, C=2, V=2);
   wait_for_completion();
   uint16_t r0 = read_register(RESULT_0);  // Should match golden
   
   // Large test (B=128, C=128)
   issue_tile_command(B=128, C=128, V=2);
   wait_for_completion();
   dma_read_results(result_buffer, 128*128*32);  // 16384 results
   ```

---

## Performance Analysis

### Bandwidth Comparison

**Simple adapter** (current):
- One result per BRAM line: 16 bits / 256 bits = **6.25% efficiency**
- For 16384 results: 512 KB transfer (16384 × 32 bytes)

**Packed adapter** (future optimization):
- 16 results per BRAM line: 256 bits / 256 bits = **100% efficiency**
- For 16384 results: 32 KB transfer (1024 × 32 bytes)

### Recommendation
- Use simple adapter for **development and debugging** (easier, proven to work)
- Optimize to packed adapter **later** if bandwidth becomes a bottleneck
- For small matrices (B×C < 1000), bandwidth difference is negligible

---

## Files Modified

1. **New**: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/result_fifo_to_simple_bram.sv`
   - Simple 1:1 result to BRAM adapter
   - Edge-triggered FIFO reading
   - Register exposure for first 4 results

2. **Modified**: `/home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test/tb_engine_gddr6.sv`
   - Updated to use simple adapter
   - Fixed BRAM write monitoring for 1:1 mapping
   - Added adapter debug output

3. **Modified**: `/home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test/Makefile`
   - Replaced `result_fifo_to_bram.sv` with `result_fifo_to_simple_bram.sv`

---

## Conclusion

✅ **Simulation validates the simple result BRAM approach**
- All 4 results captured correctly
- Results match golden reference (within FP16 rounding tolerance)
- Clean, debuggable architecture

**Next**: Integrate into hardware and implement host DMA readback path.

