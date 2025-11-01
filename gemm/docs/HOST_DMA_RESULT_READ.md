# Host DMA Result Read Protocol

**Module**: `result_fifo_to_simple_bram.sv` → `dma_bram_bridge.sv` → PCIe
**Date**: October 31, 2025
**Architecture**: Packed FP16 Result Buffer with Circular FIFO

---

## Overview

The GEMM engine writes FP16 results to a circular FIFO implemented in BRAM. The host reads these results via PCIe DMA after monitoring the `write_top` counter to determine available data.

### System Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    GEMM Compute Engine                           │
│                          ↓ FP16 results                          │
│                  result_bram (256×16-bit FIFO)                   │
│                          ↓                                       │
│              result_fifo_to_simple_bram (packing)                │
│         • Packs 16 FP16s per 256-bit BRAM line                   │
│         • Circular buffer: 512 lines × 16 results = 8192 results │
│         • Exposes write_top counter to host                      │
│                          ↓                                       │
│                  dma_bram_bridge (AXI responder)                 │
│         • BRAM_SIMPLE instance (512×256-bit)                     │
│         • PCIe BAR2 memory-mapped access                         │
│                          ↓                                       │
│                    PCIe Gen5 x16 Interface                       │
│                          ↓                                       │
│                      Host CPU/Memory                             │
└─────────────────────────────────────────────────────────────────┘
```

---

## Step-by-Step Host Read Protocol

### 1. Check Result Availability

**Read MMIO Register 139 (BAR0, Offset 0x22C)**

```c
// PCIe BAR0 base address (control registers)
volatile uint32_t *bar0 = pcie_bar0_base;

// Read write_top counter (13-bit value)
uint32_t write_top = bar0[139] & 0x1FFF;  // Mask to 13 bits

// Calculate number of results available
uint32_t results_available = write_top;

printf("Results available: %u FP16 values\n", results_available);
```

**Register Format**:
```
BAR0[139] = ENGINE_WRITE_TOP
  [31:13] - Reserved (read as 0)
  [12:0]  - write_top: Number of FP16 results processed by engine
```

**Important**: `write_top` counts ALL results processed, including any in the packing buffer that haven't been written to BRAM yet. For DMA reads, only complete BRAM lines are accessible.

---

### 2. Calculate DMA Parameters

**Determine Readable Results**:
```c
// Only complete BRAM lines are readable
// Each line contains 16 FP16 results
uint32_t complete_lines = results_available / 16;
uint32_t readable_results = complete_lines * 16;

// Calculate byte count for DMA
// Each FP16 = 2 bytes, 16 FP16s = 32 bytes per line
uint32_t bytes_to_read = complete_lines * 32;

printf("Complete lines: %u\n", complete_lines);
printf("Readable results: %u (0x%X FP16 values)\n",
       readable_results, readable_results);
printf("DMA transfer size: %u bytes (0x%X)\n",
       bytes_to_read, bytes_to_read);
```

**Example Calculation**:
- `write_top = 165` results
- Complete lines = 165 / 16 = 10 lines
- Readable results = 10 × 16 = 160 FP16 values
- DMA size = 10 × 32 = 320 bytes
- Buffered (not yet readable) = 165 - 160 = 5 results

---

### 3. Perform DMA Read from BAR2

**BAR2 Memory Map**:
```
BAR2 Base: Result BRAM (512 lines × 32 bytes = 16KB total)
  Offset 0x0000: Line 0  (Results 0-15)    [32 bytes]
  Offset 0x0020: Line 1  (Results 16-31)   [32 bytes]
  Offset 0x0040: Line 2  (Results 32-47)   [32 bytes]
  ...
  Offset 0x1FE0: Line 255 (Results 4080-4095) [32 bytes]

Note: With packing optimization, effective capacity is 8192 results
      due to circular addressing, but only 512 BRAM lines physically exist
```

**DMA Read Implementation**:
```c
// PCIe BAR2 base address (result BRAM)
volatile uint8_t *bar2 = pcie_bar2_base;

// Allocate host buffer for results
uint16_t *host_buffer = malloc(readable_results * sizeof(uint16_t));

// Perform DMA read
// Option 1: Direct memcpy (for small transfers)
memcpy(host_buffer, bar2, bytes_to_read);

// Option 2: PCIe DMA engine (for large transfers, better performance)
pcie_dma_read(bar2_address, host_buffer, bytes_to_read);

printf("DMA transfer complete: %u bytes read\n", bytes_to_read);
```

---

### 4. Parse Packed Results

**BRAM Line Format** (256 bits = 32 bytes):
```
Bit Layout (little-endian):
  [15:0]    - Result 0  (FP16)
  [31:16]   - Result 1  (FP16)
  [47:32]   - Result 2  (FP16)
  ...
  [239:224] - Result 14 (FP16)
  [255:240] - Result 15 (FP16)

Byte Layout in Memory:
  Offset +0x00: Result 0  [byte 0-1]
  Offset +0x02: Result 1  [byte 2-3]
  Offset +0x04: Result 2  [byte 4-5]
  ...
  Offset +0x1C: Result 14 [byte 28-29]
  Offset +0x1E: Result 15 [byte 30-31]
```

**Parsing Code**:
```c
// Results are already correctly ordered in host_buffer
// due to little-endian byte ordering match

// Process results
for (uint32_t i = 0; i < readable_results; i++) {
    uint16_t fp16_value = host_buffer[i];

    // Convert FP16 to FP32 for processing
    float fp32_value = fp16_to_fp32(fp16_value);

    printf("Result[%4u] = 0x%04X (FP16) = %.6f (FP32)\n",
           i, fp16_value, fp32_value);
}

free(host_buffer);
```

---

### 5. Clear Results (Optional)

**Reset write_top Counter**:

After reading and processing results, the host can reset the counter to allow the BRAM to be reused from the beginning:

```c
// Write 0x00000000 to register 139 to reset
bar0[139] = 0x00000000;

// This triggers:
//   1. Flush any partial results in packing buffer to BRAM
//   2. Reset write_top counter to 0
//   3. Reset BRAM write address to line 0

// Wait a few cycles for reset to complete
usleep(10);  // 10 microseconds

// Verify reset
uint32_t new_write_top = bar0[139] & 0x1FFF;
printf("write_top after reset: %u (expected: 0)\n", new_write_top);
```

**Reset Behavior**:
1. Any buffered results (1-15 FP16s in packing buffer) are written to BRAM
2. `write_top` counter resets to 0
3. Internal packing position resets to 0
4. Next results will start writing at BRAM line 0 (circular overwrite)

---

## Complete Example Code

```c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>

// PCIe BAR addresses (obtained from pcie_open/mmap)
extern volatile uint32_t *bar0;  // Control registers
extern volatile uint8_t *bar2;   // Result BRAM

// FP16 to FP32 conversion (IEEE 754 half → single precision)
float fp16_to_fp32(uint16_t fp16) {
    uint32_t sign = (fp16 >> 15) & 0x1;
    uint32_t exp = (fp16 >> 10) & 0x1F;
    uint32_t mant = fp16 & 0x3FF;

    uint32_t fp32;
    if (exp == 0) {
        if (mant == 0) {
            // Zero
            fp32 = sign << 31;
        } else {
            // Denormalized
            exp = 127 - 15 + 1;
            while (!(mant & 0x400)) {
                mant <<= 1;
                exp--;
            }
            mant &= 0x3FF;
            fp32 = (sign << 31) | (exp << 23) | (mant << 13);
        }
    } else if (exp == 31) {
        // Inf or NaN
        fp32 = (sign << 31) | (0xFF << 23) | (mant << 13);
    } else {
        // Normalized
        fp32 = (sign << 31) | ((exp + 127 - 15) << 23) | (mant << 13);
    }

    return *(float*)&fp32;
}

int read_gemm_results(void) {
    // Step 1: Check availability
    uint32_t write_top = bar0[139] & 0x1FFF;
    printf("[Host] write_top = %u results\n", write_top);

    if (write_top == 0) {
        printf("[Host] No results available\n");
        return 0;
    }

    // Step 2: Calculate DMA parameters
    uint32_t complete_lines = write_top / 16;
    uint32_t readable_results = complete_lines * 16;
    uint32_t bytes_to_read = readable_results * 2;  // 2 bytes per FP16

    printf("[Host] Readable: %u results (%u complete lines)\n",
           readable_results, complete_lines);
    printf("[Host] DMA size: %u bytes\n", bytes_to_read);

    if (readable_results == 0) {
        printf("[Host] Less than 16 results, waiting for more data\n");
        return 0;
    }

    // Step 3: Allocate buffer
    uint16_t *results = malloc(bytes_to_read);
    if (!results) {
        fprintf(stderr, "[Host] Failed to allocate buffer\n");
        return -1;
    }

    // Step 4: DMA read from BAR2
    memcpy(results, bar2, bytes_to_read);
    printf("[Host] DMA read complete\n");

    // Step 5: Process results
    printf("[Host] Processing %u FP16 results:\n", readable_results);
    for (uint32_t i = 0; i < readable_results; i++) {
        float value = fp16_to_fp32(results[i]);

        // Print first 10 and last 10 results
        if (i < 10 || i >= readable_results - 10) {
            printf("  Result[%4u] = 0x%04X = %10.6f\n",
                   i, results[i], value);
        } else if (i == 10) {
            printf("  ... (%u results omitted) ...\n",
                   readable_results - 20);
        }
    }

    free(results);

    // Step 6: Optional - Reset counter for next batch
    printf("[Host] Resetting write_top counter\n");
    bar0[139] = 0x00000000;
    usleep(10);

    // Verify reset
    uint32_t new_write_top = bar0[139] & 0x1FFF;
    if (new_write_top == 0) {
        printf("[Host] Counter reset successful\n");
    } else {
        fprintf(stderr, "[Host] Counter reset failed: %u\n", new_write_top);
    }

    return readable_results;
}

int main() {
    // Initialize PCIe device (device-specific)
    // pcie_init(&bar0, &bar2);

    // Read results
    int results_read = read_gemm_results();

    printf("[Host] Total results processed: %d\n", results_read);

    return 0;
}
```

---

## Performance Considerations

### DMA Transfer Optimization

1. **Burst Size**: PCIe DMA works best with aligned, large transfers
   - Minimum recommended: 64 bytes (2 BRAM lines, 32 results)
   - Optimal: 256-4096 bytes (8-128 lines, 128-2048 results)

2. **Polling Interval**: Check `write_top` register periodically
   ```c
   while (1) {
       uint32_t write_top = bar0[139] & 0x1FFF;
       if (write_top >= BATCH_SIZE) {
           read_gemm_results();
       }
       usleep(100);  // 100µs polling interval
   }
   ```

3. **Backpressure Monitoring** (future):
   ```c
   // Check almost_full flag (when connected to register)
   uint32_t status = bar0[STATUS_REG];
   if (status & ALMOST_FULL_BIT) {
       printf("[Host] Warning: Result buffer almost full!\n");
       // Urgent: read results immediately
       read_gemm_results();
   }
   ```

---

## Troubleshooting

### Issue 1: Reading Garbage Data
**Symptom**: Random or incorrect FP16 values
**Cause**: Reading partial BRAM lines (not 16-aligned)
**Solution**: Always read `(write_top / 16) * 16` results

### Issue 2: write_top Not Incrementing
**Symptom**: Counter stuck at 0
**Cause**: GEMM engine not running or FIFO interface issue
**Solution**: Check engine status registers, verify matrix commands sent

### Issue 3: Circular Buffer Overrun
**Symptom**: Oldest results overwritten before host reads
**Cause**: Host read rate < engine write rate
**Solution**: Increase polling frequency, implement backpressure handling

### Issue 4: DMA Timeout
**Symptom**: BAR2 read hangs or times out
**Cause**: BRAM bridge not responding, PCIe link issue
**Solution**: Check PCIe link status, verify bitstream programmed correctly

---

## Register Summary

| Register | Offset | Access | Width | Description |
|----------|--------|--------|-------|-------------|
| **ENGINE_WRITE_TOP** | 0x22C | R/W | 13-bit | Result counter and reset |

### ENGINE_WRITE_TOP (Register 139)
```
Read:  [12:0] = Number of FP16 results processed
Write: 0x00000000 = Reset counter and flush buffer
```

---

## Memory Map Summary

| Resource | Base Address | Size | Contents |
|----------|-------------|------|----------|
| **BAR0** | PCIe BAR0 | 532 bytes | Control registers (133 × 4 bytes) |
| **BAR2** | PCIe BAR2 | 16 KB | Result BRAM (512 lines × 32 bytes) |

### BAR2 Address Mapping
```
0x0000: Line 0   → Results [0:15]
0x0020: Line 1   → Results [16:31]
0x0040: Line 2   → Results [32:47]
...
0x3FE0: Line 511 → Results [8176:8191]

Note: With circular addressing, reading beyond write_top
      position will return stale data from previous iteration
```

---

## Integration Checklist

- [x] `result_fifo_to_simple_bram.sv` packing logic implemented
- [x] `write_top` counter connected to register 139
- [x] `write_top_reset` control signal connected
- [x] BAR2 mapped to result BRAM via `dma_bram_bridge.sv`
- [ ] `almost_full` signal connected to status register (future)
- [ ] Interrupt generation on threshold (future enhancement)
- [ ] Host software library implementation
- [ ] Performance benchmarking

---

**Document Version**: 1.0
**Last Updated**: October 31, 2025
**Status**: Ready for hardware integration and testing
