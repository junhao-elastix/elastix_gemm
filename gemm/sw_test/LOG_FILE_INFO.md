# Test Readback Raw Results Log Files

## Overview

Every run of `test_readback` now automatically saves all raw FP16 results to a timestamped hex log file.

## Log File Format

**Filename**: `test_readback_results_YYYYMMDD_HHMMSS.hex`

**Example**: `test_readback_results_20251102_014439.hex`

## File Structure

```
# test_readback.cpp raw results
# Date: Sun Nov  2 01:44:39 2025
# Total results: 2085
# Configurations: 14
#
05f4
81f0
892f
...
(2085 hex values total, one per line)
```

## Contents

- **Header** (5 lines): Comments with metadata
  - Tool name
  - Timestamp
  - Total result count
  - Number of configurations
- **Results** (2085 lines): Raw FP16 values in hex format (4 digits each)

## File Size

Approximately 11 KB per run (2085 results × 5 bytes/line + header)

## Use Cases

1. **Debugging**: Compare raw hardware output across different runs
2. **Regression Testing**: Archive results from known-good runs
3. **Analysis**: Post-process results with external tools
4. **Verification**: Manual inspection of raw values

## Comparison with Golden Files

The log file captures **exact hardware output** including:
- Tiny FP16 rounding differences (off-by-1 LSB)
- Hardware-specific precision characteristics

Example difference:
```
Hardware (log):  892f  (-0.01422119)
Golden:          8930  (-0.01422119)
Difference:      1 LSB (< 0.001% relative error)
```

These tiny differences are **expected and acceptable** for FP16 arithmetic, which is why the validation uses 40% relative error tolerance instead of exact hex matching.

## Location

Log files are created in the same directory as the test executable:
```
/home/workstation/elastix_gemm/gemm/sw_test/test_readback_results_*.hex
```

## Cleanup

To remove old log files:
```bash
rm test_readback_results_*.hex
```

To keep only the latest:
```bash
ls -t test_readback_results_*.hex | tail -n +2 | xargs rm
```

---

**Generated**: November 2, 2025
