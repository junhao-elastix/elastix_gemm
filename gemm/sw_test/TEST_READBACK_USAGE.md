# test_readback Command-Line Options

## Overview

`test_readback` now supports flexible output verbosity levels and configurable stress testing via command-line arguments.

## Usage

```bash
./test_readback [OPTIONS]
```

## Options

| Option | Description | Default |
|--------|-------------|---------|
| `-v` | Verbose mode - print everything | Off |
| `-t` | Timing mode - print timing info and summaries only | Off |
| `-s <number>` | Stress factor (number of test iterations) | 1 |
| `-h` | Display help message | - |

## Output Modes

### Default Mode (no flags)

**Usage**: `./test_readback` or `./test_readback -s 10`

**Prints**:
- Validation Summary
- Performance Summary
- Final pass/fail status

**Does NOT print**:
- Step-by-step progress
- Per-config timing
- Detailed timing averages
- DMA transfer details
- Buffer management details

**Use case**: Quick validation runs where you only care about final results and throughput.

### Timing Mode (`-t`)

**Usage**: `./test_readback -t` or `./test_readback -t -s 5`

**Prints**:
- Initial banner with configuration
- Per-config timing for each iteration
- Validation Summary
- Timing Summary (averages across all iterations)
- Performance Summary
- Final pass/fail status

**Does NOT print**:
- Step-by-step progress details
- DMA transfer details
- Buffer management details

**Use case**: Performance benchmarking and timing analysis.

### Verbose Mode (`-v`)

**Usage**: `./test_readback -v` or `./test_readback -v -s 2`

**Prints**:
- Everything! Complete step-by-step execution trace
- All headers (Step 1, Step 2, etc.)
- Loading progress
- DMA transfer notifications
- FETCH/DISPATCH/TILE execution
- Per-config timing
- Buffer management (rd_ptr, wr_ptr, polling)
- Readback threshold triggers
- Validation Summary
- Timing Summary
- Performance Summary
- Final pass/fail status

**Use case**: Debugging, development, understanding test flow.

## Stress Factor (`-s`)

The stress factor determines how many times the full test suite runs.

**Examples**:
- `-s 1` (default): Run all 14 configs once → 2,085 results
- `-s 10`: Run all 14 configs 10 times → 20,850 results
- `-s 100`: Run all 14 configs 100 times → 208,500 results

**Total iterations** = `14 configs × stress_factor`

## Examples

### Quick validation (default mode)
```bash
./test_readback
```
Output:
```
========================================================================
Validation Summary
========================================================================
Total results validated: 2085
Mismatches: 0
Match rate: 100%
...
========================================================================
Performance Summary
========================================================================
Total multiplications:  268288000
Total time:             0.523 seconds
...
✅ ALL RESULTS MATCH! TEST PASSED!
```

### Timing analysis with 10x stress
```bash
./test_readback -t -s 10
```
Output includes per-config timing and averaged timing summary.

### Full debug trace
```bash
./test_readback -v
```
Output includes complete execution trace with all details.

### Stress test with performance metrics
```bash
./test_readback -s 100
```
Runs 1,400 total iterations (14 configs × 100), prints only summaries.

## Output Sections

### Validation Summary (always printed)
- Total results validated
- Number of mismatches
- Match rate percentage
- RMSE (Root Mean Square Error)
- Maximum absolute error

### Timing Summary (printed in `-v` and `-t` modes)
- Average command timings:
  - FETCH left
  - FETCH right
  - DISPATCH left
  - DISPATCH right
  - TILE loop total
  - wait_idle total
  - Per tile average
- Total tiles executed
- Average tiles per config

### Performance Summary (always printed)
- Total multiplications performed
- Total execution time (seconds)
- Throughput:
  - Multiplications/second
  - GMUL/s (billions)
  - TMUL/s (trillions)

## Technical Details

### Multiplication Calculation
For each configuration:
```
total_multiplications = num_tiles × B × C × V × 128
```

Where:
- `num_tiles` = min(128/(B×V), 128/(C×V))
- `B`, `C`, `V` = configuration parameters
- Each output element (B×C per tile) requires V×128 MAC operations

### Timing Measurements
Timing is captured using `std::chrono::high_resolution_clock` for precision:
- **FETCH left/right**: Includes wait_idle for completion
- **DISPATCH left/right**: Includes waitDispatch for acknowledgment
- **TILE loop**: Total time for all tiles in config
- **wait_idle**: Accumulated across all tiles

### Log Files
Every run automatically saves raw FP16 results to:
```
test_readback_results_YYYYMMDD_HHMM.hex
```
This happens regardless of verbosity mode for post-analysis.

## Recommendations

- **Development**: Use `-v` for debugging and understanding behavior
- **CI/CD**: Use default mode for pass/fail validation
- **Benchmarking**: Use `-t -s <large number>` for performance characterization
- **Stress Testing**: Use `-s 100` or higher to validate reliability

---

**Last Updated**: November 2, 2025
