# Model Converter Integration with Elastix GEMM

**Date**: November 2, 2025
**Status**: ✅ Active Integration

---

## Overview

The **model_converter** project is a compiler/runtime framework that generates optimized execution schedules for GFP (Group Floating Point) matrix operations on the **elastix_gemm** FPGA hardware accelerator. It sits as the high-level software stack on top of the MS2.0 GEMM engine we've been developing.

## Project Locations

| Component | Path | Description |
|-----------|------|-------------|
| **FPGA Hardware** | `/home/workstation/elastix_gemm/gemm/` | RTL design, synthesis, testing |
| **Model Converter** | `/home/workstation/ElastiCore/projects/model_converter/` | IR compiler, scheduler, runtime |
| **Achronix Backend** | `/home/workstation/ElastiCore/projects/model_converter/src/model_converter/backends/achronix/` | Hardware-specific runtime |

---

## Architecture Stack

```
┌─────────────────────────────────────────────────────┐
│  User Application (PyTorch Models, etc.)            │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────┐
│  Model Converter (Python)                           │
│  - IR Builder: Translates models to GFP IR          │
│  - Scheduler: Optimizes operation ordering          │
│  - Pipeline: Generates hardware schedules           │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────┐
│  Achronix Backend (C++ with Python bindings)        │
│  - elastiapi.hpp: High-level command API            │
│  - elastilib.cpp: Python bindings (pybind11)        │
│  - vp815.cpp/hpp: Device interface                  │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼ PCIe Gen5 x16
┌─────────────────────────────────────────────────────┐
│  Elastix GEMM Hardware (FPGA)                       │
│  - MS2.0 GEMM Engine (AC7t1500)                     │
│  - Circular Buffer (8192 FP16 results)              │
│  - GDDR6 Channels (16GB total)                      │
│  - Command Processor (5-opcode microcode)           │
└─────────────────────────────────────────────────────┘
```

---

## Key Components

### 1. Model Converter IR (Intermediate Representation)

**Purpose**: Platform-independent representation of matrix operations with GFP data types.

**Features**:
- GFP tensor types with configurable group size and axis
- Operations: `mat_mul`, `elmwise_add`, `slice_view`, `channel_view`
- Memory hierarchy: `host` → `dram` → `bram`
- Execution constructs: `pipeline`, `parallel`, `for`

**Example IR** (from README.md):
```python
mat_mul operands (%0, %constant_0) dests (%1)
  (gfp_tensor<2x?1024x4096xgfp<m8e5>, axis=-1, size=32, host>,
   gfp_tensor<4096x128xgfp<m8e5>, axis=-2, size=32, host>)
  -> (gfp_tensor<2x?1024x128xgfp<m22e6>, host>)
  attrs { mode: MatMulMode.LINEAR }
```

### 2. Scheduler

**Purpose**: Transforms high-level IR into hardware-specific execution schedule.

**Optimizations**:
- **Data Tiling**: Breaks large matrices into BRAM-sized chunks (256×4 typical)
- **Pipeline Generation**: Overlaps data movement (DMA) with computation
- **Channel Distribution**: Maps operations across 16 GDDR6 channels
- **Memory Hierarchy**: `shell_dma` (host→GDDR6), `fpga_dma` (GDDR6→BRAM)

**Key Transforms**:
- `alloc_dram`: Allocates GDDR6 memory channels
- `alloc_bram`: Allocates BRAM resources (16×16 distribution)
- `slice_view`: Creates tensor views for tiling
- `channel_view`: Maps to specific GDDR6/BRAM channels

### 3. Achronix Backend (`elastiapi.hpp`)

**Purpose**: C++ runtime API for controlling the FPGA hardware.

**Command Interface**:
```cpp
class VP815Device {
public:
    // Matrix Data Loading
    uint8_t fetch(uint32_t startAddr, uint16_t length, bool fetch_right);

    // Vector Configuration
    uint8_t dispatch(uint8_t man_nv_cnt, uint8_t ugd_vec_size,
                     uint16_t tile_addr, bool disp_right, ...);

    // Matrix Multiplication
    uint8_t tile(uint16_t leftAddr, uint16_t rightAddr,
                 uint16_t leftUgdLen, uint16_t rightUgdLen,
                 uint16_t vecLen, ...);

    // Synchronization
    uint8_t waitDispatch(uint8_t waitId);
    uint8_t waitTile(uint8_t waitId);
    bool waitIdle(uint32_t timeout_ms);

    // Result Retrieval
    void requestOutput(uint64_t numElements, BlockT &hostBlock);
    void readPendingOutput();
};
```

**Opcode Definitions** (lines 18-22):
```cpp
constexpr uint8_t OPC_FETCH = 0xF0;          // Load matrix from GDDR6 → BRAM
constexpr uint8_t OPC_DISPATCH = 0xF1;       // Configure vector dispatch
constexpr uint8_t OPC_MATMUL = 0xF2;         // Execute matrix multiplication
constexpr uint8_t OPC_WAIT_DISPATCH = 0xF3;  // Synchronization barrier
constexpr uint8_t OPC_WAIT_MATMUL = 0xF4;    // Final barrier
```

### 4. Python Bindings (`elastilib.cpp`)

**Purpose**: Expose C++ API to Python for integration with ML frameworks.

**Implementation**: Uses pybind11 to wrap `VP815Device` class.

**Build System**:
```bash
cd /home/workstation/ElastiCore/projects/model_converter/src/model_converter/backends/achronix/
python setup.py build_ext --inplace
```

**Output**: `elastilib.cpython-313-x86_64-linux-gnu.so`

---

## Shared Documentation

### Circular Buffer Register Access

Both projects share the same circular buffer interface:

**Register Map** (from `CIRCULAR_BUFFER_REGISTER_ACCESS.md`):
| Register | Offset | Access | Description |
|----------|--------|--------|-------------|
| `REG_RD_PTR` | 0x230 | RW | Host read pointer |
| `REG_WR_PTR` | 0x234 | RO | Hardware write pointer |
| `REG_USED_ENTRIES` | 0x238 | RO | Available results count |
| `ENGINE_WRITE_TOP` | 0x22C | Trigger | Reset wr_ptr (init only!) |

**Capacity**: 8192 FP16 results (16KB)

**Reference Implementations**:
- Elastix GEMM: `/home/workstation/elastix_gemm/gemm/sw_test/test_readback.cpp`
- Model Converter: `/home/workstation/ElastiCore/projects/model_converter/src/model_converter/backends/achronix/elastiapi.hpp`

---

## Data Flow Example

### Step 1: Model Definition (Python)
```python
# High-level matrix multiplication
result = model_converter.matmul(input_tensor, weight_tensor)
```

### Step 2: IR Generation
```python
module {
  func @test_host operands (%input, %weight) dests (%output) {
    mat_mul operands (%input, %weight) dests (%output)
    return
  }
}
```

### Step 3: Scheduling
- Tiles large matrix into 256×4 chunks
- Generates DMA transfers: host → GDDR6 → BRAM
- Creates pipeline: fetch → dispatch → compute

### Step 4: Code Generation (C++)
```cpp
// elastiapi.hpp calls:
device.fetch(GDDR6_BASE_LEFT, left_lines, false);
device.fetch(GDDR6_BASE_RIGHT, right_lines, true);
device.dispatch(man_nv_cnt, ugd_vec_size, tile_addr, false, ...);
device.dispatch(man_nv_cnt, ugd_vec_size, tile_addr, true, ...);
device.tile(left_addr, right_addr, B, C, V, ...);
device.waitTile(tile_id);
device.requestOutput(num_results, host_buffer);
```

### Step 5: Hardware Execution
- Command processor parses 5-opcode microcode
- Master control FSM orchestrates data flow
- Dispatcher fetches data from GDDR6
- Compute engine performs GFP8 matrix multiplication
- Results written to circular buffer as FP16
- Host reads via DMA when threshold reached

---

## Testing Relationship

### Elastix GEMM Tests

| Test | Purpose | Model Converter Equivalent |
|------|---------|----------------------------|
| `test_gemm.cpp` | 3-stage circular buffer validation | Unit test for `elastiapi.hpp` |
| `test_readback.cpp` | Batched readback stress test | Production readback pattern |
| `test_multi_tile.cpp` | Multi-tile configurations | Scheduler output validation |

### Model Converter Tests

Located in: `/home/workstation/ElastiCore/projects/model_converter/src/model_converter/main.py`

**Workflow**:
1. **Before scheduling**: High-level IR (linear operations)
2. **After scheduling**: Hardware-specific IR (tiled, pipelined)
3. **After emulation**: Numerical validation (RMSE comparison)

**Metrics**:
- IR-Emu RMSE: 0.0005 (IR execution vs emulator)
- Ref-Emu RMSE: 0.0119 (reference vs emulator)
- Ref-IR RMSE: 0.0118 (reference vs IR)

---

## Command Correspondence

| Model Converter | Elastix GEMM Test | Opcode | Hardware Module |
|----------------|------------------|--------|-----------------|
| `device.fetch(...)` | `gemm_device.fetch(...)` | 0xF0 | `dispatcher_control.sv` |
| `device.dispatch(...)` | `gemm_device.dispatch(...)` | 0xF1 | `master_control.sv` |
| `device.tile(...)` | `gemm_device.tile(...)` | 0xF2 | `compute_engine_modular.sv` |
| `device.waitDispatch(...)` | `gemm_device.waitDispatch(...)` | 0xF3 | `master_control.sv` FSM |
| `device.waitTile(...)` | `gemm_device.waitTile(...)` | 0xF4 | `master_control.sv` FSM |
| `device.requestOutput(...)` | `requestOutput(...)` | N/A | Circular buffer DMA |
| `device.readPendingOutput()` | `readPendingOutput()` | N/A | Circular buffer DMA |

---

## Key Differences

### test_readback.cpp (Hardware Validation)
- **Purpose**: Validate circular buffer correctness
- **Golden Reference**: Pre-computed hex files
- **Configurations**: 14 hardcoded test cases
- **Stress Testing**: Configurable iterations (`-s` flag)
- **Focus**: Hardware reliability and edge cases

### elastiapi.hpp (Production Runtime)
- **Purpose**: Enable real ML workloads
- **Data Source**: Live model weights/activations
- **Configurations**: Dynamic, generated by scheduler
- **Performance**: Optimized for throughput
- **Focus**: Production deployment

---

## Development Workflow

### Modifying Hardware (RTL)
1. Edit RTL in `/home/workstation/elastix_gemm/gemm/src/rtl/`
2. Build bitstream: `cd gemm && ./build_and_flash.sh`
3. Validate with tests: `cd sw_test && ./test_readback`
4. Update elastiapi.hpp if interface changes

### Modifying Software (Model Converter)
1. Edit Python in `/home/workstation/ElastiCore/projects/model_converter/src/`
2. Rebuild C++ bindings: `python setup.py build_ext --inplace`
3. Run tests: `python -m model_converter.main`
4. Validate against hardware with elastiapi.hpp

### Adding New Operations
1. **Hardware**: Add opcode to `master_control.sv` (0xF5, 0xF6, ...)
2. **Runtime**: Add method to `elastiapi.hpp` (e.g., `uint8_t newOp(...)`)
3. **IR**: Add operation to `model_converter/ops.py`
4. **Scheduler**: Add scheduling rule to `scheduler.py`
5. **Test**: Validate in both `test_*.cpp` and `main.py`

---

## Build System Integration

### Elastix GEMM
```bash
cd /home/workstation/elastix_gemm/gemm
./build_and_flash.sh              # Hardware build + flash
cd sw_test && make test_readback  # Software test build
```

### Model Converter
```bash
cd /home/workstation/ElastiCore/projects/model_converter
source .venv/bin/activate
python -m model_converter.main    # Run compiler/emulator
```

### Achronix Backend (C++ Bindings)
```bash
cd src/model_converter/backends/achronix
python setup.py build_ext --inplace
```

---

## Shared Resources

### Documentation
- **Circular Buffer**: Both projects reference `CIRCULAR_BUFFER_REGISTER_ACCESS.md`
- **Register Map**: Shared understanding of MS2.0 registers (0x28-0x54)
- **Command Interface**: 5-opcode microcode (0xF0-0xF4)

### Hardware Platform
- **Board**: VectorPath 815 (VP815)
- **FPGA**: Achronix AC7t1500 Speedster7t
- **Memory**: 8× GDDR6 channels (16GB), DDR4
- **Interface**: PCIe Gen5 x16

### Test Matrices
- **Safetensors Files**: Linear layer weights in `/home/workstation/ElastiCore/projects/model_converter/`
  - `linear_b1_l1024_i4096_o1024.safetensors` (8.4MB)
  - `linear_b1_l1024_i14336_o4096.safetensors` (117.6MB)
  - etc.

---

## Future Integration Opportunities

1. **Unified Testing**
   - Use model_converter's scheduler output as golden reference for `test_readback.cpp`
   - Validate hardware against emulated IR execution

2. **Performance Benchmarking**
   - Compare `test_readback.cpp` throughput with elastiapi.hpp production runs
   - Identify bottlenecks in scheduler vs hardware

3. **Hardware Profiling**
   - Export timing data from elastiapi.hpp
   - Compare against RTL simulation for validation

4. **Continuous Integration**
   - Automated testing: RTL changes → rebuild → test_readback → model_converter validation
   - Ensure hardware-software compatibility

---

## Contact Points

### Elastix GEMM Project
- **Location**: `/home/workstation/elastix_gemm/gemm/`
- **Documentation**: `CLAUDE.md`, `REFERENCES.md`
- **Tests**: `sw_test/test_readback.cpp`, `test_gemm.cpp`, `test_multi_tile.cpp`

### Model Converter Project
- **Location**: `/home/workstation/ElastiCore/projects/model_converter/`
- **Documentation**: `README.md`, `CIRCULAR_BUFFER_REGISTER_ACCESS.md`
- **Backend**: `src/model_converter/backends/achronix/elastiapi.hpp`

---

## Quick Reference

### Running Model Converter
```bash
cd /home/workstation/ElastiCore/projects/model_converter
./run_main.sh  # or: python -m model_converter.main
```

### Running Hardware Tests
```bash
cd /home/workstation/elastix_gemm/gemm/sw_test
./test_readback        # Default: 1× stress, summary only
./test_readback -v     # Verbose: full execution trace
./test_readback -t     # Timing: performance metrics
./test_readback -s 100 # Stress: 100 iterations
```

### Checking Circular Buffer Status
```cpp
// Both projects use identical code:
uint32_t rd_ptr = mmio_read32(0, 0x230) & 0x1FFF;
uint32_t wr_ptr = mmio_read32(0, 0x234) & 0x1FFF;
uint32_t used = mmio_read32(0, 0x238) & 0x3FFF;
```

---

**Last Updated**: November 2, 2025
**Status**: ✅ Actively integrated, production-ready
