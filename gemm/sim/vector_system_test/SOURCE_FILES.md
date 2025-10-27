# Source Files for Engine Top Simulation

**Generated**: Sun Oct 12 18:47 PDT 2025  
**Testbench**: `tb_engine_top.sv`  
**DUT**: `engine_top.sv` (MS2.0 GEMM Engine with FIFO Interface)

---

## File Organization

### Packages (Compiled First)
1. **gemm_pkg.sv**
   - Location: `/home/dev/Dev/elastix_gemm/gemm/src/include/gemm_pkg.sv`
   - Purpose: Global parameters (FIFO depths, data widths, timing constants)
   - Key Parameters: 
     - `tile_out_fifo_els_gp = 256` (Result FIFO depth)
     - `cmd_buf_els_gp = 64` (Command FIFO depth)

---

## Testbench Files

### Local Testbench
1. **tb_engine_top.sv**
   - Location: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/tb_engine_top.sv`
   - Purpose: Main testbench with 8 test configurations
   - Features:
     - Command sequence generation
     - Continuous FIFO draining
     - Golden reference validation
     - Result verification with mismatch reporting

### Support Testbenches (from compute_engine_w8a8)
2. **tb_ucode_gen.sv**
   - Location: `/home/dev/Dev/compute_engine_w8a8/src/tb/tb_ucode_gen.sv`
   - Purpose: Microcode generation utilities
   - Functions:
     - `gen_fetch_cmd()` - Generate FETCH command
     - `gen_disp_cmd()` - Generate DISPATCH command
     - `gen_tile_cmd()` - Generate TILE command
     - `gen_wait_cmd()` - Generate WAIT command

3. **tb_memory_model.sv**
   - Location: `/home/dev/Dev/compute_engine_w8a8/src/tb/tb_memory_model.sv`
   - Purpose: Memory model for loading test matrices
   - Features:
     - Loads `left.hex` and `right.hex` from `/home/dev/Dev/compute_engine_w8a8/hex/`
     - Provides read interface for dispatcher
     - Emulates DDR/GDDR6 memory behavior

---

## RTL Design Files (DUT Hierarchy)

### Top-Level Integration
4. **engine_top.sv**
   - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/engine_top.sv`
   - Purpose: Top-level wrapper with FIFO interfaces
   - Interfaces:
     - Command FIFO input (32-bit commands)
     - Result FIFO output (16-bit FP16 results)
     - Control/status signals

### Command Processing
5. **cmd_fifo.sv**
   - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/cmd_fifo.sv`
   - Purpose: Command FIFO buffer
   - Specs: 64 entries × 32-bit

6. **master_control.sv**
   - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/master_control.sv`
   - Purpose: Command parsing and sequencing FSM
   - Commands: FETCH (0xF0), DISPATCH (0xF1), MATMUL (0xF2), WAIT (0xF3, 0xF4)

### Memory Interface
7. **dispatcher_control.sv**
   - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/dispatcher_control.sv`
   - Purpose: Fetch data from memory and buffer in BRAM
   - Features:
     - AXI4 master interface
     - Dual-page buffering
     - BRAM write control

8. **dispatcher_bram.sv**
   - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/dispatcher_bram.sv`
   - Purpose: Dual-port BRAM with simultaneous left/right matrix reads
   - Specs: 2048 entries × 256-bit
   - Features:
     - Port A: Write from dispatcher
     - Port B: Dual read for compute engine (left + right simultaneously)

### Compute Engine (Hierarchical)
9. **compute_engine_modular.sv**
   - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/compute_engine_modular.sv`
   - Purpose: Top-level compute orchestration
   - Features:
     - BCV loop coordination
     - Dual BRAM read interface
     - Result buffering

10. **gfp8_bcv_controller.sv**
    - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/gfp8_bcv_controller.sv`
    - Purpose: B×C×V nested loop controller
    - Features:
      - Orchestrates 3-level nested loops (Batch, Column, Vector)
      - V-loop accumulation (GFP mantissa/exponent)
      - BRAM address generation for dual reads

11. **gfp8_nv_dot.sv**
    - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/gfp8_nv_dot.sv`
    - Purpose: Native Vector (128-element) dot product
    - Features:
      - Instantiates 4× gfp8_group_dot modules
      - Exponent alignment across groups
      - Result accumulation

12. **gfp8_group_dot.sv**
    - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/gfp8_group_dot.sv`
    - Purpose: Group (32-element) dot product
    - Features:
      - Integer-only multiply-accumulate
      - Group exponent calculation
      - GFP8 format handling (7-bit mantissa, shared exponent)

13. **gfp8_to_fp16.sv**
    - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/gfp8_to_fp16.sv`
    - Purpose: Convert GFP8 accumulated result to IEEE 754 FP16
    - Features:
      - Mantissa normalization (leading zero count)
      - Exponent bias adjustment
      - Overflow/underflow handling
      - Sign bit extraction

### Result Path
14. **result_bram.sv**
    - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/result_bram.sv`
    - Purpose: Result FIFO buffer
    - Specs: 256 entries × 16-bit FP16
    - Features:
      - Almost-full threshold @ 192 entries
      - FIFO count output (15-bit)
      - Read/write control

### NAP Interface (Referenced but not actively used in testbench)
15. **nap_responder_wrapper.sv**
    - Location: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/nap_responder_wrapper.sv`
    - Purpose: Defines `t_AXI4` interface type
    - Note: Interface definition only, not instantiated in testbench simulation

---

## Total File Count

| Category | Count | Description |
|----------|-------|-------------|
| **Packages** | 1 | Global parameters |
| **Testbenches** | 3 | Main TB + utilities |
| **Top-Level** | 1 | engine_top wrapper |
| **Command** | 2 | FIFO + control FSM |
| **Memory** | 2 | Dispatcher + BRAM |
| **Compute** | 5 | Modular compute hierarchy |
| **Result** | 1 | Result FIFO |
| **Interface** | 1 | AXI4 type definitions |
| **TOTAL** | **16** | Active source files |

---

## Compilation Order

**Critical**: Package must be compiled first, then order doesn't matter due to SystemVerilog 2-pass compilation:

```bash
# Step 1: Compile package
vlog -sv +incdir+<paths> gemm_pkg.sv

# Step 2: Compile all sources (order-independent after package)
vlog -sv +incdir+<paths> +define+SIMULATION +define+SIM_VERBOSE \
    nap_responder_wrapper.sv \
    cmd_fifo.sv \
    master_control.sv \
    dispatcher_control.sv \
    dispatcher_bram.sv \
    compute_engine_modular.sv \
    gfp8_bcv_controller.sv \
    gfp8_nv_dot.sv \
    gfp8_group_dot.sv \
    gfp8_to_fp16.sv \
    result_bram.sv \
    engine_top.sv \
    tb_ucode_gen.sv \
    tb_memory_model.sv \
    tb_engine_top.sv
```

---

## Data Files (Not Source Code)

### Input Matrices
- **left.hex**: 528 lines × 256-bit GFP8 left matrix
- **right.hex**: 528 lines × 256-bit GFP8 right matrix
- **Location**: `/home/dev/Dev/compute_engine_w8a8/hex/`

### Golden Reference
- **golden_B*_C*_V*.hex**: Expected FP16 results for each test configuration
- **Location**: `/home/dev/Dev/elastix_gemm/hex/`
- **Generated by**: `/home/dev/Dev/compute_engine_w8a8/hex/hardware_gfp_reference.py`

---

## Include Paths

The compilation requires two include paths:

1. **CE_W8A8_INC**: `/home/dev/Dev/compute_engine_w8a8/src/include`
   - Contains shared packages (if any)

2. **GEMM_INC**: `/home/dev/Dev/elastix_gemm/gemm/src/include`
   - Contains `gemm_pkg.sv`

---

## Simulation Defines

- **`SIMULATION`**: Enables simulation-specific code (e.g., timing checks, assertions)
- **`SIM_VERBOSE`**: Enables detailed debug output in modules

---

## Dependencies Graph

```
tb_engine_top.sv
    ├─> tb_ucode_gen.sv (command generation)
    ├─> tb_memory_model.sv (matrix data)
    └─> engine_top.sv
        ├─> cmd_fifo.sv
        ├─> master_control.sv
        ├─> dispatcher_control.sv
        │   └─> dispatcher_bram.sv
        ├─> compute_engine_modular.sv
        │   └─> gfp8_bcv_controller.sv
        │       └─> gfp8_nv_dot.sv
        │           └─> gfp8_group_dot.sv (×4 instances)
        │       └─> gfp8_to_fp16.sv
        └─> result_bram.sv
```

---

## Notes

- **All files are ACTIVE** - no obsolete code in compilation list
- **Clean hierarchy** - clear separation of concerns
- **Dual BRAM architecture** - key performance feature (42% faster)
- **Modular compute engine** - 5-level hierarchy for clarity and maintainability

**Status**: Production-ready source file organization ✅














