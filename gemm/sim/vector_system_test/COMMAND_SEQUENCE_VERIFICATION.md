# Command Sequence Verification: Simulation vs Software

**Date**: 2025-11-15
**Purpose**: Verify command sequences match exactly between RTL simulation and software test

## Summary

✅ **VERIFIED**: Command sequences are **EXACTLY THE SAME** between simulation and software
⚠️ **CRITICAL FINDING**: Simulation PASSES but hardware FAILS with identical commands

## Command Comparison by Test

### Test 1: B1_C1_V1
**Software** (test_gemm_full.cpp lines 854-886):
```cpp
dispatch(1*1=1, ugd_vec_size=1, broadcast=1)  // LEFT
dispatch(1*1=1, ugd_vec_size=1, broadcast=0)  // RIGHT
tile(B=1, C=1, V=1, col_en=0x000001)
readout(start_col=0, rd_len=1*1=1)
```

**Simulation** (sim.log lines 5653-5659):
```
DISPATCH LEFT: man_nv_cnt=1 (B×V=1×1), ugd_vec_size=1, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=1 (C×V=1×1), ugd_vec_size=1, broadcast=0, col_en=0x000001
MATMUL: B=1, C_global=1, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=1 (B×C=1×1)
```
✓ **MATCH**

### Test 2: B2_C2_V2
**Software**:
```cpp
dispatch(2*2=4, ugd_vec_size=2, broadcast=1)  // LEFT
dispatch(2*2=4, ugd_vec_size=2, broadcast=0)  // RIGHT
tile(B=2, C=2, V=2, col_en=0x000001)
readout(start_col=0, rd_len=2*2=4)
```

**Simulation** (sim.log lines 5702-5708):
```
DISPATCH LEFT: man_nv_cnt=4 (B×V=2×2), ugd_vec_size=2, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=4 (C×V=2×2), ugd_vec_size=2, broadcast=0, col_en=0x000001
MATMUL: B=2, C_global=2, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=4 (B×C=2×2)
```
✓ **MATCH**

### Test 3: B4_C4_V4
**Software**:
```cpp
dispatch(4*4=16, ugd_vec_size=4, broadcast=1)  // LEFT
dispatch(4*4=16, ugd_vec_size=4, broadcast=0)  // RIGHT
tile(B=4, C=4, V=4, col_en=0x000001)
readout(start_col=0, rd_len=4*4=16)
```

**Simulation** (sim.log lines 5751-5757):
```
DISPATCH LEFT: man_nv_cnt=16 (B×V=4×4), ugd_vec_size=4, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=16 (C×V=4×4), ugd_vec_size=4, broadcast=0, col_en=0x000001
MATMUL: B=4, C_global=4, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=16 (B×C=4×4)
```
✓ **MATCH**

### Test 4: B2_C2_V64
**Software**:
```cpp
dispatch(2*64=128, ugd_vec_size=64, broadcast=1)  // LEFT
dispatch(2*64=128, ugd_vec_size=64, broadcast=0)  // RIGHT
tile(B=2, C=2, V=64, col_en=0x000001)
readout(start_col=0, rd_len=2*2=4)
```

**Simulation** (sim.log lines 5798-5804):
```
DISPATCH LEFT: man_nv_cnt=128 (B×V=2×64), ugd_vec_size=64, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=128 (C×V=2×64), ugd_vec_size=64, broadcast=0, col_en=0x000001
MATMUL: B=2, C_global=2, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=4 (B×C=2×2)
```
✓ **MATCH**

### Test 5: B4_C4_V32
**Software**:
```cpp
dispatch(4*32=128, ugd_vec_size=32, broadcast=1)  // LEFT
dispatch(4*32=128, ugd_vec_size=32, broadcast=0)  // RIGHT
tile(B=4, C=4, V=32, col_en=0x000001)
readout(start_col=0, rd_len=4*4=16)
```

**Simulation** (sim.log lines 5845-5851):
```
DISPATCH LEFT: man_nv_cnt=128 (B×V=4×32), ugd_vec_size=32, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=128 (C×V=4×32), ugd_vec_size=32, broadcast=0, col_en=0x000001
MATMUL: B=4, C_global=4, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=16 (B×C=4×4)
```
✓ **MATCH**

### Test 6: B8_C8_V16
**Software**:
```cpp
dispatch(8*16=128, ugd_vec_size=16, broadcast=1)  // LEFT
dispatch(8*16=128, ugd_vec_size=16, broadcast=0)  // RIGHT
tile(B=8, C=8, V=16, col_en=0x000001)
readout(start_col=0, rd_len=8*8=64)
```

**Simulation** (sim.log lines 5892-5898):
```
DISPATCH LEFT: man_nv_cnt=128 (B×V=8×16), ugd_vec_size=16, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=128 (C×V=8×16), ugd_vec_size=16, broadcast=0, col_en=0x000001
MATMUL: B=8, C_global=8, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=64 (B×C=8×8)
```
✓ **MATCH**

### Test 7: B16_C16_V8
**Software**:
```cpp
dispatch(16*8=128, ugd_vec_size=8, broadcast=1)  // LEFT
dispatch(16*8=128, ugd_vec_size=8, broadcast=0)  // RIGHT
tile(B=16, C=16, V=8, col_en=0x000001)
readout(start_col=0, rd_len=16*16=256)
```

**Simulation** (sim.log lines 5939-5945):
```
DISPATCH LEFT: man_nv_cnt=128 (B×V=16×8), ugd_vec_size=8, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=128 (C×V=16×8), ugd_vec_size=8, broadcast=0, col_en=0x000001
MATMUL: B=16, C_global=16, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=256 (B×C=16×16)
```
✓ **MATCH**

### Test 8: B1_C128_V1
**Software**:
```cpp
dispatch(1*1=1, ugd_vec_size=1, broadcast=1)  // LEFT
dispatch(128*1=128, ugd_vec_size=1, broadcast=0)  // RIGHT
tile(B=1, C=128, V=1, col_en=0x000001)
readout(start_col=0, rd_len=1*128=128)
```

**Simulation** (sim.log lines 5986-5992):
```
DISPATCH LEFT: man_nv_cnt=1 (B×V=1×1), ugd_vec_size=1, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=128 (C×V=128×1), ugd_vec_size=1, broadcast=0, col_en=0x000001
MATMUL: B=1, C_global=128, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=128 (B×C=1×128)
```
✓ **MATCH**

### Test 9: B128_C1_V1
**Software**:
```cpp
dispatch(128*1=128, ugd_vec_size=1, broadcast=1)  // LEFT
dispatch(1*1=1, ugd_vec_size=1, broadcast=0)  // RIGHT
tile(B=128, C=1, V=1, col_en=0x000001)
readout(start_col=0, rd_len=128*1=128)
```

**Simulation** (sim.log lines 6033-6039):
```
DISPATCH LEFT: man_nv_cnt=128 (B×V=128×1), ugd_vec_size=1, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=1 (C×V=1×1), ugd_vec_size=1, broadcast=0, col_en=0x000001
MATMUL: B=128, C_global=1, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=128 (B×C=128×1)
```
✓ **MATCH**

### Test 10: B1_C1_V128
**Software**:
```cpp
dispatch(1*128=128, ugd_vec_size=128, broadcast=1)  // LEFT
dispatch(1*128=128, ugd_vec_size=128, broadcast=0)  // RIGHT
tile(B=1, C=1, V=128, col_en=0x000001)
readout(start_col=0, rd_len=1*1=1)
```

**Simulation** (sim.log lines 6080-6086):
```
DISPATCH LEFT: man_nv_cnt=128 (B×V=1×128), ugd_vec_size=128, broadcast=1, col_en=0x000001
DISPATCH RIGHT: man_nv_cnt=128 (C×V=1×128), ugd_vec_size=128, broadcast=0, col_en=0x000001
MATMUL: B=1, C_global=1, num_tiles=1, col_en=0x000001
READOUT: start_col=0, rd_len=1 (B×C=1×1)
```
✓ **MATCH**

## Conclusion

**All 10 tests have IDENTICAL command sequences between simulation and software.**

## Critical Implication

Since command sequences match exactly but simulation PASSES while hardware FAILS, this confirms:

❌ **NOT an RTL logic bug** - behavioral simulation would show the bug if logic was wrong
✅ **Likely causes**:
- **Synthesis/timing issue**: Race condition in synthesized netlist
- **CDC (Clock Domain Crossing) issue**: Metastability or synchronization failure
- **Reset/initialization difference**: Hardware reset behavior differs from simulation
- **FPGA-specific behavior**: Timing closure violation, glitches, or hardware anomalies

## Next Steps

1. **Timing Analysis**: Check place-and-route timing reports for violations in result_fifo_to_simple_bram.sv or result_arbiter.sv
2. **CDC Review**: Analyze clock domain crossings in result collection path
3. **Hardware Debug**: Use SignalTap/ChipScope to capture waveforms on hardware
4. **Reset Analysis**: Compare reset sequences and initialization between simulation and hardware

## References

- Software test: `/home/dev/Dev/elastix_gemm/gemm/sw_test/test_gemm_full.cpp` lines 764-920
- Simulation log: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/sim.log`
- Testbench: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/tb_engine_top.sv`
