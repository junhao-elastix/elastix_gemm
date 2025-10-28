# Portable Setup Instructions

**Purpose**: Create self-contained portable version of compute_engine_test
**Date**: Fri Oct 24 2025

---

## Automated Setup (Recommended)

Run the provided Python script to automatically copy all dependencies:

```bash
cd /home/dev/Dev/elastix_gemm/gemm_simple/sim/compute_engine_test
python3 setup_portable.py
```

This will:
1. Create subdirectories: rtl/, include/, hex/, docs/
2. Copy all RTL dependencies
3. Copy include files
4. Copy test hex files
5. Organize documentation

---

## Manual Setup (If Script Fails)

### Step 1: Create Directories

```bash
cd /home/dev/Dev/elastix_gemm/gemm_simple/sim/compute_engine_test
mkdir -p rtl include hex docs
```

### Step 2: Copy RTL Files

```bash
# Copy from ../../src/rtl/
cp ../../src/rtl/compute_engine_modular.sv rtl/
cp ../../src/rtl/gfp8_bcv_controller.sv rtl/
cp ../../src/rtl/gfp8_nv_dot.sv rtl/
cp ../../src/rtl/gfp8_group_dot_mlp.sv rtl/
cp ../../src/rtl/gfp8_to_fp16.sv rtl/
```

### Step 3: Copy Include Files

```bash
# Copy from ../../src/include/
cp ../../src/include/gemm_pkg.sv include/
```

### Step 4: Copy Hex Test Files

```bash
# Copy from /home/dev/Dev/elastix_gemm/hex/
cp /home/dev/Dev/elastix_gemm/hex/left.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/right.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/golden_B1_C1_V1.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/golden_B2_C2_V2.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/golden_B4_C4_V4.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/golden_B2_C2_V64.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/golden_B4_C4_V32.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/golden_B8_C8_V16.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/golden_B1_C128_V1.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/golden_B128_C1_V1.hex hex/
cp /home/dev/Dev/elastix_gemm/hex/golden_B1_C1_V128.hex hex/
```

### Step 5: Organize Documentation

```bash
# Move PORTABLE_README.md to docs/
cp PORTABLE_README.md docs/
```

### Step 6: Verify Setup

```bash
# Check RTL files (should show 5 files)
ls -l rtl/

# Check include files (should show 1 file)
ls -l include/

# Check hex files (should show 11 files)
ls -l hex/

# Check docs (should show PORTABLE_README.md)
ls -l docs/
```

---

## Testing the Portable Version

After setup is complete, test that everything works:

```bash
# Clean and run simulation
make clean && make run

# View results
make summary
```

Expected output:
- All files compile successfully
- All tests PASS
- Results logged to sim.log

---

## What Has Been Modified

### 1. Makefile Changes

The Makefile has been updated to use local paths:

**Before**:
```makefile
GEMM_RTL := ../../src/rtl
GEMM_INC := ../../src/include
```

**After**:
```makefile
GEMM_RTL := ./rtl
GEMM_INC := ./include
GEMM_TB := .
```

### 2. Testbench Changes

The testbench (`tb_compute_engine_modular.sv`) has been updated to use local hex paths:

**Before**:
```systemverilog
fd_left = $fopen("/home/dev/Dev/elastix_gemm/hex/left.hex", "r");
load_golden_reference("/home/dev/Dev/elastix_gemm/hex/golden_B1_C1_V1.hex", 1);
```

**After**:
```systemverilog
fd_left = $fopen("./hex/left.hex", "r");
load_golden_reference("./hex/golden_B1_C1_V1.hex", 1);
```

---

## Verification Checklist

After setup, verify:

- [ ] Directory `rtl/` exists with 5 .sv files
- [ ] Directory `include/` exists with gemm_pkg.sv
- [ ] Directory `hex/` exists with 11 .hex files
- [ ] Directory `docs/` exists with PORTABLE_README.md
- [ ] `make clean` runs without errors
- [ ] `make compile` successfully compiles all modules
- [ ] `make run` executes simulation
- [ ] `make summary` shows test results

---

## Troubleshooting

**Issue**: Script fails with "permission denied"
**Solution**: Make script executable:
```bash
chmod +x setup_portable.py
```

**Issue**: Files not copied
**Solution**: Check source paths exist:
```bash
ls -l ../../src/rtl/
ls -l ../../src/include/
ls -l /home/dev/Dev/elastix_gemm/hex/
```

**Issue**: Compilation fails
**Solution**: Verify ACE_INSTALL_DIR is set:
```bash
echo $ACE_INSTALL_DIR
```

---

## Next Steps

Once setup is complete and verified:

1. **Test locally**: `make clean && make run`
2. **Read documentation**: `cat docs/PORTABLE_README.md`
3. **Try portability**: Copy entire directory to new location and test

---

**Setup Status**: Ready for execution
**Last Updated**: Fri Oct 24 2025
