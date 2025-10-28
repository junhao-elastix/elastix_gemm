# Portable Compute Engine Test - Quick Start Guide

**Status**: ✅ Files prepared - **Run setup script to complete**
**Location**: `/home/dev/Dev/elastix_gemm/gemm_simple/sim/compute_engine_test/`
**Date**: Fri Oct 24 2025

---

## TL;DR - Quick Setup

```bash
cd /home/dev/Dev/elastix_gemm/gemm_simple/sim/compute_engine_test

# Run automated setup (copies all dependencies locally)
python3 setup_portable.py

# Verify and test
make clean && make run
make summary
```

---

## What Was Done

### ✅ Completed Preparations

1. **Makefile Updated** - Changed paths to local directories (`./rtl`, `./include`, `./hex`)
2. **Testbench Updated** - Changed hex file paths to local (`./hex/*.hex`)
3. **Setup Script Created** - `setup_portable.py` for automated file copying
4. **Documentation Created**:
   - `PORTABLE_README.md` - Comprehensive portable guide (300+ lines)
   - `SETUP_INSTRUCTIONS.md` - Step-by-step manual setup
   - `PORTABLE_STATUS.md` - Detailed status report
   - `README_PORTABLE_SETUP.md` - This quick start guide

### ⚡ Action Required

**Run the setup script** to copy files locally:
```bash
python3 setup_portable.py
```

This will create and populate:
- `rtl/` - 5 RTL modules
- `include/` - 1 package file
- `hex/` - 11 test data files
- `docs/` - Documentation

---

## File Structure

### Before Setup (Current)
```
compute_engine_test/
├── tb_compute_engine_modular.sv        # ✅ UPDATED (local paths)
├── Makefile                            # ✅ UPDATED (local paths)
├── setup_portable.py                   # ✅ CREATED (setup script)
├── PORTABLE_README.md                  # ✅ CREATED (main guide)
├── SETUP_INSTRUCTIONS.md               # ✅ CREATED (instructions)
├── PORTABLE_STATUS.md                  # ✅ CREATED (status report)
└── README_PORTABLE_SETUP.md            # ✅ CREATED (this file)
```

### After Setup (Target)
```
compute_engine_test/
├── rtl/                                # ⏳ TO BE CREATED
│   ├── compute_engine_modular.sv
│   ├── gfp8_bcv_controller.sv
│   ├── gfp8_nv_dot.sv
│   ├── gfp8_group_dot_mlp.sv
│   └── gfp8_to_fp16.sv
├── include/                            # ⏳ TO BE CREATED
│   └── gemm_pkg.sv
├── hex/                                # ⏳ TO BE CREATED
│   ├── left.hex
│   ├── right.hex
│   └── golden_*.hex (9 files)
├── docs/                               # ⏳ TO BE CREATED
│   └── PORTABLE_README.md
└── [other files]
```

---

## Setup Methods

### Method 1: Automated (Recommended)

```bash
python3 setup_portable.py
```

**Advantages**:
- Fast and reliable
- Automatic verification
- Clear output of what was copied

### Method 2: Manual

See `SETUP_INSTRUCTIONS.md` for detailed step-by-step commands.

**Use when**:
- Setup script fails
- Want to understand each step
- Need selective file copying

---

## Verification

After setup, verify everything is ready:

```bash
# Check directories exist
ls -ld rtl/ include/ hex/ docs/

# Check file counts
ls rtl/       # Should show 5 .sv files
ls include/   # Should show 1 .sv file
ls hex/       # Should show 11 .hex files
ls docs/      # Should show 1 .md file

# Test compilation
make clean && make compile

# Test simulation
make run

# View results
make summary
```

---

## What Makes This Portable?

### Local Dependencies
All RTL, includes, and test data copied locally:
- ✅ No paths to `../../src/rtl/`
- ✅ No paths to `/home/dev/Dev/elastix_gemm/hex/`
- ✅ All files in subdirectories

### Can Be Moved
Copy entire directory anywhere:
```bash
# Copy to new location
cp -r compute_engine_test /new/location/

# Still works!
cd /new/location/compute_engine_test
make clean && make run
```

### What's Still External
These must be installed (Achronix licensed IP):
- ACE Tools (`$ACE_INSTALL_DIR`)
- Device models (AC7t1500)
- Component libraries
- ModelSim/QuestaSim

---

## Quick Reference

### Setup
```bash
python3 setup_portable.py              # Run automated setup
```

### Build
```bash
make clean && make run                 # Clean + compile + simulate
make compile                           # Compile only
make debug                             # Run with GUI
```

### Results
```bash
make summary                           # Show test summary
make view-log                          # View full log
grep "PASS\|FAIL" sim.log             # Quick results check
```

### Clean
```bash
make clean                             # Remove generated files
```

---

## Documentation Guide

| File | Purpose | Read When |
|------|---------|-----------|
| **README_PORTABLE_SETUP.md** | Quick start (this file) | First time setup |
| **SETUP_INSTRUCTIONS.md** | Detailed manual setup | If script fails |
| **PORTABLE_README.md** | Complete portable guide | Understanding portability |
| **PORTABLE_STATUS.md** | Current status report | Checking what's done |
| **README.md** | Original simulation guide | Understanding tests |
| **VALIDATION_REPORT.md** | Test results | Understanding validation |

---

## Troubleshooting

### Setup script not found
```bash
# Check you're in the right directory
pwd
# Should show: /home/dev/Dev/elastix_gemm/gemm_simple/sim/compute_engine_test

# Check script exists
ls -l setup_portable.py
```

### Setup script fails
```bash
# Use manual setup instead
# See SETUP_INSTRUCTIONS.md for commands
```

### Compilation fails
```bash
# Check ACE tools
echo $ACE_INSTALL_DIR
# Should show path to ACE installation

# Check files copied
ls rtl/ include/ hex/
# Should show all files
```

### Tests fail
```bash
# View detailed log
make view-log

# Check for errors
grep "ERROR" sim.log
```

---

## Next Steps

1. **✅ Complete**: Review this guide
2. **⏳ Action**: Run `python3 setup_portable.py`
3. **⏳ Verify**: Check all files copied
4. **⏳ Test**: Run `make clean && make run`
5. **⏳ Validate**: Check `make summary` shows PASS

---

## Support

**Questions?** Read the documentation:
1. Start with `PORTABLE_README.md` - Most comprehensive
2. Check `SETUP_INSTRUCTIONS.md` - Step-by-step guide
3. Review `PORTABLE_STATUS.md` - Current status
4. See `README.md` - Original documentation

**Still stuck?** Check main project:
- `../../README.md` - Main project guide
- `../../CLAUDE.md` - Claude Code guidance

---

**Created**: Fri Oct 24 2025
**Status**: Ready for setup
**Action**: Run `python3 setup_portable.py`
