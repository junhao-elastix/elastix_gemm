#!/usr/bin/env python3
"""
Setup script to create portable compute_engine_test directory
Copies all dependencies locally
"""

import shutil
from pathlib import Path

# Base directory
BASE_DIR = Path(__file__).parent
PROJECT_ROOT = BASE_DIR.parent.parent

# Source paths
RTL_SRC = PROJECT_ROOT / "src" / "rtl"
INC_SRC = PROJECT_ROOT / "src" / "include"
HEX_SRC = Path("/home/dev/Dev/elastix_gemm/hex")

# Destination paths
RTL_DST = BASE_DIR / "rtl"
INC_DST = BASE_DIR / "include"
HEX_DST = BASE_DIR / "hex"
DOCS_DST = BASE_DIR / "docs"

# Create directories
for dir_path in [RTL_DST, INC_DST, HEX_DST, DOCS_DST]:
    dir_path.mkdir(exist_ok=True)
    print(f"Created directory: {dir_path}")

# RTL files to copy
RTL_FILES = [
    "compute_engine_modular.sv",
    "gfp8_bcv_controller.sv",
    "gfp8_nv_dot.sv",
    "gfp8_group_dot_mlp.sv",
    "gfp8_to_fp16.sv"
]

# Include files to copy
INC_FILES = [
    "gemm_pkg.sv"
]

# Hex files to copy
HEX_FILES = [
    "left.hex",
    "right.hex",
    "golden_B1_C1_V1.hex",
    "golden_B2_C2_V2.hex",
    "golden_B4_C4_V4.hex",
    "golden_B2_C2_V64.hex",
    "golden_B4_C4_V32.hex",
    "golden_B8_C8_V16.hex",
    "golden_B1_C128_V1.hex",
    "golden_B128_C1_V1.hex",
    "golden_B1_C1_V128.hex"
]

# Copy RTL files
print("\nCopying RTL files...")
for file in RTL_FILES:
    src = RTL_SRC / file
    dst = RTL_DST / file
    if src.exists():
        shutil.copy2(src, dst)
        print(f"  ✓ {file}")
    else:
        print(f"  ✗ {file} (not found)")

# Copy include files
print("\nCopying include files...")
for file in INC_FILES:
    src = INC_SRC / file
    dst = INC_DST / file
    if src.exists():
        shutil.copy2(src, dst)
        print(f"  ✓ {file}")
    else:
        print(f"  ✗ {file} (not found)")

# Copy hex files
print("\nCopying hex files...")
for file in HEX_FILES:
    src = HEX_SRC / file
    dst = HEX_DST / file
    if src.exists():
        shutil.copy2(src, dst)
        print(f"  ✓ {file}")
    else:
        print(f"  ✗ {file} (not found)")

# Move PORTABLE_README.md to docs/
portable_readme = BASE_DIR / "PORTABLE_README.md"
if portable_readme.exists():
    shutil.copy2(portable_readme, DOCS_DST / "PORTABLE_README.md")
    print(f"\n✓ Copied PORTABLE_README.md to docs/")

print("\n" + "="*70)
print("Portable setup complete!")
print("="*70)
print(f"\nDirectory structure:")
print(f"  rtl/     : {len(list(RTL_DST.glob('*.sv')))} files")
print(f"  include/ : {len(list(INC_DST.glob('*.sv')))} files")
print(f"  hex/     : {len(list(HEX_DST.glob('*.hex')))} files")
print(f"  docs/    : {len(list(DOCS_DST.glob('*.md')))} files")

print(f"\nReady to use! Try:")
print(f"  cd {BASE_DIR}")
print(f"  make clean && make run")
