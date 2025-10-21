#!/usr/bin/env python3
"""
Convert golden reference .txt files (float format) to .hex files (FP16 hex format)
for testbench consumption.
"""

import sys
import struct
import numpy as np

def float_to_fp16_hex(value):
    """Convert float to FP16 hex string (4 hex digits)"""
    # Convert to numpy float16, then get hex representation
    fp16 = np.float16(value)
    # Get the raw bytes
    bits = struct.unpack('<H', struct.pack('<e', fp16))[0]
    return f"{bits:04x}"

def convert_golden_txt_to_hex(txt_file, hex_file):
    """Convert a golden .txt file to .hex format"""
    
    with open(txt_file, 'r') as f:
        lines = f.readlines()
    
    # Skip header lines (first 5 lines contain metadata)
    data_lines = lines[5:]
    
    # Parse float values
    values = []
    for line in data_lines:
        line = line.strip()
        if line:
            # Split by whitespace and convert to float
            for val_str in line.split():
                try:
                    val = float(val_str)
                    values.append(val)
                except ValueError:
                    continue
    
    # Convert to FP16 hex and write
    with open(hex_file, 'w') as f:
        for val in values:
            hex_str = float_to_fp16_hex(val)
            f.write(f"{hex_str}\n")
    
    print(f"Converted {len(values)} values: {txt_file} → {hex_file}")

def main():
    import glob
    import os
    
    # Get all golden .txt files
    txt_files = glob.glob("/home/dev/Dev/elastix_gemm/hex/golden_B*.txt")
    
    print(f"Found {len(txt_files)} golden .txt files")
    print()
    
    for txt_file in sorted(txt_files):
        # Generate corresponding .hex filename
        hex_file = txt_file.replace('.txt', '.hex')
        
        # Convert
        convert_golden_txt_to_hex(txt_file, hex_file)
    
    print()
    print("All conversions complete!")

if __name__ == "__main__":
    main()

