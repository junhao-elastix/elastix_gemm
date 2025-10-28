#!/usr/bin/env python3
"""
Generate golden reference outputs for all multi-tile test cases
"""

import numpy as np
import struct
import sys

def gfp8_to_float(mantissa_bytes, exponent):
    """Convert GFP8 group (32 mantissas + 1 exponent) to float32 array
    
    GFP8 format:
    - Exponent: 5-bit signed (-16 to +15)
    - Mantissa: 8-bit signed (-128 to +127)
    """
    # Convert 5-bit exponent to signed (-16 to +15)
    exp_5bit = exponent & 0x1F  # Keep only lower 5 bits
    if exp_5bit >= 16:
        signed_exp = exp_5bit - 32  # Two's complement for 5 bits
    else:
        signed_exp = exp_5bit
    
    results = []
    for m in mantissa_bytes:
        if m == 0:
            results.append(0.0)
        else:
            # Mantissa is 8-bit signed value
            if m > 127:
                signed_mantissa = m - 256  # Two's complement for 8 bits
            else:
                signed_mantissa = m
            
            # Convert to float: mantissa * 2^exponent
            value = float(signed_mantissa) * (2.0 ** signed_exp)
            results.append(value)
    return np.array(results, dtype=np.float32)

def load_gfp8_memory(hex_file):
    """Load GFP8 memory from hex file
    Returns: (exponents, mantissas) where
        exponents[nv_idx] = 8-bit exponent for that NV
        mantissas[nv_idx] = 32-element array of mantissa bytes
    """
    with open(hex_file, 'r') as f:
        lines = [line.strip() for line in f if line.strip() and not line.startswith('#')]
    
    # Memory layout:
    # Lines 0-15: Exponents (32 exponents per line, 8 bits each = 256 bits)
    #             Each line holds exponents for 8 NVs (4 exponents per NV)
    # Lines 16-527: Mantissas (32 mantissas per line, 8 bits each = 256 bits)
    #               1 line per group, 4 groups per NV
    
    exponents = {}  # nv_idx -> list of 4 group exponents
    mantissas = {}  # nv_idx -> list of 4 groups, each 32 mantissas
    
    # Parse exponent lines (0-15)
    for line_idx in range(min(16, len(lines))):
        hex_str = lines[line_idx].replace('_', '')
        # Convert to bytes (256 bits = 32 bytes)
        line_bytes = bytes.fromhex(hex_str)
        
        # Each line has 32 exponents (8 bits each)
        # These correspond to 8 NVs (4 groups per NV)
        for byte_idx in range(32):
            exp_val = line_bytes[byte_idx]
            nv_idx = line_idx * 8 + byte_idx // 4
            group_in_nv = byte_idx % 4
            
            if nv_idx not in exponents:
                exponents[nv_idx] = [0, 0, 0, 0]
            exponents[nv_idx][group_in_nv] = exp_val
    
    # Parse mantissa lines (16-527)
    for line_idx in range(16, min(len(lines), 528)):
        hex_str = lines[line_idx].replace('_', '')
        line_bytes = bytes.fromhex(hex_str)
        
        # Each line is one group (32 mantissas)
        mantissa_line = line_idx - 16  # 0-511
        nv_idx = mantissa_line // 4
        group_in_nv = mantissa_line % 4
        
        if nv_idx not in mantissas:
            mantissas[nv_idx] = [[], [], [], []]
        
        # Store 32 mantissa bytes for this group
        mantissas[nv_idx][group_in_nv] = [line_bytes[i] for i in range(32)]
    
    return exponents, mantissas

def get_nv_data(exponents, mantissas, start_nv, num_nvs):
    """Extract data for a range of NVs and convert to float32"""
    result = []
    for nv_offset in range(num_nvs):
        nv_idx = start_nv + nv_offset
        if nv_idx not in exponents or nv_idx not in mantissas:
            # Return zeros if NV doesn't exist
            result.append(np.zeros(128, dtype=np.float32))
            continue
        
        nv_floats = []
        for group in range(4):
            exp = exponents[nv_idx][group]
            mants = mantissas[nv_idx][group]
            group_floats = gfp8_to_float(mants, exp)
            nv_floats.extend(group_floats)
        
        result.append(np.array(nv_floats, dtype=np.float32))
    
    return result

def compute_tile_golden(left_exp, left_man, right_exp, right_man, 
                        left_addr, right_addr, B, C, V):
    """Compute golden reference for one tile"""
    # Address translation: mantissa line to NV index
    left_start_nv = left_addr // 4
    right_start_nv = right_addr // 4
    
    # Get data for this tile
    left_nvs = get_nv_data(left_exp, left_man, left_start_nv, B * V)
    right_nvs = get_nv_data(right_exp, right_man, right_start_nv, C * V)
    
    # Reshape for matrix multiplication
    # Left: (B*V) NVs -> (B, V*128) matrix
    # Right: (C*V) NVs -> (V*128, C) matrix
    left_matrix = np.zeros((B, V * 128), dtype=np.float32)
    for b in range(B):
        for v in range(V):
            nv_idx = b * V + v
            if nv_idx < len(left_nvs):
                left_matrix[b, v*128:(v+1)*128] = left_nvs[nv_idx]
    
    right_matrix = np.zeros((V * 128, C), dtype=np.float32)
    for c in range(C):
        for v in range(V):
            nv_idx = c * V + v
            if nv_idx < len(right_nvs):
                right_matrix[v*128:(v+1)*128, c] = right_nvs[nv_idx]
    
    # Matrix multiplication: (B, V*128) @ (V*128, C) -> (B, C)
    result = np.matmul(left_matrix, right_matrix)
    
    # Flatten to row-major order
    return result.flatten()

def float32_to_fp16(val):
    """Convert float32 to FP16 (approximation for validation)"""
    # Use numpy's float16 conversion
    return np.float16(val)

def generate_test_golden(test_name, test_config, left_hex, right_hex, output_file):
    """Generate golden reference for one test case"""
    print(f"Generating golden reference for {test_name}...")
    
    # Load memory
    left_exp, left_man = load_gfp8_memory(left_hex)
    right_exp, right_man = load_gfp8_memory(right_hex)
    
    num_tiles = test_config['num_tiles']
    
    with open(output_file, 'w') as f:
        f.write(f"# Golden Reference for {test_name}\n")
        f.write(f"# Total tiles: {num_tiles}\n\n")
        
        total_results = 0
        for tile_idx in range(num_tiles):
            left_addr = test_config['tile_left_addrs'][tile_idx]
            right_addr = test_config['tile_right_addrs'][tile_idx]
            B = test_config['tile_B'][tile_idx]
            C = test_config['tile_C'][tile_idx]
            V = test_config['tile_V'][tile_idx]
            
            f.write(f"--- Tile {tile_idx} ---\n")
            f.write(f"B={B}, C={C}, V={V}, left_addr={left_addr}, right_addr={right_addr}\n")
            f.write(f"Expected results: {B*C}\n\n")
            
            # Compute golden reference
            golden = compute_tile_golden(left_exp, left_man, right_exp, right_man,
                                        left_addr, right_addr, B, C, V)
            
            f.write(f"Results (FP32 golden, FP16 for comparison):\n")
            for idx, val in enumerate(golden):
                fp16_val = float32_to_fp16(val)
                # Write both FP32 and FP16 hex representation
                fp32_hex = struct.unpack('>I', struct.pack('>f', val))[0]
                fp16_hex = struct.unpack('>H', struct.pack('>e', fp16_val))[0]
                f.write(f"{idx:4d}: {val:15.6f} (FP32: 0x{fp32_hex:08x}, FP16: 0x{fp16_hex:04x})\n")
            
            f.write(f"\n")
            total_results += len(golden)
            
            if tile_idx % 16 == 15 or tile_idx == num_tiles - 1:
                print(f"  Processed {tile_idx+1}/{num_tiles} tiles, {total_results} results so far...")
        
        print(f"  Complete: {total_results} total results")

def main():
    left_hex = '/home/dev/Dev/compute_engine_w8a8/hex/left.hex'
    right_hex = '/home/dev/Dev/compute_engine_w8a8/hex/right.hex'
    
    # Define all test cases
    tests = {
        'test1_bcv_2_2_2': {
            'num_tiles': 2,
            'tile_left_addrs': [0, 32],
            'tile_right_addrs': [0, 32],
            'tile_B': [2, 2],
            'tile_C': [2, 2],
            'tile_V': [2, 2],
        },
        'test2_bcv_4_4_1': {
            'num_tiles': 2,
            'tile_left_addrs': [0, 64],
            'tile_right_addrs': [0, 64],
            'tile_B': [4, 4],
            'tile_C': [4, 4],
            'tile_V': [1, 1],
        },
        'test3_bcv_1_8_1': {
            'num_tiles': 2,
            'tile_left_addrs': [0, 32],
            'tile_right_addrs': [0, 32],
            'tile_B': [1, 1],
            'tile_C': [8, 8],
            'tile_V': [1, 1],
        },
        'test4_bcv_8_1_1': {
            'num_tiles': 2,
            'tile_left_addrs': [0, 32],
            'tile_right_addrs': [0, 32],
            'tile_B': [8, 8],
            'tile_C': [1, 1],
            'tile_V': [1, 1],
        },
        'test5_bcv_2_2_4': {
            'num_tiles': 2,
            'tile_left_addrs': [0, 64],
            'tile_right_addrs': [0, 64],
            'tile_B': [2, 2],
            'tile_C': [2, 2],
            'tile_V': [4, 4],
        },
        'test6_bcv_1_128_1_x128': {
            'num_tiles': 128,
            'tile_left_addrs': [t * 4 for t in range(128)],
            'tile_right_addrs': [t * 4 for t in range(128)],
            'tile_B': [1] * 128,
            'tile_C': [128] * 128,
            'tile_V': [1] * 128,
        },
        'test7_bcv_128_1_1_x128': {
            'num_tiles': 128,
            'tile_left_addrs': [t * 4 for t in range(128)],
            'tile_right_addrs': [t * 4 for t in range(128)],
            'tile_B': [128] * 128,
            'tile_C': [1] * 128,
            'tile_V': [1] * 128,
        },
    }
    
    # Generate golden references for all tests
    for test_name, test_config in tests.items():
        output_file = f'/home/dev/Dev/compute_engine_w8a8/hex/golden_{test_name}.txt'
        try:
            generate_test_golden(test_name, test_config, left_hex, right_hex, output_file)
        except Exception as e:
            print(f"ERROR generating {test_name}: {e}")
            import traceback
            traceback.print_exc()
    
    print("\nAll golden references generated!")

if __name__ == '__main__':
    main()

