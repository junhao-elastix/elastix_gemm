#!/usr/bin/env python3
"""
Hardware-Accurate GFP GEMM Reference Model

PURPOSE:
--------
This script generates a golden reference that EXACTLY matches the hardware's
GFP8 group-based computation algorithm for HARDWARE VERIFICATION.

USE THIS SCRIPT WHEN:
- Verifying hardware RTL output (compute_engine.sv)
- Generating golden reference for hardware testbenches
- Debugging hardware computation mismatches

USE mem_layout.py WHEN:
- Understanding GFP memory layout and decoding
- Validating hex file format and matrix dimensions
- Testing with variable B, C, V parameters
- Comparing GFP vs floating-point accuracy

Hardware Algorithm (from compute_engine.sv):
1. For each output element C[i,j]:
   a. Compute 4 group accumulators (integer multiplication and addition)
   b. Scale each group result by 2^(exp_left[g] + exp_right[g] - 2*BIAS)
   c. Sum the 4 scaled group results (floating-point addition)
   d. Convert to FP16 with overflow clamping

KEY DIFFERENCE:
This differs from the Python GFP library (used in mem_layout.py) which uses
dynamic range compression (finding max exponent and aligning mantissas before
accumulation). The hardware uses simpler group-by-group processing.

OUTPUTS:
- out.hex: 16,384 FP16 values (4-digit hex) in tile-major order
- Matches hardware testbench expected output format

Last Updated: Sat Oct 4 06:40:18 PM PDT 2025
"""

import numpy as np
import sys
import struct
import os

# Add hex utilities from local directory
script_dir = os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() else os.getcwd()
sys.path.insert(0, script_dir)
from mem_layout import load_hex_file, decode_exponents, decode_mantissas


class HardwareGFPCompute:
    """
    Hardware-accurate GFP computation matching compute_engine.sv behavior.
    """

    def __init__(self, exp_bits=5, exp_bias=15, group_size=32):
        """
        Initialize hardware GFP parameters.

        Args:
            exp_bits: Number of exponent bits (5 for GFP8)
            exp_bias: Exponent bias (15 for 5-bit exponent)
            group_size: Elements per group (32 for GFP8)
        """
        self.exp_bits = exp_bits
        self.exp_bias = exp_bias
        self.group_size = group_size
        self.num_groups = 4  # For 128-element vectors (128 / 32 = 4)

    def compute_dot_product(self, left_mant, left_exp, right_mant, right_exp):
        """
        Compute dot product of two GFP vectors using hardware algorithm.
        
        CRITICAL: Matches gfp8_nv_dot.sv exponent-aligned integer summation algorithm.

        Args:
            left_mant: [128] array of left mantissas (int8)
            left_exp: [4] array of left exponents (uint5)
            right_mant: [128] array of right mantissas (int8)
            right_exp: [4] array of right exponents (uint5)

        Returns:
            float: Dot product result (before FP16 conversion)
        """
        group_mantissas = []
        group_exponents = []

        # Step 1: Compute each group dot product (matching gfp8_group_dot.sv)
        for g in range(self.num_groups):
            # Integer accumulation within group
            accumulator = 0
            for i in range(self.group_size):
                elem_idx = g * self.group_size + i
                accumulator += int(left_mant[elem_idx]) * int(right_mant[elem_idx])

            # Calculate exponent: exp_result = exp_left + exp_right - 2*bias
            exp_sum = int(left_exp[g]) + int(right_exp[g]) - 2 * self.exp_bias
            
            group_mantissas.append(accumulator)
            group_exponents.append(exp_sum)

        # Step 2: Exponent alignment and integer summation (matching gfp8_nv_dot.sv lines 116-134)
        # Find maximum exponent among all 4 groups
        max_exponent = max(group_exponents)
        
        # Align mantissas by right-shifting to max exponent
        aligned_mantissas = []
        for g in range(self.num_groups):
            exp_diff = max_exponent - group_exponents[g]
            
            # Check for underflow (matching gfp8_nv_dot.sv line 129-131)
            if exp_diff > 31:
                # Underflow - set to zero
                aligned = 0
            else:
                # Python's >> operator performs arithmetic right shift for negative numbers
                # (same behavior as SystemVerilog's >>> operator)
                aligned = group_mantissas[g] >> exp_diff
            aligned_mantissas.append(aligned)
        
        # Sum aligned mantissas as integers
        sum_mantissa = sum(aligned_mantissas)
        
        # Return GFP result (mantissa, exponent) - do NOT convert to float yet!
        # Hardware returns this as GFP, only converts to FP16 after V-loop accumulation
        return (sum_mantissa, max_exponent)

    def gfp_add(self, gfp1, gfp2):
        """
        Add two GFP values using exponent-aligned integer addition.
        
        Matches hardware gfp8_bcv_controller.sv accumulation logic.
        
        Args:
            gfp1: (mantissa1, exponent1) tuple
            gfp2: (mantissa2, exponent2) tuple
        
        Returns:
            (mantissa_sum, exponent_max) tuple
        """
        mant1, exp1 = gfp1
        mant2, exp2 = gfp2
        
        # Find maximum exponent
        max_exp = max(exp1, exp2)
        
        # Align mantissas to max exponent
        exp_diff1 = max_exp - exp1
        exp_diff2 = max_exp - exp2
        
        # Right shift with underflow check
        # Python's >> operator performs arithmetic right shift (same as SystemVerilog >>>)
        if exp_diff1 > 31:
            aligned_mant1 = 0
        else:
            aligned_mant1 = mant1 >> exp_diff1

        if exp_diff2 > 31:
            aligned_mant2 = 0
        else:
            aligned_mant2 = mant2 >> exp_diff2
        
        # Integer addition of aligned mantissas
        sum_mant = aligned_mant1 + aligned_mant2
        
        return (sum_mant, max_exp)

    def gfp_to_float(self, gfp):
        """
        Convert GFP (mantissa, exponent) to floating-point value.
        
        Args:
            gfp: (mantissa, exponent) tuple
        
        Returns:
            float: Real value
        """
        mantissa, exponent = gfp
        scale_factor = 2.0 ** exponent
        return float(mantissa) * scale_factor

    def real_to_fp16(self, val):
        """
        Convert real value to FP16 with hardware-accurate clamping.

        Matches compute_engine.sv:543-603 behavior.

        Args:
            val: Float value to convert

        Returns:
            uint16: FP16 representation
        """
        # Clamp to FP16 range (matching hardware's clamp at line 553-559)
        FP16_MAX = 65504.0
        if val > FP16_MAX:
            clamped_val = FP16_MAX
        elif val < -FP16_MAX:
            clamped_val = -FP16_MAX
        else:
            clamped_val = val

        # Convert to numpy float16, then extract bits
        fp16_val = np.float16(clamped_val)
        fp16_bits = fp16_val.view(np.uint16)

        return fp16_bits

    def compute_gemm(self, left_mant, left_exp, right_mant, right_exp,
                     output_rows=128, output_cols=128):
        """
        Compute full GEMM using hardware algorithm.

        Hardware computes in 4×4 tiles, processing in tile-major order.
        Each tile computes 16 dot products.

        Args:
            left_mant: [128, 128] left mantissa matrix
            left_exp: [128, 4] left exponent matrix
            right_mant: [128, 128] right mantissa matrix (transposed)
            right_exp: [128, 4] right exponent matrix (transposed)
            output_rows: Number of output rows (default 128)
            output_cols: Number of output columns (default 128)

        Returns:
            [16384] array of FP16 results in tile-major order
        """
        results_tile_major = []

        # Process in tile-major order: tile(0,0), tile(0,1), ..., tile(31,31)
        # Addressing matches hardware testbench (tb_ucode_gen.sv):
        # - left_addr = row_block * 16 (base address, hardware adds +16 for mantissas)
        # - right_addr = 528 + col_block * 16 (base address, hardware adds +16 for mantissas)
        # Python directly indexes matrices, so we just use row/col indices

        num_tile_rows = output_rows // 4
        num_tile_cols = output_cols // 4

        for tile_row in range(num_tile_rows):
            for tile_col in range(num_tile_cols):
                # Compute 4×4 tile
                for row_in_tile in range(4):
                    for col_in_tile in range(4):
                        # Output matrix position
                        out_row = tile_row * 4 + row_in_tile
                        out_col = tile_col * 4 + col_in_tile

                        # Extract vectors for this dot product
                        # Left: row from left matrix (A[out_row, :])
                        left_vec_mant = left_mant[out_row, :]
                        left_vec_exp = left_exp[out_row, :]

                        # Right: row from right matrix (B^T[out_col, :] = B[:, out_col])
                        right_vec_mant = right_mant[out_col, :]
                        right_vec_exp = right_exp[out_col, :]

                        # Debug first position
                        if out_row == 0 and out_col == 0:
                            print(f"\n[DEBUG] Position ({out_row},{out_col}):")
                            print(f"  Left mantissas [0:8]: {left_vec_mant[:8]}")
                            print(f"  Right mantissas [0:8]: {right_vec_mant[:8]}")
                            print(f"  Left exponents: {left_vec_exp}")
                            print(f"  Right exponents: {right_vec_exp}")

                        # Compute dot product using hardware algorithm
                        gfp_result = self.compute_dot_product(
                            left_vec_mant, left_vec_exp,
                            right_vec_mant, right_vec_exp
                        )

                        # Convert GFP to float for FP16 conversion
                        dot_result = self.gfp_to_float(gfp_result)

                        # Debug first position result
                        if out_row == 0 and out_col == 0:
                            print(f"  GFP result: mantissa={gfp_result[0]}, exponent={gfp_result[1]}")
                            print(f"  Float value: {dot_result:.6f}")
                            print(f"  FP16 result: 0x{self.real_to_fp16(dot_result):04x}\n")

                        # Convert to FP16
                        fp16_result = self.real_to_fp16(dot_result)
                        results_tile_major.append(fp16_result)

                # Progress indicator
                tile_num = tile_row * num_tile_cols + tile_col
                if (tile_num + 1) % 64 == 0:
                    print(f"Progress: {tile_num + 1}/{num_tile_rows * num_tile_cols} tiles completed")

        return np.array(results_tile_major, dtype=np.uint16)

    def compute_gemm_with_bcv(self, left_mant, left_exp, right_mant, right_exp, B, C, V, left_start_addr=0, right_start_addr=0):
        """
        Compute GEMM with B, C, V parameters and V-loop accumulation.
        
        Matches gfp8_bcv_controller.sv algorithm:
        for b in range(B):
            for c in range(C):
                accumulator = 0
                for v in range(V):
                    left_nv = b * V + v
                    right_nv = c * V + v
                    accumulator += dot_product(NV_left[left_nv], NV_right[right_nv])
                output[b, c] = accumulator

        Args:
            left_mant: [128, 128] left mantissa matrix
            left_exp: [128, 4] left exponent matrix
            right_mant: [128, 128] right mantissa matrix (transposed)
            right_exp: [128, 4] right exponent matrix (transposed)
            B: Output rows (batch size)
            C: Output columns
            V: Inner dimension multiplier (V Native Vectors per output)
            left_start_addr: Starting BRAM address for left matrix (in 4-line units)
            right_start_addr: Starting BRAM address for right matrix (in 4-line units)

        Returns:
            [B*C] array of FP16 results
        """
        results = []
        
        print(f"   Computing with V-loop accumulation:")
        print(f"   - For each of {B}×{C} outputs")
        print(f"   - Accumulate {V} dot products")
        print(f"   - Total: {B*C*V} dot products")

        # Iterate over output positions
        for b in range(B):
            for c in range(C):
                # V-loop accumulation (matching hardware gfp8_bcv_controller.sv)
                # Initialize accumulator as GFP (0, 0) - matching hardware ST_IDLE init
                accumulator_gfp = (0, 0)
                
                for v in range(V):
                    # Calculate Native Vector indices with address offset
                    # Address is in 4-line units, so nv_idx = addr / 4
                    left_nv_idx = (left_start_addr // 4) + b * V + v
                    right_nv_idx = (right_start_addr // 4) + c * V + v
                    
                    # Extract vectors for this dot product
                    left_vec_mant = left_mant[left_nv_idx, :]
                    left_vec_exp = left_exp[left_nv_idx, :]
                    right_vec_mant = right_mant[right_nv_idx, :]
                    right_vec_exp = right_exp[right_nv_idx, :]
                    
                    # Compute single NV dot product (returns GFP)
                    dot_gfp = self.compute_dot_product(
                        left_vec_mant, left_vec_exp,
                        right_vec_mant, right_vec_exp
                    )
                    
                    # GFP accumulation (exponent-aligned integer addition)
                    # This matches hardware gfp8_bcv_controller.sv ST_ACCUM logic
                    if v == 0:
                        # First iteration: initialize accumulator
                        accumulator_gfp = dot_gfp
                    else:
                        # Subsequent iterations: add using GFP addition
                        accumulator_gfp = self.gfp_add(accumulator_gfp, dot_gfp)
                    
                    # Debug first output
                    if b == 0 and c == 0:
                        dot_float = self.gfp_to_float(dot_gfp)
                        acc_float = self.gfp_to_float(accumulator_gfp)
                        print(f"     V-iter {v}: left_nv={left_nv_idx}, right_nv={right_nv_idx}")
                        print(f"       dot_gfp=({dot_gfp[0]}, {dot_gfp[1]}) = {dot_float:.6f}")
                        print(f"       acc_gfp=({accumulator_gfp[0]}, {accumulator_gfp[1]}) = {acc_float:.6f}")
                
                # Convert final GFP accumulator to float, then to FP16
                accumulator_float = self.gfp_to_float(accumulator_gfp)
                fp16_result = self.real_to_fp16(accumulator_float)
                results.append(fp16_result)
                
                # Debug first output
                if b == 0 and c == 0:
                    print(f"   Output[{b},{c}]: acc_gfp=({accumulator_gfp[0]}, {accumulator_gfp[1]})")
                    print(f"                     = {accumulator_float:.6f} -> FP16=0x{fp16_result:04x}")
        
        return np.array(results, dtype=np.uint16)


def generate_multitile_golden_reference(B, C, V, output_prefix="golden"):
    """
    Generate multi-tile golden reference with command sequence.
    
    Args:
        B: Output rows (batch size)
        C: Output columns  
        V: Inner dimension multiplier (V Native Vectors per output)
        output_prefix: Prefix for output files
    
    Returns:
        tuple: (flat_results, command_sequence)
    """
    import os
    
    # Calculate tile dimensions
    num_left_tile = 128 // (B * V)
    num_right_tile = 128 // (C * V)
    total_tiles = num_left_tile * num_right_tile
    total_results = total_tiles * B * C
    
    print(f"Multi-tile configuration:")
    print(f"  B={B}, C={C}, V={V}")
    print(f"  num_left_tile={num_left_tile}, num_right_tile={num_right_tile}")
    print(f"  total_tiles={total_tiles}, total_results={total_results}")
    
    # Load matrices from hex files
    script_dir = os.path.dirname(os.path.abspath(__file__))
    left_hex_path = os.path.join(script_dir, 'left.hex')
    right_hex_path = os.path.join(script_dir, 'right.hex')
    
    exp_left_raw, man_left_raw = load_hex_file(left_hex_path)
    left_exp_torch = decode_exponents(exp_left_raw)
    left_exp = left_exp_torch.numpy()
    left_mant = decode_mantissas(man_left_raw)

    exp_right_raw, man_right_raw = load_hex_file(right_hex_path)
    right_exp_torch = decode_exponents(exp_right_raw)
    right_exp = right_exp_torch.numpy()
    right_mant = decode_mantissas(man_right_raw)
    
    # Initialize hardware-accurate compute engine
    hw_compute = HardwareGFPCompute(exp_bits=5, exp_bias=15, group_size=32)
    
    # Generate results for all tiles
    flat_results = []
    command_sequence = []
    
    print(f"\nGenerating {total_tiles} tiles...")
    
    for left_tile_idx in range(num_left_tile):
        for right_tile_idx in range(num_right_tile):
            tile_num = left_tile_idx * num_right_tile + right_tile_idx
            
            # Calculate BRAM addresses using hardware formula
            # Each Native Vector takes 4 lines, so addr = nv_idx * 4
            left_addr = (left_tile_idx * B * V) * 4
            right_addr = (right_tile_idx * C * V) * 4
            
            # Compute B×C results for this tile
            tile_results = hw_compute.compute_gemm_with_bcv(
                left_mant, left_exp, right_mant, right_exp, 
                B, C, V, left_addr, right_addr
            )
            
            # Append to flat results array
            flat_results.extend(tile_results)
            
            # Add to command sequence
            command_sequence.append({
                'tile_num': tile_num,
                'left_tile_idx': left_tile_idx,
                'right_tile_idx': right_tile_idx,
                'left_addr': left_addr,
                'right_addr': right_addr,
                'results': tile_results.copy()
            })
            
            if (tile_num + 1) % 4 == 0:
                print(f"  Completed {tile_num + 1}/{total_tiles} tiles")
    
    # Write output files
    hex_filename = f"{output_prefix}_B{B}_C{C}_V{V}_multitile.hex"
    cmd_filename = f"{output_prefix}_commands_b{B}_c{C}_v{V}_multitile.txt"
    
    # Write hex file (flat results)
    with open(hex_filename, 'w') as f:
        for val in flat_results:
            f.write(f"{val:04x}\n")
    
    # Write command sequence file
    with open(cmd_filename, 'w') as f:
        f.write(f"# Multi-tile command sequence for B={B}, C={C}, V={V}\n")
        f.write(f"# num_left_tile={num_left_tile}, num_right_tile={num_right_tile}\n")
        f.write(f"# total_tiles={total_tiles}, total_results={total_results}\n\n")
        
        for cmd in command_sequence:
            f.write(f"Tile {cmd['tile_num']} (left_tile={cmd['left_tile_idx']}, right_tile={cmd['right_tile_idx']}):\n")
            f.write(f"  left_addr = ({cmd['left_tile_idx']}*{B}*{V})*4 = {cmd['left_addr']}\n")
            f.write(f"  right_addr = ({cmd['right_tile_idx']}*{C}*{V})*4 = {cmd['right_addr']}\n")
            f.write(f"  Expected: {len(cmd['results'])} results (B*C)\n")
            f.write(f"  Results: {' '.join(f'0x{v:04x}' for v in cmd['results'])}\n\n")
    
    print(f"\nGenerated files:")
    print(f"  {hex_filename}: {len(flat_results)} FP16 results")
    print(f"  {cmd_filename}: Command sequence with addresses")
    
    return flat_results, command_sequence


def main():
    import argparse
    
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Generate hardware-accurate GFP GEMM golden reference')
    parser.add_argument('--B', type=int, default=128, help='Output rows (batch size)')
    parser.add_argument('--C', type=int, default=128, help='Output columns')
    parser.add_argument('--V', type=int, default=1, help='Inner dimension multiplier (V Native Vectors)')
    parser.add_argument('--multitile', action='store_true', help='Generate multi-tile golden reference')
    args = parser.parse_args()
    
    B, C, V = args.B, args.C, args.V
    
    # Validate parameters
    if B * V > 128 or C * V > 128:
        print(f"ERROR: Invalid parameters! B×V={B*V} and C×V={C*V} must both be ≤ 128")
        sys.exit(1)
    
    # Handle multi-tile mode
    if args.multitile:
        print("=" * 80)
        print("Multi-Tile Golden Reference Generation")
        print("=" * 80)
        
        # Generate multi-tile golden reference
        flat_results, command_sequence = generate_multitile_golden_reference(B, C, V)
        
        print("\n" + "=" * 80)
        print("Multi-tile golden reference generation complete!")
        print("Files generated:")
        print(f"  golden_B{B}_C{C}_V{V}_multitile.hex - Flat FP16 results")
        print(f"  golden_commands_b{B}_c{C}_v{V}_multitile.txt - Command sequence")
        print("=" * 80)
        return
    
    # Single-tile mode (original behavior)
    print("=" * 80)
    print("Hardware-Accurate GFP GEMM Reference Generation")
    print("=" * 80)
    print(f"\nConfiguration: B={B}, C={C}, V={V}")
    print(f"  Matrix A: {B} × {128*V} (uses {B*V} Native Vectors)")
    print(f"  Matrix B: {128*V} × {C} (uses {C*V} Native Vectors)")
    print(f"  Output:   {B} × {C} = {B*C} results")

    # Load matrices from hex files
    print("\n1. Loading matrices from hex files...")
    left_hex_path = os.path.join(script_dir, 'left.hex')
    right_hex_path = os.path.join(script_dir, 'right.hex')
    
    exp_left_raw, man_left_raw = load_hex_file(left_hex_path)
    left_exp_torch = decode_exponents(exp_left_raw)      # [128, 4] torch.Tensor
    left_exp = left_exp_torch.numpy()                     # Convert to numpy for processing
    left_mant = decode_mantissas(man_left_raw)           # [128, 128] numpy array

    exp_right_raw, man_right_raw = load_hex_file(right_hex_path)
    right_exp_torch = decode_exponents(exp_right_raw)    # [128, 4] torch.Tensor
    right_exp = right_exp_torch.numpy()                   # Convert to numpy for processing
    right_mant = decode_mantissas(man_right_raw)         # [128, 128] numpy array (already transposed)

    print(f"   Left matrix: {left_mant.shape}, exponents: {left_exp.shape}")
    print(f"   Right matrix: {right_mant.shape}, exponents: {right_exp.shape}")
    print(f"   Mantissa range: [{np.min(left_mant)}, {np.max(left_mant)}]")
    print(f"   Exponent range: [{np.min(left_exp)}, {np.max(left_exp)}]")

    # Initialize hardware-accurate compute engine
    print("\n2. Initializing hardware-accurate GFP compute engine...")
    hw_compute = HardwareGFPCompute(exp_bits=5, exp_bias=15, group_size=32)

    # Compute GEMM with V-loop accumulation
    print(f"\n3. Computing {B}×{C} GEMM with V={V} accumulation...")
    results = hw_compute.compute_gemm_with_bcv(left_mant, left_exp, right_mant, right_exp, B, C, V)

    print(f"\n4. Computation complete!")
    print(f"   Generated {len(results)} FP16 results ({B}×{C})")
    print(f"   First 4 values: {' '.join(f'0x{v:04x}' for v in results[:4])}")

    # Write to output files
    output_path = os.path.join(script_dir, 'out.hex')
    golden_path = os.path.join(script_dir, f'golden_B{B}_C{C}_V{V}.hex')
    
    print(f"\n5. Writing results...")
    print(f"   Writing to {output_path}...")
    with open(output_path, 'w') as f:
        for val in results:
            f.write(f"{val:04x}\n")
    print(f"   ✓ Wrote {len(results)} values")
    
    print(f"   Writing to {golden_path}...")
    with open(golden_path, 'w') as f:
        for val in results:
            f.write(f"{val:04x}\n")
    print(f"   ✓ Wrote {len(results)} values")

    # Verify first results
    print("\n6. Verification:")
    num_to_show = min(16, len(results))
    print(f"   First {num_to_show} results:")
    for i in range(num_to_show):
        row = i // C
        col = i % C
        fp16_bits = results[i]
        fp16_val = np.frombuffer(struct.pack('<H', fp16_bits), dtype=np.float16)[0]
        print(f"     [{i:2d}] output[{row},{col}] = 0x{fp16_bits:04x} ({fp16_val:8.4f})")

    print("\n" + "=" * 80)
    print("Golden reference generation complete!")
    print("Hardware-accurate GFP algorithm used:")
    print("  - Group-by-group integer accumulation")
    print("  - Exponent-aligned integer summation (matches gfp8_nv_dot.sv)")
    print("  - V-loop accumulation (matches gfp8_bcv_controller.sv)")
    print("  - FP16 conversion with overflow clamping")
    print("=" * 80)


if __name__ == '__main__':
    main()
