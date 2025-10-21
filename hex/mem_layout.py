#!/usr/bin/env python3
"""
Memory Layout Decoder for GFP Data

This module provides functions to decode base memory representations
of Group Floating Point (GFP) tensors stored in external memory format.

Memory Layout Structure (Fixed):
- Total 528 lines per tensor (always fixed)
- Lines 0-15: Exponent data (16 lines x 32 bytes = 512 bytes)
- Lines 16-527: Mantissa data (512 lines x 32 bytes = 16384 bytes)
- Each line represents 256 bits (32 bytes or 32 8-bit numbers)
- Group size: 32 elements per group
- Vector size: 128 elements per vector
- Block size: Always 128 NVs (128×128 elements)

Matrix Dimensions (Configurable):
- Matrix A (left): B × (128 × V) - Activation matrix
- Matrix B (right): (128 × V) × C - Weight matrix (stored transposed)
- Result: B × C - Output matrix
- Default: B=C=1, V=1 → 128×128 matrices
- Constraint: B×V ≤ 128 and C×V ≤ 128

File Format Details:
- Exponent bits: 5-bit, padded to 8-bit
- Mantissa bits: 8-bit
- Each group of 32 elements shares 1 exponent
- Matrix B is stored transposed for efficient multiplication

Adapted from gfp_gen.py and tb_matrix_engine.py reference implementations.
"""

import numpy as np
import torch
import sys
import os

# Add the emulator path to import GFP classes
sys.path.append('/home/dev/Dev/emulator/src/emulator')

from group_floating_point import GFPTensor, GFPDataType, GFPGemm


def parse_hex_line(hex_line: str) -> torch.Tensor:
    """
    Parse a single hex line and convert to tensor of bytes.
    
    Hex file byte ordering: [byte_31] [byte_30] ... [byte_1] [byte_0]
    Display order (L→R): MSB/Left → LSB/Right
    Element order: byte_0 is rightmost, corresponds to element [0]
    
    Args:
        hex_line: String containing space-separated hex bytes (e.g., "0a 0a 09...")
        
    Returns:
        torch.Tensor: Tensor of raw byte values as uint8, reversed to match element order
    """
    hex_line = hex_line.strip()
    if not hex_line:
        return torch.zeros(32, dtype=torch.uint8)

    byte_values = []
    for hex_byte in hex_line.split():
        byte_values.append(int(hex_byte, 16))

    if len(byte_values) < 32:
        byte_values.extend([0] * (32 - len(byte_values)))

    # Hex file already shows bytes in correct order [0→31]
    # No reversal needed - hardware reads bytes in forward order
    byte_values_truncated = byte_values[:32]

    return torch.tensor(byte_values_truncated, dtype=torch.uint8)


def load_hex_file(file_path: str) -> tuple[torch.Tensor, torch.Tensor]:
    """
    Load a complete hex file and separate into exponent and mantissa data.
    
    Args:
        file_path: Path to the hex file
        
    Returns:
        tuple: (exponent_data, mantissa_data) where:
               - exponent_data: [16, 32] uint8 tensor
               - mantissa_data: [512, 32] uint8 tensor
    """
    with open(file_path, 'r') as f:
        lines = f.readlines()
    
    if len(lines) != 528:
        raise ValueError(f"Expected 528 lines, got {len(lines)}")
    
    # Parse all lines to tensors
    parsed_lines = [parse_hex_line(line) for line in lines]
    
    # Separate exponent data (lines 0-15)
    exp_data = torch.stack(parsed_lines[:16])  # [16, 32]
    
    # Separate mantissa data (lines 16-527)
    man_data = torch.stack(parsed_lines[16:528])  # [512, 32]
    
    return exp_data, man_data


def decode_exponents(exponent_data: torch.Tensor) -> torch.Tensor:
    """
    Decode exponent data from memory format into a 128x4 exponent matrix.
    
    The exponent layout is simple: mantissa line N uses exponent index N (1:1 mapping).
    Each mantissa line (group of 32 elements) has one shared exponent.
    - 512 mantissa lines → 512 exponents
    - 512 exponents = 128 NVs × 4 groups per NV
    
    Args:
        exponent_data: [16, 32] tensor of raw exponent bytes (uint8)

    Returns:
        torch.Tensor: [128, 4] tensor of exponents (uint8, one per group per NV)
    """
    # Flatten and ensure we have the right number of exponents
    flat_exps = exponent_data.reshape(-1)  # Keep as torch tensor, shape [512]
    if flat_exps.shape[0] != 128 * 4:
        raise ValueError(f"Unexpected exponent count: {flat_exps.shape[0]}")

    # Simple 1:1 mapping: reshape flat exponents into [128 NVs, 4 groups per NV]
    # Exponent index i corresponds to mantissa line i
    # Ensure dtype is uint8 (5-bit exponents padded to 8-bit)
    exponents = flat_exps.reshape(128, 4)
    
    # Mask to 5 bits (exponents are only 5-bit, padded to 8-bit)
    exponents = exponents & 0x1F  # Keep only the 5 LSBs
    exponents = exponents.to(torch.uint8)

    return exponents


def decode_mantissas(mantissa_data: torch.Tensor) -> np.ndarray:
    """
    Decode mantissa data from memory format into a 128x128 mantissa matrix.
    
    Mantissa layout: Each row uses 4 lines (one per group of 32 elements).
    Each line contains 32 bytes representing 32 mantissa values.
    Raw bytes are 8-bit two's complement signed integers.
    
    Args:
        mantissa_data: [512, 32] tensor of raw mantissa bytes
        
    Returns:
        np.ndarray: [128, 128] array of signed 8-bit mantissa values in range [-128, 127]
    """
    mantissa_matrix = np.zeros((128, 128), dtype=np.int16)
    
    for row_idx in range(128):
        line_start = row_idx * 4  # Each row uses 4 lines
        
        for group_idx in range(4):
            line_idx = line_start + group_idx
            line = mantissa_data[line_idx].numpy()
            
            # Convert each byte from 8-bit two's complement to signed int
            signed = np.array(line, dtype=np.int16)
            signed[signed >= 128] -= 256  # Convert to signed range [-128, 127]
            
            # Use full 8-bit mantissa (no shifting needed)
            mantissas = signed
            
            # Store in correct column range
            col_start = group_idx * 32
            col_end = col_start + 32
            mantissa_matrix[row_idx, col_start:col_end] = mantissas

    return mantissa_matrix


def convert_to_float_matrix(mantissa_data: np.ndarray, exp_data: np.ndarray) -> np.ndarray:
    """
    Convert GFP matrix (mantissas + exponents) to floating point matrix.
    
    This follows the same logic as tb_matrix_engine.py's _convert_to_float() method.
    Each element is converted using: value = mantissa * 2^(exponent - bias)
    
    Args:
        mantissa_data: [128, 128] array of signed mantissa values (8-bit)
        exp_data: [128, 4] array of exponents (5-bit, one per group per row)
        
    Returns:
        np.ndarray: [128, 128] float matrix
    """
    float_matrix = np.zeros((128, 128), dtype=np.float64)
    
    # GFP parameters (8-bit mantissa, 5-bit exponent)
    exp_bits = 5
    bias = (1 << (exp_bits - 1)) - 1  # 15 for 5-bit exponent
    group_size = 32
    
    for r in range(128):
        for c in range(128):
            mantissa_val = int(mantissa_data[r, c])  # Ensure it's a Python int
            
            # Get exponent for this element's group
            group_idx = c // group_size  # Column-wise grouping (row_blocks=1)
            exp_val = int(exp_data[r, group_idx])  # Ensure it's a Python int
            
            # Convert to float using GFP formula
            if exp_val == 0:
                float_matrix[r, c] = 0.0
            else:
                # Use int() to avoid numpy overflow warnings
                exponent = exp_val - bias  # This will be negative for small exponents
                scale_factor = 2.0 ** exponent
                float_matrix[r, c] = mantissa_val * scale_factor
    
    return float_matrix


class GFPMatrix:
    """
    GFP Matrix class adapted from tb_matrix_engine.py.
    
    Stores a 128x128 GFP matrix decoded from hex file format with:
    - Mantissa data: 128x128 signed integers
    - Exponent data: 128x4 exponents (one per group of 32 elements)
    - Float matrix: Dequantized floating point representation
    
    Supports configurable matrix dimensions via B, C, V parameters:
    - Matrix A (left): B × (128 × V) - Activation matrix
    - Matrix B (right): (128 × V) × C - Weight matrix (stored transposed)
    - Constraint: B×V ≤ 128 and C×V ≤ 128
    """
    
    def __init__(self, filename: str, is_left: bool = True, B: int = 1, C: int = 1, V: int = 1):
        self.filename = filename
        self.is_left = is_left  # True for Matrix A, False for Matrix B
        self.B = B
        self.C = C
        self.V = V
        
        # Validate parameters
        if self.is_left and self.B * self.V > 128:
            raise ValueError(f"Matrix A constraint violated: B×V = {self.B}×{self.V} = {self.B*self.V} > 128")
        if not self.is_left and self.C * self.V > 128:
            raise ValueError(f"Matrix B constraint violated: C×V = {self.C}×{self.V} = {self.C*self.V} > 128")
        
        # Always load full 128x128 from hex file
        self.rows = 128
        self.cols = 128
        self.block_size = 32  # Group size
        self.int_size = 8     # Mantissa bits (8-bit mantissa)
        self.fp_exp_size = 5  # Exponent bits (5-bit exponent)
        self.mantissa_data = None
        self.exp_data = None
        self.float_matrix = None
        
        # Effective dimensions for computation
        if self.is_left:
            # Matrix A: B × (128 × V)
            self.effective_rows = self.B
            self.effective_cols = 128 * self.V
        else:
            # Matrix B: (128 × V) × C (stored transposed)
            self.effective_rows = 128 * self.V
            self.effective_cols = self.C
        
        self._load_and_decode()
    
    def _load_and_decode(self):
        """Load hex file and decode into mantissa/exponent/float representations."""
        print(f"Reading GFP matrix from: {self.filename}")
        
        # Load raw hex data
        exp_raw, man_raw = load_hex_file(self.filename)
        
        # Decode exponents and mantissas
        self.exp_data_torch = decode_exponents(exp_raw)  # Keep as torch tensor for GFPTensor
        self.exp_data = self.exp_data_torch.numpy()      # numpy version for float conversion
        self.mantissa_data = decode_mantissas(man_raw)
        
        # Convert to float matrix
        self.float_matrix = convert_to_float_matrix(self.mantissa_data, self.exp_data)
        
        print(f"  Full matrix dimensions: {self.rows}x{self.cols}")
        print(f"  Effective dimensions: {self.effective_rows}x{self.effective_cols}")
        print(f"  Matrix type: {'A (left)' if self.is_left else 'B (right)'}")
        print(f"  Parameters: B={self.B}, C={self.C}, V={self.V}")
        print(f"  Mantissa range: [{np.min(self.mantissa_data)}, {np.max(self.mantissa_data)}]")
        print(f"  Exponent range: [{np.min(self.exp_data)}, {np.max(self.exp_data)}]")
        print(f"  Float range: [{np.min(self.float_matrix):.6e}, {np.max(self.float_matrix):.6e}]")
    
    def get_float_matrix(self):
        """Return the floating point matrix."""
        return self.float_matrix.copy()
    
    def get_effective_gfp_data(self):
        """
        Return mantissa and exponent data in GFP tensor format for the effective matrix.
        
        Returns:
            Tuple of (mantissa_tensor, exponent_tensor):
            - mantissa_tensor: torch.Tensor of shape matching the GFP grouped format
            - exponent_tensor: torch.Tensor of shape matching the GFP grouped format
        """
        # Get effective matrix dimensions
        num_nvs = self.B * self.V if self.is_left else self.C * self.V
        
        # Extract mantissa data for the effective NVs
        # Mantissa data is [128 NVs, 128 elements], reshaped to [128, 4 groups, 32 elements/group]
        mant_reshaped = self.mantissa_data[:, :].reshape(128, 4, 32)
        exp_reshaped = self.exp_data_torch[:, :]  # [128 NVs, 4 groups]
        
        # Extract the effective NVs
        nvs_mant = mant_reshaped[:num_nvs, :, :]  # [B×V or C×V, 4, 32]
        nvs_exp = exp_reshaped[:num_nvs, :]        # [B×V or C×V, 4]
        
        if self.is_left:
            # Matrix A: B rows, each row is V consecutive NVs
            if self.V == 1:
                # [B, 4 groups, 32 elements/group]
                result_mant = nvs_mant[:self.B, :, :]
                result_exp = nvs_exp[:self.B, :].unsqueeze(-1)  # [B, 4, 1]
            else:
                # Reshape to [B, V, 4, 32] then merge V with groups
                reshaped_mant = nvs_mant.reshape(self.B, self.V, 4, 32)
                reshaped_exp = nvs_exp.reshape(self.B, self.V, 4)
                
                # Concatenate V NVs: [B, V×4 groups, 32]
                result_mant = reshaped_mant.reshape(self.B, self.V * 4, 32)
                result_exp = reshaped_exp.reshape(self.B, self.V * 4).unsqueeze(-1)  # [B, V×4, 1]
        else:
            # Matrix B: stored transposed, so C columns become rows after transpose
            if self.V == 1:
                # [C, 4 groups, 32 elements/group] -> transpose to [128, C]
                result_mant = nvs_mant[:self.C, :, :].transpose(0, 1).reshape(4, 32, self.C)
                result_mant = result_mant.transpose(0, 2).reshape(self.C * 128 // 32, 32)
                # This is complex, let me think...
                # Actually for Matrix B with V=1, we have C NVs, each is [4, 32]
                # We need to create [128, C] which gets grouped as [4, 32, C]
                # Wait, I think I'm overcomplicating this
                
                # Matrix B effective is [128×V, C], so with V=1 it's [128, C]
                # Each of the C NVs has [4 groups, 32 elements]
                # After transpose: rows become columns
                # So we need [128, C] with groups along axis 0 (rows)
                
                # Let me reshape: nvs_mant is [C, 4, 32]
                # We want the result to be groupable as [128/32=4, 32, C]
                # Which is [4 groups, 32 elements, C columns]
                result_mant = nvs_mant[:self.C, :, :].permute(1, 2, 0)  # [4, 32, C]
                result_exp = nvs_exp[:self.C, :].unsqueeze(-1)  # [C, 4, 1]
                result_exp = result_exp.permute(1, 0, 2)  # [4, C, 1]
            else:
                # Similar logic but with V > 1
                reshaped_mant = nvs_mant.reshape(self.C, self.V, 4, 32)
                reshaped_exp = nvs_exp.reshape(self.C, self.V, 4)
                
                # [C, V, 4, 32] -> [C, V×4, 32] -> permute for transpose
                merged_mant = reshaped_mant.reshape(self.C, self.V * 4, 32)
                merged_exp = reshaped_exp.reshape(self.C, self.V * 4)
                
                # Transpose: [C, V×4, 32] -> [V×4, 32, C]
                result_mant = merged_mant.permute(1, 2, 0)
                result_exp = merged_exp.permute(1, 0).unsqueeze(-1)  # [V×4, C, 1]
        
        # Convert mantissa to int16 tensor (signed)
        result_mant = torch.from_numpy(result_mant).to(torch.int16)
        
        return result_mant, result_exp
    
    def get_effective_matrix(self):
        """
        Return the effective submatrix for computation based on B, C, V parameters.
        
        The hex file contains 128 Native Vectors (NVs), each with 128 elements.
        Physical storage: 128 rows × 128 columns
        
        Access pattern from memory:
        - Matrix A[n][b][v][i]: file_line = 16 + b×V×4 + v×4 + floor(i/32)
        - Matrix B[n][c][v][i]: file_line = 16 + c×V×4 + v×4 + floor(i/32)
        
        Matrix A (is_left=True):
        - Logical dimensions: B × (128×V)
        - Each row b concatenates V consecutive NVs
        - NVs for row b: indices [b×V, b×V+1, ..., b×V+V-1]
        - Total NVs used: B×V
        
        Matrix B (is_left=False, stored transposed):
        - Logical dimensions: (128×V) × C
        - Physically stored as C×V NVs in hex file (transposed view)
        - Each column c concatenates V consecutive NVs
        - NVs for column c: indices [c×V, c×V+1, ..., c×V+V-1]
        - Total NVs used: C×V
        - Need to transpose from [C, 128×V] to [128×V, C]
        """
        if self.is_left:
            # Matrix A: B × (128×V)
            # Extract first B×V NVs (rows) from the 128×128 matrix
            num_nvs = self.B * self.V
            if num_nvs > 128:
                raise ValueError(f"B×V = {num_nvs} exceeds maximum 128 NVs")
            
            # Take first B×V rows
            nvs = self.float_matrix[:num_nvs, :]  # [B×V, 128]
            
            if self.V == 1:
                # Simple case: B rows × 128 columns
                return nvs[:self.B, :]
            else:
                # Reshape to [B, V, 128] then concatenate V dimension
                nvs_reshaped = nvs.reshape(self.B, self.V, 128)  # [B, V, 128]
                # Concatenate along V dimension to get [B, V×128]
                result = nvs_reshaped.reshape(self.B, self.V * 128)
                return result
        else:
            # Matrix B: (128×V) × C
            # Hex file stores B^T as C×V NVs
            num_nvs = self.C * self.V
            if num_nvs > 128:
                raise ValueError(f"C×V = {num_nvs} exceeds maximum 128 NVs")
            
            # Take first C×V rows (these represent transposed columns)
            nvs = self.float_matrix[:num_nvs, :]  # [C×V, 128]
            
            if self.V == 1:
                # Simple case: [C, 128] stored transposed
                # Transpose to get [128, C]
                return nvs[:self.C, :].T
            else:
                # Reshape to [C, V, 128] then concatenate V dimension
                nvs_reshaped = nvs.reshape(self.C, self.V, 128)  # [C, V, 128]
                # Concatenate along V dimension to get [C, V×128]
                nvs_concat = nvs_reshaped.reshape(self.C, self.V * 128)  # [C, V×128]
                # Transpose to get [V×128, C]
                return nvs_concat.T
    
    def print_matrix(self, name="Matrix", max_rows=4, max_cols=8):
        """Print matrix preview."""
        print(f"\n{name} ({self.rows}x{self.cols}):")
        print("=" * 80)
        print(f"Float data (first {max_rows}x{max_cols}):")
        for r in range(min(max_rows, self.rows)):
            row_str = ""
            for c in range(min(max_cols, self.cols)):
                row_str += f"{self.float_matrix[r, c]:10.6f} "
            print(row_str)


def test_gemm_decoding(B: int = 1, C: int = 1, V: int = 1):
    """
    Test the decoding process and perform GEMM operation with configurable dimensions.
    Adapted from gfp_gen.py's test_generated_matrices() workflow.
    
    Args:
        B: Number of rows in Matrix A (activation matrix)
        C: Number of columns in Matrix B (weight matrix)  
        V: Inner dimension multiplier (128×V)
    
    Matrix dimensions:
        - Matrix A: B × (128 × V)
        - Matrix B: (128 × V) × C (stored transposed)
        - Result: B × C
    """
    left_file = "/home/dev/Dev/elastix_gemm/hex/left.hex"
    right_file = "/home/dev/Dev/elastix_gemm/hex/right.hex"
    
    try:
        print("=" * 80)
        print(f"GFP Matrix Decoding and GEMM Test (B={B}, C={C}, V={V})")
        print("=" * 80)
        
        # Step 1: Load and decode matrices using GFPMatrix class
        print("\n1. Loading and decoding matrices...")
        matrix_a = GFPMatrix(left_file, is_left=True, B=B, C=C, V=V)
        matrix_b = GFPMatrix(right_file, is_left=False, B=B, C=C, V=V)
        
        # Print matrix previews
        matrix_a.print_matrix("Left Matrix (A)", max_rows=4, max_cols=8)
        matrix_b.print_matrix("Right Matrix (B)", max_rows=4, max_cols=8)
        
        # Step 2: Get effective matrices for computation
        print("\n2. Extracting effective matrices for computation...")
        effective_a = matrix_a.get_effective_matrix()
        effective_b = matrix_b.get_effective_matrix()
        
        print(f"   Effective Matrix A shape: {effective_a.shape} (B={B} × 128×V={128*V})")
        print(f"   Effective Matrix B shape: {effective_b.shape} (128×V={128*V} × C={C})")
        
        # Convert to torch tensors
        float_a = torch.from_numpy(effective_a).float()
        float_b = torch.from_numpy(effective_b).float()
        
        print(f"   Torch Tensor A shape: {float_a.shape}")
        print(f"   Torch Tensor B shape: {float_b.shape}")
        
        # Step 2.5: Perform FP Matmul for comparison
        print("\n2.5. Performing FP Matmul for comparison...")
        fp_result = torch.matmul(float_a, float_b).numpy()
        
        print(f"   FP Matmul Result shape: {fp_result.shape}")
        print(f"   FP Matmul Min value: {np.min(fp_result):.6f}")
        print(f"   FP Matmul Max value: {np.max(fp_result):.6f}")
        print(f"   FP Matmul Mean value: {np.mean(fp_result):.6f}")
        print(f"   FP Matmul Non-zero elements: {np.count_nonzero(fp_result)}")
        
        # Preview FP result (first 4x8)
        print(f"\n   FP Matmul Result preview (first 4x8) - Float values:")
        for r in range(min(4, fp_result.shape[0])):
            row_str = "   "
            for c in range(min(8, fp_result.shape[1])):
                row_str += f"{fp_result[r, c]:12.6f} "
            print(row_str)
        
        # Step 3: Create GFP data type (8-bit mantissa, 5-bit exponent)
        print("\n3. Creating GFP tensors...")
        dtype = GFPDataType(
            mantissa_bits=8,  # 8-bit mantissa
            exp_bits=5,       # 5-bit exponent
            exp_bias=15,      # Bias for 5-bit exponent: 2^(5-1) - 1 = 15
            mantissa_signed=True
        )
        
        # Create GFP tensors with proper grouping for GEMM
        # LHS: group_axis=1 (group along columns)
        # RHS: group_axis=0 (group along rows)
        gfp_a = GFPTensor(
            original_shape=torch.Size([effective_a.shape[0], effective_a.shape[1]]),
            group_axis=1,  # Group along columns (LHS requirement)
            group_size=32,
            dtype=dtype,
            original_data=float_a
        )
        
        gfp_b = GFPTensor(
            original_shape=torch.Size([effective_b.shape[0], effective_b.shape[1]]),
            group_axis=0,  # Group along rows (RHS requirement)
            group_size=32,
            dtype=dtype,
            original_data=float_b
        )
        
        print(f"   GFP Tensor A: shape={gfp_a.original_shape}, group_axis={gfp_a.group_axis}")
        print(f"   GFP Tensor B: shape={gfp_b.original_shape}, group_axis={gfp_b.group_axis}")
        
        # Step 4: Define GEMM operation
        print("\n4. Setting up GFP GEMM operation...")
        product_dtype = GFPDataType(
            mantissa_bits=17,  # 17 bits for products of 8-bit mantissas (to avoid overflow)
            exp_bits=5,        # Same as input exponent bits
            mantissa_signed=True
        )
        
        accum_dtype = GFPDataType(
            mantissa_bits=24,  # Wide enough for accumulation (128 products of 17-bit values)
            exp_bits=6,        # Extra exponent bit for larger range
            mantissa_signed=True
        )
        
        gemm = GFPGemm(
            accum_dtype=accum_dtype,
            product_dtype=product_dtype
        )
        
        # Step 5: Perform GEMM
        print("\n5. Performing GFP GEMM...")
        gfp_result = gemm(gfp_a, gfp_b)
        result = gfp_result.dequantize().numpy()
        
        # Step 6: Display results
        print(f"\n6. GEMM Result ({result.shape[0]}x{result.shape[1]}) - Expected: {B}x{C}:")
        print("=" * 80)
        
        # Statistics
        print(f"   Min value: {np.min(result):.6f}")
        print(f"   Max value: {np.max(result):.6f}")
        print(f"   Mean value: {np.mean(result):.6f}")
        print(f"   Non-zero elements: {np.count_nonzero(result)}")
        
        # Preview (first 4x8) - Float values
        print(f"\n   Result preview (first 4x8) - Float values:")
        for r in range(min(4, result.shape[0])):
            row_str = "   "
            for c in range(min(8, result.shape[1])):
                row_str += f"{result[r, c]:12.6f} "
            print(row_str)
        
        # Preview (first 4x8) - Hex values (IEEE 754 half precision - float16)
        print(f"\n   Result preview (first 4x8) - Hex values (IEEE 754 float16):")
        for r in range(min(4, result.shape[0])):
            row_str = "   "
            for c in range(min(8, result.shape[1])):
                # Convert float to 16-bit half precision hex representation
                float16_val = np.float16(result[r, c])
                hex_val = float16_val.view(np.uint16)
                row_str += f"0x{hex_val:04x} "
            print(row_str)
        
        # Step 7: Compare FP Matmul vs GFP GEMM Results
        print(f"\n7. Comparison: FP Matmul vs GFP GEMM Results")
        print("=" * 80)
        
        # Calculate differences
        diff = fp_result - result
        abs_diff = np.abs(diff)
        rel_diff = np.abs(diff / (np.abs(fp_result) + 1e-10))  # Avoid division by zero
        
        print(f"   Result shapes match: {fp_result.shape == result.shape}")
        print(f"   Max absolute difference: {np.max(abs_diff):.6f}")
        print(f"   Mean absolute difference: {np.mean(abs_diff):.6f}")
        print(f"   Max relative difference: {np.max(rel_diff):.6f}")
        print(f"   Mean relative difference: {np.mean(rel_diff):.6f}")
        
        # Show side-by-side comparison for first few elements
        print(f"\n   Side-by-side comparison (first 4x4 elements):")
        print(f"   {'Row':<3} {'Col':<3} {'FP Matmul':<12} {'GFP GEMM':<12} {'Diff':<12} {'Rel Diff':<10}")
        print(f"   {'-'*3} {'-'*3} {'-'*12} {'-'*12} {'-'*12} {'-'*10}")
        
        for r in range(min(4, result.shape[0])):
            for c in range(min(4, result.shape[1])):
                fp_val = fp_result[r, c]
                gfp_val = result[r, c]
                diff_val = fp_val - gfp_val
                rel_diff_val = abs(diff_val / (abs(fp_val) + 1e-10))
                print(f"   {r:<3} {c:<3} {fp_val:<12.6f} {gfp_val:<12.6f} {diff_val:<12.6f} {rel_diff_val:<10.6f}")
        
        # Determine if results are "close enough"
        tolerance = 1e-3  # 0.1% tolerance
        close_enough = np.all(rel_diff < tolerance)
        print(f"\n   Results within {tolerance*100:.1f}% tolerance: {close_enough}")
        
        if not close_enough:
            print(f"   Warning: Significant differences detected between FP and GFP results!")
            print(f"   This may indicate precision loss in GFP quantization or computation differences.")
        else:
            print(f"   Results are consistent between FP Matmul and GFP GEMM.")
        
        # Step 8: Save results to file
        output_path = "/home/dev/Dev/elastix_gemm/hex/decoded_result.txt"
        with open(output_path, 'w') as f:
            f.write("GFP GEMM vs FP Matmul Comparison - Decoded from Hex Files\n")
            f.write("=" * 80 + "\n")
            f.write(f"Parameters: B={B}, C={C}, V={V}\n")
            f.write(f"Matrix A dimensions: {B} × {128*V}\n")
            f.write(f"Matrix B dimensions: {128*V} × {C}\n")
            f.write(f"Result dimensions: {B} × {C}\n")
            f.write(f"Left matrix: {left_file}\n")
            f.write(f"Right matrix: {right_file}\n")
            f.write(f"Result shape: {result.shape}\n")
            f.write(f"GFP GEMM Statistics: Min={np.min(result):.6f}, Max={np.max(result):.6f}, Mean={np.mean(result):.6f}\n")
            f.write(f"FP Matmul Statistics: Min={np.min(fp_result):.6f}, Max={np.max(fp_result):.6f}, Mean={np.mean(fp_result):.6f}\n")
            f.write(f"Max absolute difference: {np.max(abs_diff):.6f}\n")
            f.write(f"Mean absolute difference: {np.mean(abs_diff):.6f}\n")
            f.write(f"Max relative difference: {np.max(rel_diff):.6f}\n")
            f.write(f"Mean relative difference: {np.mean(rel_diff):.6f}\n")
            
            f.write("\n" + "=" * 80 + "\n")
            f.write("GFP GEMM Result Matrix (Float values):\n")
            f.write("=" * 80 + "\n")
            for r in range(result.shape[0]):
                for c in range(result.shape[1]):
                    f.write(f"{result[r, c]:12.6f} ")
                f.write("\n")
            
            f.write("\n" + "=" * 80 + "\n")
            f.write("FP Matmul Result Matrix (Float values):\n")
            f.write("=" * 80 + "\n")
            for r in range(fp_result.shape[0]):
                for c in range(fp_result.shape[1]):
                    f.write(f"{fp_result[r, c]:12.6f} ")
                f.write("\n")
            
            f.write("\n" + "=" * 80 + "\n")
            f.write("Difference Matrix (FP - GFP):\n")
            f.write("=" * 80 + "\n")
            for r in range(diff.shape[0]):
                for c in range(diff.shape[1]):
                    f.write(f"{diff[r, c]:12.6f} ")
                f.write("\n")
            
            f.write("\n" + "=" * 80 + "\n")
            f.write("GFP GEMM Result Matrix (Hex values - IEEE 754 float16):\n")
            f.write("=" * 80 + "\n")
            for r in range(result.shape[0]):
                for c in range(result.shape[1]):
                    float16_val = np.float16(result[r, c])
                    hex_val = float16_val.view(np.uint16)
                    f.write(f"0x{hex_val:04x} ")
                f.write("\n")
        
        print(f"\n8. Results saved to: {output_path}")
        print("\n" + "=" * 80)
        print("GFP GEMM vs FP Matmul Comparison Test Completed Successfully!")
        print("=" * 80)
        
        return matrix_a, matrix_b, result
        
    except Exception as e:
        print(f"\nError during decoding or GEMM: {e}")
        import traceback
        traceback.print_exc()
        return None, None, None


if __name__ == "__main__":
    """
    Main entry point - decode hex files and perform GFP GEMM with configurable dimensions.
    Following the workflow from gfp_gen.py and tb_matrix_engine.py.
    
    Usage:
        python mem_layout.py [--B B] [--C C] [--V V]
    
    Default: B=C=V=1 (128×128 matrices)
    """
    import argparse
    
    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description="GFP Matrix Decoder with configurable dimensions",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python mem_layout.py                    # Default: B=C=V=1 (128×128)
  python mem_layout.py --B 2 --C 4 --V 1  # Matrix A: 2×128, Matrix B: 128×4, Result: 2×4
  python mem_layout.py --B 1 --C 1 --V 2  # Matrix A: 1×256, Matrix B: 256×1, Result: 1×1

Constraints:
  - B×V ≤ 128 (Matrix A constraint)
  - C×V ≤ 128 (Matrix B constraint)
  - Hex files always contain full 128×128 block (528 lines)
        """
    )
    
    parser.add_argument('--B', type=int, default=1, 
                       help='Number of rows in Matrix A (default: 1)')
    parser.add_argument('--C', type=int, default=1, 
                       help='Number of columns in Matrix B (default: 1)')
    parser.add_argument('--V', type=int, default=1, 
                       help='Inner dimension multiplier 128×V (default: 1)')
    
    args = parser.parse_args()
    
    # Validate constraints
    if args.B * args.V > 128:
        print(f"Error: B×V = {args.B}×{args.V} = {args.B*args.V} > 128")
        print("Matrix A constraint violated. Please reduce B or V.")
        sys.exit(1)
    
    if args.C * args.V > 128:
        print(f"Error: C×V = {args.C}×{args.V} = {args.C*args.V} > 128")
        print("Matrix B constraint violated. Please reduce C or V.")
        sys.exit(1)
    
    print(f"Running GFP GEMM with parameters: B={args.B}, C={args.C}, V={args.V}")
    print(f"Matrix A: {args.B} × {128*args.V}")
    print(f"Matrix B: {128*args.V} × {args.C}")
    print(f"Result: {args.B} × {args.C}")
    print()
    
    # Run the GEMM decoding test with specified parameters
    matrix_a, matrix_b, result = test_gemm_decoding(B=args.B, C=args.C, V=args.V)
    
    if result is not None:
        print("\n✓ Test completed successfully!")
    else:
        print("\n✗ Test failed - see error messages above")
