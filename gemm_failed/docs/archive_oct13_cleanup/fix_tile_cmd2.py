#!/usr/bin/env python3
"""Correct TILE command packing for gemm testbench."""

def generate_tile_command(dim_b, dim_c, dim_v, left_addr, right_addr):
    """Generate correctly packed TILE command."""
    # Defaults
    flags = 0  
    vec_len = dim_v
    left_ugd_len = 1
    right_ugd_len = 1
    
    # Build 87-bit structure
    struct = 0
    struct |= (dim_b & 0xFF) << 79
    struct |= (dim_c & 0xFF) << 71
    struct |= (dim_v & 0xFF) << 63
    struct |= (flags & 0x7) << 60
    struct |= (vec_len & 0x7FF) << 49
    struct |= (right_ugd_len & 0x7FF) << 38
    struct |= (left_ugd_len & 0x7FF) << 27
    struct |= (right_addr & 0x7FF) << 16
    struct |= (left_addr & 0x7FF) << 5
    
    # Split into words
    word1 = struct & 0xFFFFFFFF
    word2 = (struct >> 32) & 0xFFFFFFFF
    word3 = (struct >> 64) & 0x7FFFFF
    
    return word1, word2, word3

# Test cases
cases = [
    (1, 1, 1, 0, 528, "B1_C1_V1"),
    (4, 4, 32, 0, 528, "B4_C4_V32"),
]

print("=== TILE Command Generator ===\n")

for b, c, v, left, right, name in cases:
    w1, w2, w3 = generate_tile_command(b, c, v, left, right)
    
    # Decode to verify
    dec_left = (w1 >> 5) & 0x7FF
    dec_right = (w1 >> 16) & 0x7FF
    dec_left_ugd_lo = (w1 >> 27) & 0x1F
    dec_left_ugd_hi = w2 & 0x3F
    dec_left_ugd = dec_left_ugd_lo | (dec_left_ugd_hi << 5)
    dec_right_ugd = (w2 >> 6) & 0x7FF
    dec_vec = (w2 >> 17) & 0x7FF
    dec_flags = (w2 >> 28) & 0x7
    dec_v_lo = (w2 >> 28) & 0xF
    dec_v_hi = w3 & 0x7F
    dec_v = dec_v_lo | (dec_v_hi << 4)
    dec_c = (w3 >> 7) & 0xFF
    dec_b = (w3 >> 15) & 0xFF
    
    print(f"{name}: B={b}, C={c}, V={v}, L={left}, R={right}")
    print(f"  cmd[1] = 0x{w1:08x}")
    print(f"  cmd[2] = 0x{w2:08x}")  
    print(f"  cmd[3] = 0x{w3:08x}")
    print(f"  Verify: B={dec_b} C={dec_c} V={dec_v} L={dec_left} R={dec_right}")
    
    if dec_b == b and dec_c == c and dec_v == v and dec_left == left and dec_right == right:
        print(f"  ✓ PASS\n")
    else:
        print(f"  ✗ FAIL\n")
