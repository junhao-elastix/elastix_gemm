#!/usr/bin/env python3
"""
Calculate correct TILE command packing according to cmd_tile_s structure.
Structure is 87 bits, packed from MSB to LSB:
  [86:79] dim_b (8 bits)
  [78:71] dim_c (8 bits)
  [70:63] dim_v (8 bits)
  [62:60] flags (3 bits)
  [59:49] vec_len (11 bits)
  [48:38] right_ugd_len (11 bits)
  [37:27] left_ugd_len (11 bits)
  [26:16] right_addr (11 bits)
  [15:5]  left_addr (11 bits)
  [4:0]   padding (5 bits)
"""

def generate_tile_command(dim_b, dim_c, dim_v, left_addr, right_addr):
    """Generate correctly packed TILE command."""
    # Assume simple defaults
    flags = 0  # {main_loop_over_left, right_man_4b, left_man_4b}
    vec_len = dim_v  # For simple case, vec_len = V
    left_ugd_len = 1  # Unified group dot length (typically 1)
    right_ugd_len = 1
    
    # Build 87-bit structure bit by bit
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
    # bits [4:0] are padding (0)
    
    # Split into 3 words: {word3[22:0], word2[31:0], word1[31:0]}
    word1 = struct & 0xFFFFFFFF
    word2 = (struct >> 32) & 0xFFFFFFFF
    word3 = (struct >> 64) & 0x7FFFFF
    
    return word1, word2, word3, struct

# Test cases
test_cases = [
    (1, 1, 1, 0, 528, "B1_C1_V1"),
    (4, 4, 32, 0, 528, "B4_C4_V32"),
]

for b, c, v, left, right, name in test_cases:
    w1, w2, w3, full = generate_tile_command(b, c, v, left, right)
    print(f"=== {name}: B={b}, C={c}, V={v} ===")
    print(f"  87-bit value: 0x{full:022x}")
    print(f"  cmd[1] = 0x{w1:08x}")
    print(f"  cmd[2] = 0x{w2:08x}")
    print(f"  cmd[3] = 0x{w3:08x} (23 bits)")
    
    # Decode and verify
    dec_left = (w1 >> 5) & 0x7FF
    dec_right = (w1 >> 16) & 0x7FF
    dec_left_ugd = ((w1 >> 27) & 0x1F) | ((w2 & 0x3F) << 5)
    dec_right_ugd = (w2 >> 6) & 0x7FF
    dec_vec = (w2 >> 17) & 0x7FF
    dec_v = ((w2 >> 28) & 0xF) | ((w3 & 0xF) << 4)
    dec_c = (w3 >> 7) & 0xFF
    dec_b = (w3 >> 15) & 0xFF
    
    print(f"  Decoded: B={dec_b} C={dec_c} V={dec_v} left={dec_left} right={dec_right}")
    assert dec_b == b, f"B mismatch: {dec_b} != {b}"
    assert dec_c == c, f"C mismatch: {dec_c} != {c}"
    assert dec_v == v, f"V mismatch: {dec_v} != {v}"
    assert dec_left == left, f"left_addr mismatch: {dec_left} != {left}"
    assert dec_right == right, f"right_addr mismatch: {dec_right} != {right}"
    print(f"  ✓ All fields verified!")
    print()
