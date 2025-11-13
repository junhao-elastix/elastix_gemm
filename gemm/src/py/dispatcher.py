"""
Python Dispatcher Implementation

Implements the dispatcher logic from dispatcher.sv in Python.
Takes 4 input arrays (man_left, man_right, exp_left, exp_right) and
distributes them to NUM_TILES tiles, each with 4 arrays.

Based on:
- dispatcher.sv (RTL implementation)
- MULTI_TILE_DISPATCH_REFERENCE.md
- SINGLE_ROW_REFERENCE.md

Usage:
    from dispather import dispatcher
    
    # Initialize input arrays (512 lines each)
    man_left = np.zeros((512, 32), dtype=np.uint8)  # 512 lines x 32 bytes
    man_right = np.zeros((512, 32), dtype=np.uint8)
    exp_left = np.zeros(512, dtype=np.uint8)        # 512 bytes
    exp_right = np.zeros(512, dtype=np.uint8)
    
    # Dispatch parameters
    num_tiles = 8
    tile_addr = 0
    man_nv_cnt = 128
    ugd_vec_size = 16
    disp_right = False  # 0=left, 1=right
    broadcast = True    # 0=distribute, 1=broadcast
    col_en = 0xFF       # Enable 8 tiles
    col_start = 0
    
    # Output arrays: [num_tiles][4 arrays]
    tile_man_left, tile_man_right, tile_exp_left, tile_exp_right = dispatcher(
        man_left, man_right, exp_left, exp_right,
        num_tiles, tile_addr, man_nv_cnt, ugd_vec_size,
        disp_right, broadcast, col_en, col_start
    )
"""

import numpy as np
from typing import Tuple, List


# Constants matching RTL dispatcher.sv
MAN_WIDTH = 256        # Mantissa data width (bits) = 32 bytes
EXP_WIDTH = 8          # Exponent data width (bits) = 1 byte
BRAM_DEPTH = 512       # Dispatcher BRAM depth
MAX_NUM_TILES = 24     # Maximum number of tiles (based on col_en width)


def popcount_24bit(bits):
    count = 0
    for i in range(24):
        if bits & (1 << i):
            count += 1
    return count


def dispatcher(
    man_left,
    man_right,
    exp_left,
    exp_right,
    num_tiles = 8,
    tile_addr = 0,
    man_nv_cnt = 128,
    ugd_vec_size = 4,
    disp_right = False,
    broadcast = True,
    col_en = 0xFF,
    col_start = 0
):
    """
    Dispatcher function - distributes data from 4 input arrays to NUM_TILES tiles.
    
    This function emulates the same logic as the RTL dispatcher.sv module.
    It reads from dispatcher_bram (4 input arrays) and writes to tile_bram
    (NUM_TILES x 4 arrays).
    
    Args:
        man_left: Input mantissa left array [BRAM_DEPTH, MAN_WIDTH//8] (512x32 bytes)
        man_right: Input mantissa right array [BRAM_DEPTH, MAN_WIDTH//8] (512x32 bytes)
        exp_left: Input exponent left array [BRAM_DEPTH] (512 bytes)
        exp_right: Input exponent right array [BRAM_DEPTH] (512 bytes)
        num_tiles: Number of tiles to dispatch to (must match enabled tiles in col_en)
        tile_addr: Starting address in tile BRAM
        man_nv_cnt: Total NVs to dispatch
        ugd_vec_size: NVs per UGD vector (batch size)
        disp_right: Dispatch side (False=left, True=right)
        broadcast: Distribution mode (False=distribute, True=broadcast)
        col_en: Column enable mask (24 bits)
        col_start: Distribution start column (for multi-dispatch continuity)
        
    Returns:
        Tuple of 4 lists, each containing num_tiles arrays:
        - tile_man_left: List of [BRAM_DEPTH, MAN_WIDTH//8] arrays
        - tile_man_right: List of [BRAM_DEPTH, MAN_WIDTH//8] arrays
        - tile_exp_left: List of [BRAM_DEPTH] arrays
        - tile_exp_right: List of [BRAM_DEPTH] arrays
    """
    
    # Validate inputs
    assert man_left.shape == (BRAM_DEPTH, MAN_WIDTH // 8), \
        f"man_left shape {man_left.shape} != ({BRAM_DEPTH}, {MAN_WIDTH // 8})"
    assert man_right.shape == (BRAM_DEPTH, MAN_WIDTH // 8), \
        f"man_right shape {man_right.shape} != ({BRAM_DEPTH}, {MAN_WIDTH // 8})"
    assert exp_left.shape == (BRAM_DEPTH,), \
        f"exp_left shape {exp_left.shape} != ({BRAM_DEPTH},)"
    assert exp_right.shape == (BRAM_DEPTH,), \
        f"exp_right shape {exp_right.shape} != ({BRAM_DEPTH},)"
    assert num_tiles <= MAX_NUM_TILES, \
        f"num_tiles {num_tiles} > MAX_NUM_TILES {MAX_NUM_TILES}"
    
    # Initialize output arrays for all tiles
    tile_man_left = [np.zeros((BRAM_DEPTH, MAN_WIDTH // 8), dtype=np.uint8) 
                     for _ in range(num_tiles)]
    tile_man_right = [np.zeros((BRAM_DEPTH, MAN_WIDTH // 8), dtype=np.uint8) 
                      for _ in range(num_tiles)]
    tile_exp_left = [np.zeros(BRAM_DEPTH, dtype=np.uint8) 
                     for _ in range(num_tiles)]
    tile_exp_right = [np.zeros(BRAM_DEPTH, dtype=np.uint8) 
                      for _ in range(num_tiles)]
    
    # Calculate dispatch parameters
    num_enabled_tiles = popcount_24bit(col_en)
    assert num_enabled_tiles == num_tiles, \
        f"num_enabled_tiles {num_enabled_tiles} != num_tiles {num_tiles}"
    
    batch_lines = ugd_vec_size * 4  # ugd_vec_size x 4 lines per batch
    total_batches = man_nv_cnt // ugd_vec_size
    lines_to_copy = man_nv_cnt * 4  # man_nv_cnt x 4 total lines
    
    # Get enabled tile indices from col_en mask
    # Note: RTL assumes enabled tiles are sequential starting from bit 0
    # (e.g., col_en=0xFF means tiles 0-7, not arbitrary tiles)
    enabled_tiles = []
    for i in range(24):
        if col_en & (1 << i):
            enabled_tiles.append(i)
    
    # Verify tiles are sequential starting from 0 (RTL requirement)
    assert enabled_tiles == list(range(num_enabled_tiles)), \
        f"Enabled tiles must be sequential starting from 0, got {enabled_tiles}"
    
    # Current tile index (start from col_start modulo num_enabled_tiles)
    # This is the logical tile index (0 to num_enabled_tiles-1)
    current_tile_idx = col_start % num_enabled_tiles
    
    # Source pointer in dispatcher BRAM
    disp_tile_start = 0
    
    # Destination pointer in tile BRAM
    receive_tile_start = tile_addr
    
    # Select input arrays based on disp_right
    input_man = man_right if disp_right else man_left
    input_exp = exp_right if disp_right else exp_left
    
    # Dispatch loop: process each batch
    for batch_cnt in range(total_batches):
        # Process each line in the current batch
        for within_batch in range(batch_lines):
            # Calculate source address in dispatcher BRAM
            src_addr = disp_tile_start + within_batch
            
            # Calculate destination address in tile BRAM (shared across tiles)
            # Write address = receive_tile_start + write_counter
            dst_addr = receive_tile_start + within_batch
            
            if broadcast:
                # BROADCAST MODE: Write same data to all enabled tiles simultaneously
                # RTL uses: tile_wr_en = col_en (all enabled tiles at once)
                for tile_idx in range(num_enabled_tiles):
                    if tile_idx < num_tiles:
                        # Copy mantissa
                        if disp_right:
                            tile_man_right[tile_idx][dst_addr] = input_man[src_addr]
                        else:
                            tile_man_left[tile_idx][dst_addr] = input_man[src_addr]
                        
                        # Copy exponent
                        if disp_right:
                            tile_exp_right[tile_idx][dst_addr] = input_exp[src_addr]
                        else:
                            tile_exp_left[tile_idx][dst_addr] = input_exp[src_addr]
            else:
                # DISTRIBUTE MODE: Write different data to each tile sequentially
                # RTL uses: tile_wr_en = 24'h000001 << current_tile_idx
                # Since enabled tiles are sequential starting from 0,
                # current_tile_idx directly maps to the physical tile index
                target_tile = current_tile_idx
                
                if target_tile < num_tiles:
                    # Copy mantissa to target tile
                    if disp_right:
                        tile_man_right[target_tile][dst_addr] = input_man[src_addr]
                    else:
                        tile_man_left[target_tile][dst_addr] = input_man[src_addr]
                    
                    # Copy exponent to target tile
                    if disp_right:
                        tile_exp_right[target_tile][dst_addr] = input_exp[src_addr]
                    else:
                        tile_exp_left[target_tile][dst_addr] = input_exp[src_addr]
        
        # Update pointers and tile index after batch completion
        if broadcast:
            # BROADCAST: Advance source after all tiles receive same batch
            if current_tile_idx == (num_enabled_tiles - 1):
                # Last tile received this batch, advance to next batch
                disp_tile_start += batch_lines
                receive_tile_start += batch_lines
                current_tile_idx = 0
            else:
                # Move to next tile with SAME data (source pointer unchanged)
                current_tile_idx += 1
        else:
            # DISTRIBUTE: Each tile gets different data, advance source pointer
            disp_tile_start += batch_lines
            
            # Destination address increment logic:
            # - Multi-tile (num_tiles > 1): Only increment when wrapping to tile 0
            # - Single-tile (num_tiles == 1): Always increment
            if num_enabled_tiles == 1:
                receive_tile_start += batch_lines
            elif ((current_tile_idx + 1) % num_enabled_tiles) == 0:
                # Wrapping to tile 0, increment destination address
                receive_tile_start += batch_lines
            
            # Move to next tile (modulo wrap-around)
            current_tile_idx = (current_tile_idx + 1) % num_enabled_tiles
    
    return tile_man_left, tile_man_right, tile_exp_left, tile_exp_right


def dispatcher_simple(
    man_left: np.ndarray,
    man_right: np.ndarray,
    exp_left: np.ndarray,
    exp_right: np.ndarray,
    num_tiles: int,
    tile_addr: int,
    man_nv_cnt: int,
    ugd_vec_size: int,
    disp_right: bool,
    broadcast: bool,
    col_en: int,
    col_start: int = 0
) -> dict:
    """
    Simplified dispatcher that returns a dictionary with tile arrays.
    
    Returns:
        Dictionary with keys:
        - 'tile_man_left': List of arrays
        - 'tile_man_right': List of arrays
        - 'tile_exp_left': List of arrays
        - 'tile_exp_right': List of arrays
    """
    tile_man_left, tile_man_right, tile_exp_left, tile_exp_right = dispatcher(
        man_left, man_right, exp_left, exp_right,
        num_tiles, tile_addr, man_nv_cnt, ugd_vec_size,
        disp_right, broadcast, col_en, col_start
    )
    
    return {
        'tile_man_left': tile_man_left,
        'tile_man_right': tile_man_right,
        'tile_exp_left': tile_exp_left,
        'tile_exp_right': tile_exp_right
    }


if __name__ == "__main__":
    # Example usage
    print("Python Dispatcher Implementation")
    print("=" * 80)
    
    # Create test input arrays
    man_left = np.random.randint(0, 256, (BRAM_DEPTH, MAN_WIDTH // 8), dtype=np.uint8)
    man_right = np.random.randint(0, 256, (BRAM_DEPTH, MAN_WIDTH // 8), dtype=np.uint8)
    exp_left = np.random.randint(0, 256, BRAM_DEPTH, dtype=np.uint8)
    exp_right = np.random.randint(0, 256, BRAM_DEPTH, dtype=np.uint8)
    
    # Test parameters
    num_tiles = 8
    tile_addr = 0
    man_nv_cnt = 128
    ugd_vec_size = 16
    disp_right = False
    broadcast = True
    col_en = 0xFF  # 8 tiles enabled
    col_start = 0
    
    print(f"Input arrays:")
    print(f"  man_left:  {man_left.shape}")
    print(f"  man_right: {man_right.shape}")
    print(f"  exp_left:  {exp_left.shape}")
    print(f"  exp_right: {exp_right.shape}")
    print()
    print(f"Dispatch parameters:")
    print(f"  num_tiles:     {num_tiles}")
    print(f"  tile_addr:     {tile_addr}")
    print(f"  man_nv_cnt:    {man_nv_cnt}")
    print(f"  ugd_vec_size:  {ugd_vec_size}")
    print(f"  disp_right:    {disp_right}")
    print(f"  broadcast:     {broadcast}")
    print(f"  col_en:        0x{col_en:06X}")
    print(f"  col_start:     {col_start}")
    print()
    
    # Run dispatcher
    tile_man_left, tile_man_right, tile_exp_left, tile_exp_right = dispatcher(
        man_left, man_right, exp_left, exp_right,
        num_tiles, tile_addr, man_nv_cnt, ugd_vec_size,
        disp_right, broadcast, col_en, col_start
    )
    
    print(f"Output arrays:")
    print(f"  tile_man_left:  {len(tile_man_left)} tiles, each {tile_man_left[0].shape}")
    print(f"  tile_man_right: {len(tile_man_right)} tiles, each {tile_man_right[0].shape}")
    print(f"  tile_exp_left:  {len(tile_exp_left)} tiles, each {tile_exp_left[0].shape}")
    print(f"  tile_exp_right: {len(tile_exp_right)} tiles, each {tile_exp_right[0].shape}")
    print()
    
    # Verify broadcast mode: all tiles should have same data
    if broadcast and not disp_right:
        print("Verifying broadcast mode (left side):")
        for i in range(1, num_tiles):
            if np.array_equal(tile_man_left[0], tile_man_left[i]):
                print(f"  ✓ Tile {i} matches Tile 0")
            else:
                print(f"  ✗ Tile {i} does NOT match Tile 0")
    
    print("=" * 80)

