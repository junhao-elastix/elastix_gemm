"""
Multi-Tile Dispatch Logic Implementation

This module simulates the VECTOR_DISPATCH command behavior described in
MULTI_TILE_DISPATCH_REFERENCE.md. It copies aligned data from dispatcher_bram
(shared L2) to tile_bram (private L1) for each compute tile.
"""

def pop_count(bitmask):
    """Count the number of set bits in a bitmask."""
    return bin(bitmask).count('1')

class BRAMArray:
    """Simple BRAM array simulator for visualization."""
    def __init__(self, size=512, name="BRAM"):
        self.name = name
        self.data = ['_' * 16] * size  # 16 bytes per line
        self.size = size
    
    def write(self, addr, data_16_bytes):
        """Write 16 bytes (4 words) at address."""
        if addr < self.size:
            self.data[addr] = data_16_bytes
        else:
            print(f"WARNING: Address {addr} out of range for {self.name}")
    
    def read(self, addr):
        """Read 16 bytes (4 words) at address."""
        if addr < self.size:
            return self.data[addr]
        else:
            print(f"WARNING: Address {addr} out of range for {self.name}")
            return '_' * 16
    
    def __str__(self):
        return f"{self.name}[{self.size}]"
    
    def display_range(self, start, end):
        """Display a range of addresses."""
        print(f"\n{self.name} contents [{start}:{end-1}]:")
        for i in range(start, min(end, self.size)):
            print(f"  [{i:3d}]: {self.data[i]}")

def dispatch(
    cmd_id,
    tile_addr,
    man_nv_cnt,
    ugd_vec_size,
    disp_right,
    broadcast,
    man_4b,
    col_start,
    col_en,
    verbose=True
):
    """
    Simulate VECTOR_DISPATCH command execution.
    
    Args:
        cmd_id: Command ID for tracking
        tile_addr: Starting address in tile_bram
        man_nv_cnt: Total number of Native Vectors to dispatch
        ugd_vec_size: Number of NVs to dispatch to a tile at a time
        disp_right: 1 = dispatch to right brams, 0 = dispatch to left
        broadcast: 1 = broadcast same data to all tiles, 0 = distribute
        man_4b: Mantissa format (0 = 8-bit, 1 = 4-bit)
        col_start: Starting column tile
        col_en: Bitmask for enabled tiles
        verbose: Print detailed step-by-step execution
    
    Returns:
        Dictionary with execution statistics
    """
    if ugd_vec_size * man_nv_cnt > 128:
        raise ValueError("ugd_vec_size * man_nv_cnt must be less than or equal to 128")

    num_tiles = pop_count(col_en)
    disp_addr_start = 0
    tile_addr_start = 0
    
    # Calculate dimensions
    outer_dim = man_nv_cnt // ugd_vec_size  # UGD
    inner_dim = ugd_vec_size
    
    # Initialize BRAMs
    side = "right" if disp_right else "left"
    disp_bram = BRAMArray(size=512, name=f"dispatcher_bram_{side}")
    tile_brams = [BRAMArray(size=512, name=f"tile_{i}_bram_{side}") 
                  for i in range(num_tiles)]
    
    # Initialize dispatcher_bram with sample data
    total_lines = man_nv_cnt * 4  # Hardware stores as line count
    for addr in range(total_lines):
        disp_bram.write(addr, f"DATA{addr:04d}")
    
    if verbose:
        print()
        print("Here's what actually happens:")
        print()
        print("0. FETCH already puts the data from GDDR6 to dispatcher_bram; dispatcher_bram has data needed for this VECTOR_DISPATCH")
        print(f"1. DC understands there are {num_tiles} tiles, all of which are enabled.")
    
    copy_count = 0
    copy_steps = []
    
    # Main dispatch loop
    if broadcast:
        for ugd_idx in range(outer_dim):
            for t_idx in range(num_tiles):
                for vec_idx in range(inner_dim):
                    # Broadcast: same data from dispatcher_bram to all tiles
                    # Disp_offset doesn't depend on t_idx
                    # vec_idx increments by 1 line (16 bytes) per iteration
                    disp_offset = disp_addr_start + ugd_idx * inner_dim + vec_idx
                    tile_offset = ugd_idx * inner_dim + vec_idx
                    
                    # Store copy information
                    copy_count += 1
                    
                    # Calculate byte addresses (each line is 16 bytes)
                    # disp_offset is in line units (each line is 16 bytes)
                    # For display, show sequential byte ranges: [15:0], [31:16], [47:32], etc.
                    disp_byte_addr = disp_offset * 4
                    tile_byte_addr = (tile_addr + tile_offset) * 4
                    
                    copy_steps.append({
                        'step': copy_count,
                        'tile': t_idx,
                        'disp_byte': disp_byte_addr,
                        'tile_byte': tile_byte_addr
                    })
                    
                    # Read from dispatcher_bram
                    data = disp_bram.read(disp_offset)
                    
                    # Write to tile_bram (respecting tile_addr offset)
                    tile_write_addr = tile_addr + tile_offset
                    tile_brams[t_idx].write(tile_write_addr, data)
    else:
        t_idx = 0
        for ugd_idx in range(outer_dim):
            t_idx = t_idx % num_tiles
            if t_idx == 0 and ugd_idx > 0:
                tile_addr_start += inner_dim
            for vec_idx in range(inner_dim):
                # Distribute: round-robin distribution across tiles
                # Disp_offset depends on t_idx
                disp_offset = disp_addr_start + ugd_idx * inner_dim + vec_idx
                tile_offset = tile_addr_start + vec_idx
            
                # Store copy information
                copy_count += 1
                
                # Calculate byte addresses (each line is 16 bytes)
                # disp_offset is in line units (each line is 16 bytes)
                # For display, show sequential byte ranges: [15:0], [31:16], [47:32], etc.
                disp_byte_addr = disp_offset * 4
                tile_byte_addr = (tile_addr + tile_offset) * 4
                
                copy_steps.append({
                    'step': copy_count,
                    'tile': t_idx,
                    'disp_byte': disp_byte_addr,
                    'tile_byte': tile_byte_addr
                })
                
                # Read from dispatcher_bram
                data = disp_bram.read(disp_offset)
                
                # Write to tile_bram (respecting tile_addr offset)
                tile_write_addr = tile_addr + tile_offset
                tile_brams[t_idx].write(tile_write_addr, data)
            t_idx += 1
    
    # Print output in documentation format
    if verbose:
        side_label = "right" if disp_right else "left"
        broadcast_label = "broadcasts" if broadcast else "distributes"
        print(f"2. DC {broadcast_label} data sequentially from dispatcher_bram_{side_label} to tile_bram_{side_label}, each step below writes 4 lines of data which is 1 Native Vector of 128 GFP8 numbers")
        for step_info in copy_steps:
            # Display as byte ranges [high:low] where each is a 16-byte chunk
            tile_hi = step_info['tile_byte'] + 3
            tile_lo = step_info['tile_byte']
            disp_hi = step_info['disp_byte'] + 3
            disp_lo = step_info['disp_byte']
            
            # Format to match documentation style
            print(f"    {step_info['step']}. tile_{step_info['tile']}_bram [{tile_hi}:{tile_lo}]   <= dispatcher_bram [{disp_hi}:{disp_lo}]")
        print("3. Dispatch done")
    
    if verbose:
        print()
    
    return {
        'cmd_id': cmd_id,
        'copy_count': copy_count,
        'num_tiles': num_tiles,
        'total_lines': total_lines
    }


def example_dispatch_left():
    """Example: DISPATCH LEFT with broadcast."""
    print("\n" + "=" * 80)
    print("EXAMPLE 1: DISPATCH LEFT (BROADCAST MODE)")
    print("=" * 80)
    
    dispatch(
        cmd_id=3,
        tile_addr=0,
        man_nv_cnt=8,      # 8 Native Vectors total (B * V)
        ugd_vec_size=4,    # 4 NVs per UGD
        disp_right=0,      # Dispatch to left
        broadcast=1,       # Broadcast mode
        man_4b=0,
        col_start=0,
        col_en=0x000F      # 4 tiles enabled
    )


def example_dispatch_right():
    """Example: DISPATCH RIGHT with distribute."""
    print("\n" + "=" * 80)
    print("EXAMPLE 2: DISPATCH RIGHT (DISTRIBUTE MODE)")
    print("=" * 80)
    
    dispatch(
        cmd_id=3,
        tile_addr=0,
        man_nv_cnt=32,     # 32 Native Vectors total (C * V)
        ugd_vec_size=4,    # 4 NVs per UGD
        disp_right=1,      # Dispatch to right
        broadcast=0,       # Distribute mode
        man_4b=0,
        col_start=0,
        col_en=0x000F      # 4 tiles enabled
    )


if __name__ == "__main__":
    # Run examples
    example_dispatch_left()
    example_dispatch_right()
    
    print("\n" + "=" * 80)
    print("SUMMARY OF DISPATCH LOGIC:")
    print("=" * 80)
    print("""
The dispatch logic uses nested loops:
  1. Outer loop: ugd_idx (UGD dimension)
  2. Middle loop: t_idx (tile index)
  3. Inner loop: vec_idx (vector index within UGD)

Address calculation:
  - broadcast mode: disp_offset = disp_addr_start + ugd_idx * inner_dim * 4 + vec_idx * 4
                     (same source for all tiles)
  
  - distribute mode: disp_offset = disp_addr_start + (ugd_idx * num_tiles + t_idx) * inner_dim * 4 + vec_idx * 4
                     (different source per tile)
  
  - tile_offset (same for both): ugd_idx * inner_dim * 4 + vec_idx * 4
  
The key difference:
  - Broadcast: All tiles get the same data (for left activations)
  - Distribute: Tiles get different chunks in round-robin fashion (for right weights)
    """)

