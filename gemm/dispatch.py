#!/usr/bin/env python3
"""
Dispatcher Simulator for Multi-Column Architecture

Shows copy steps and final tile BRAM contents for VECTOR_DISPATCH operations.
Based on MULTI_TILE_DISPATCH_REFERENCE.md and SINGLE_ROW_REFERENCE.md.

Usage:
    # As a module
    from dispatch import simulate_dispatch
    simulate_dispatch(tile_addr=16, man_nv_cnt=16, ugd_vec_size=4,
                     broadcast=0, col_start=6, col_en=0xFF)

    # Command line
    python3 dispatch.py <tile_addr> <man_nv_cnt> <ugd_vec_size> <broadcast> <col_start> [col_en]

    # Interactive mode
    python3 dispatch.py
"""

import sys


def simulate_dispatch(tile_addr, man_nv_cnt, ugd_vec_size, broadcast, col_start, col_en=0xFF, show_steps=True):
    """
    Simulate VECTOR_DISPATCH command execution.

    Args:
        tile_addr: Starting address in tile_bram (base for all columns)
        man_nv_cnt: Total number of Native Vectors to dispatch
        ugd_vec_size: Number of NVs to dispatch to a column before switching
        broadcast: 1 = broadcast same data to all columns, 0 = distribute
        col_start: Starting column for round-robin (for multi-dispatch continuity)
        col_en: Bitmask for enabled columns (default 0xFF = 8 columns)
        show_steps: If True, show all copy steps; if False, only show final BRAMs

    Returns:
        Dictionary with last_column and next_col_start for continuity
    """

    # Get enabled columns from bitmask
    enabled_cols = []
    for i in range(24):  # Max 24 columns
        if col_en & (1 << i):
            enabled_cols.append(i)

    if not enabled_cols:
        print("ERROR: No columns enabled!")
        return None

    num_columns = len(enabled_cols)

    print("="*80)
    print("DISPATCHER SIMULATION")
    print("="*80)
    print(f"Parameters:")
    print(f"  tile_addr     = {tile_addr}")
    print(f"  man_nv_cnt    = {man_nv_cnt} NVs")
    print(f"  ugd_vec_size  = {ugd_vec_size} NVs per batch")
    print(f"  broadcast     = {broadcast} {'(BROADCAST)' if broadcast else '(DISTRIBUTE)'}")
    print(f"  col_start     = {col_start}")
    print(f"  col_en        = 0x{col_en:06X} ({num_columns} columns: {enabled_cols})")
    print()

    # Track what goes into each tile BRAM
    tile_brams = {col: {} for col in enabled_cols}

    if show_steps:
        print("COPY STEPS:")
        print("-"*80)

    step_num = 1
    last_col_index = 0

    if broadcast:
        # BROADCAST MODE: All columns get the same data
        if show_steps:
            print("Mode: BROADCAST - all columns receive same data\n")

        for col_idx in enabled_cols:
            for nv_idx in range(man_nv_cnt):
                write_addr = tile_addr + nv_idx * 4

                # Copy 4 lines per NV
                for line in range(4):
                    src = nv_idx * 4 + line
                    dst = write_addr + line
                    data = f"NV{nv_idx:03d}_L{line}"

                    if show_steps:
                        print(f"Step {step_num:4d}: Disp[{src:3d}] -> Column {col_idx:2d}[{dst:3d}] = {data}")

                    tile_brams[col_idx][dst] = f"NV{nv_idx:03d}"
                    step_num += 1

        last_col_index = enabled_cols[-1]  # All columns get data

    else:
        # DISTRIBUTE MODE: Round-robin with batches
        if show_steps:
            print(f"Mode: DISTRIBUTE - round-robin with batch size {ugd_vec_size}\n")

        current_col_idx = col_start % num_columns
        round_num = 0
        nv_dispatched = 0

        while nv_dispatched < man_nv_cnt:
            batch_size = min(ugd_vec_size, man_nv_cnt - nv_dispatched)
            col_physical = enabled_cols[current_col_idx]

            # Calculate base write address for this round
            base_write_addr = tile_addr + round_num * ugd_vec_size * 4

            # Dispatch batch to current column
            for nv_in_batch in range(batch_size):
                nv_idx = nv_dispatched + nv_in_batch
                write_addr = base_write_addr + nv_in_batch * 4

                # Copy 4 lines per NV
                for line in range(4):
                    src = nv_idx * 4 + line
                    dst = write_addr + line
                    data = f"NV{nv_idx:03d}_L{line}"

                    if show_steps:
                        print(f"Step {step_num:4d}: Disp[{src:3d}] -> Column {col_physical:2d}[{dst:3d}] = {data}")

                    tile_brams[col_physical][dst] = f"NV{nv_idx:03d}"
                    step_num += 1

            last_col_index = col_physical
            nv_dispatched += batch_size

            # Move to next column
            prev_col_idx = current_col_idx
            current_col_idx = (current_col_idx + 1) % num_columns

            # Check for wrap-around
            if current_col_idx < prev_col_idx:
                if show_steps:
                    print(f"    >> Wrap-around: column {enabled_cols[prev_col_idx]} -> column {enabled_cols[current_col_idx]}, round {round_num} -> {round_num+1}")
                round_num += 1

    # Show final BRAM contents
    print()
    print("="*80)
    print("TILE BRAM CONTENTS AFTER DISPATCH:")
    print("="*80)

    for col in sorted(tile_brams.keys()):
        if tile_brams[col]:
            print(f"\nColumn {col}:")
            print("-"*40)

            # Group consecutive addresses by NV
            nv_ranges = {}
            for addr, nv in sorted(tile_brams[col].items()):
                if nv not in nv_ranges:
                    nv_ranges[nv] = []
                nv_ranges[nv].append(addr)

            # Print each NV's address range
            for nv in sorted(nv_ranges.keys(), key=lambda x: int(x[2:])):
                addrs = sorted(nv_ranges[nv])
                if addrs:
                    print(f"  [{min(addrs):3d}-{max(addrs):3d}] {nv}")
        else:
            print(f"\nColumn {col}: Empty")

    # Calculate next col_start for multi-dispatch continuity
    if broadcast:
        next_col_start = 0  # Not relevant for broadcast
    else:
        # Find which column index received the last NV
        last_col_idx = enabled_cols.index(last_col_index)
        next_col_start = enabled_cols[(last_col_idx + 1) % num_columns]

    print()
    print("="*80)
    print(f"Last column to receive data: {last_col_index}")
    print(f"Next dispatch should use col_start: {next_col_start}")
    print("="*80)

    return {
        'last_column': last_col_index,
        'next_col_start': next_col_start
    }


def generate_testbench_vectors(tile_addr, man_nv_cnt, ugd_vec_size, broadcast, col_start, col_en,
                              output_format='hex', filename=None):
    """Generate testbench vectors for RTL simulation

    Args:
        output_format: 'hex', 'bin', or 'verilog'
        filename: Output filename (None for stdout)

    Returns:
        Dictionary with test vectors and expected outputs
    """

    # Run simulation to get expected results
    enabled_cols = [i for i in range(24) if col_en & (1 << i)]
    num_columns = len(enabled_cols)

    # Generate test vectors
    vectors = {
        'inputs': {
            'tile_addr': tile_addr,
            'man_nv_cnt': man_nv_cnt,
            'ugd_vec_size': ugd_vec_size,
            'broadcast': broadcast,
            'col_start': col_start,
            'col_en': col_en
        },
        'expected_tiles': {},
        'dispatcher_bram': []
    }

    # Generate dispatcher BRAM contents (source data)
    for i in range(man_nv_cnt * 4):  # 4 lines per NV
        if output_format == 'hex':
            data = f"{i:08x}"  # Simple incrementing pattern
        else:
            data = i
        vectors['dispatcher_bram'].append(data)

    # Calculate expected tile contents using simulation
    if num_columns > 0:
        # Initialize tile BRAMs
        tile_brams = {}
        for col in enabled_cols:
            tile_brams[col] = {}

        # Simulate distribution
        if broadcast:
            # All tiles get same data
            for nv_idx in range(man_nv_cnt):
                write_addr = tile_addr + nv_idx * 4
                for col in enabled_cols:
                    for line in range(4):
                        tile_brams[col][write_addr + line] = f"NV{nv_idx:03d}_L{line}"
        else:
            # Round-robin distribution
            current_col_idx = col_start % num_columns
            round_num = 0
            nv_dispatched = 0

            while nv_dispatched < man_nv_cnt:
                batch_size = min(ugd_vec_size, man_nv_cnt - nv_dispatched)
                col_physical = enabled_cols[current_col_idx]
                base_write_addr = tile_addr + round_num * ugd_vec_size * 4

                for nv_in_batch in range(batch_size):
                    nv_idx = nv_dispatched + nv_in_batch
                    write_addr = base_write_addr + nv_in_batch * 4

                    for line in range(4):
                        dst = write_addr + line
                        tile_brams[col_physical][dst] = f"NV{nv_idx:03d}_L{line}"

                nv_dispatched += batch_size
                prev_col_idx = current_col_idx
                current_col_idx = (current_col_idx + 1) % num_columns

                if current_col_idx < prev_col_idx:
                    round_num += 1

        # Convert to expected format
        for col, contents in tile_brams.items():
            vectors['expected_tiles'][col] = contents

    # Write to file if specified
    if filename:
        with open(filename, 'w') as f:
            if output_format == 'hex':
                f.write("// Testbench vectors in hex format\n")
                f.write(f"// Inputs: tile_addr={tile_addr:03x} man_nv_cnt={man_nv_cnt} ")
                f.write(f"ugd_vec_size={ugd_vec_size} broadcast={broadcast} ")
                f.write(f"col_start={col_start} col_en={col_en:06x}\n")
                f.write("\n// Dispatcher BRAM contents:\n")
                for addr, data in enumerate(vectors['dispatcher_bram']):
                    f.write(f"@{addr:04x} {data}\n")

                f.write("\n// Expected tile contents:\n")
                for tile, contents in vectors['expected_tiles'].items():
                    f.write(f"\n// Tile {tile}:\n")
                    for addr in sorted(contents.keys()):
                        f.write(f"@{addr:04x} {contents[addr]}\n")

            elif output_format == 'verilog':
                f.write("// Verilog testbench initialization\n")
                f.write(f"initial begin\n")
                f.write(f"    // Configure dispatch parameters\n")
                f.write(f"    tile_addr = 11'd{tile_addr};\n")
                f.write(f"    man_nv_cnt = 11'd{man_nv_cnt};\n")
                f.write(f"    ugd_vec_size = 5'd{ugd_vec_size};\n")
                f.write(f"    broadcast = 1'b{1 if broadcast else 0};\n")
                f.write(f"    col_start = 5'd{col_start};\n")
                f.write(f"    col_en = 24'h{col_en:06x};\n")
                f.write(f"    \n")
                f.write(f"    // Initialize dispatcher BRAM\n")
                for addr, data in enumerate(vectors['dispatcher_bram']):
                    f.write(f"    disp_bram[{addr}] = 32'h{data};\n")
                f.write(f"end\n")

        print(f"Generated test vectors saved to {filename}")

    return vectors


def interactive_mode():
    """Interactive dispatcher simulator."""
    print("INTERACTIVE DISPATCHER SIMULATOR")
    print("Assumes 128 NVs available (NV000-NV127)")
    print("Enter 'quit' to exit")
    print()

    while True:
        print("\nEnter dispatch parameters:")

        try:
            cmd = input("tile_addr: ")
            if cmd.lower() == 'quit':
                break
            tile_addr = int(cmd)

            man_nv_cnt = int(input("man_nv_cnt: "))
            ugd_vec_size = int(input("ugd_vec_size: "))
            broadcast = int(input("broadcast (0/1): "))
            col_start = int(input("col_start: "))
            col_en_str = input("col_en (hex, e.g. 0xFF): ")
            col_en = int(col_en_str, 16) if '0x' in col_en_str.lower() else int(col_en_str)

            show_steps_str = input("Show copy steps? (y/n, default=y): ").strip().lower()
            show_steps = show_steps_str != 'n'

            simulate_dispatch(tile_addr, man_nv_cnt, ugd_vec_size,
                            broadcast, col_start, col_en, show_steps)

        except (ValueError, KeyboardInterrupt):
            print("\nInvalid input or interrupted.")
        except EOFError:
            break

    print("\nGoodbye!")


def main():
    """Main entry point for command-line usage."""

    if len(sys.argv) == 1:
        # No arguments - run interactive mode
        interactive_mode()

    elif len(sys.argv) == 2 and sys.argv[1] in ['help', '-h', '--help']:
        print("Usage:")
        print("  python3 dispatch.py                          # Interactive mode")
        print("  python3 dispatch.py <tile_addr> <man_nv_cnt> <ugd_vec_size> <broadcast> <col_start> [col_en]")
        print()
        print("Examples:")
        print("  python3 dispatch.py 0 8 2 0 0 0x0F          # 8 NVs, batch=2, 4 columns")
        print("  python3 dispatch.py 16 16 4 0 6 0xFF        # Wrap-around example")
        print()
        print("Parameters:")
        print("  tile_addr    : Base address in tile BRAM")
        print("  man_nv_cnt   : Number of Native Vectors to dispatch")
        print("  ugd_vec_size : Batch size (NVs per column before switching)")
        print("  broadcast    : 0=distribute (round-robin), 1=broadcast (all columns)")
        print("  col_start    : Starting column for round-robin")
        print("  col_en       : Column enable bitmask (hex, default=0xFF for 8 columns)")

    elif len(sys.argv) >= 6:
        # Command-line arguments provided
        try:
            tile_addr = int(sys.argv[1])
            man_nv_cnt = int(sys.argv[2])
            ugd_vec_size = int(sys.argv[3])
            broadcast = int(sys.argv[4])
            col_start = int(sys.argv[5])
            col_en = int(sys.argv[6], 16) if len(sys.argv) > 6 else 0xFF

            simulate_dispatch(tile_addr, man_nv_cnt, ugd_vec_size,
                            broadcast, col_start, col_en)

        except ValueError as e:
            print(f"Error parsing arguments: {e}")
            print("Run 'python3 dispatch.py help' for usage")
            sys.exit(1)

    else:
        print("Invalid number of arguments")
        print("Run 'python3 dispatch.py help' for usage")
        sys.exit(1)


if __name__ == "__main__":
    main()