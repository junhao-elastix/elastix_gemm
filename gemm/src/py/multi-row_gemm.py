
# Multi-Row GEMM Python Model
# This file implements a software model of the 2-D Multi-Row GEMM architecture described in the MULTI_ROW_REFERENCE.md.
# Each class and method is annotated to connect with the reference manual's architectural blocks and compute pattern.
#
# Memory Block format (528 lines total):
# - Lines 0-15: Exponents (16 lines × 32 bytes = 512 exponents for 128 NVs × 4 groups)
# - Lines 16-527: Mantissas (512 lines × 32 bytes per line, one group per line)
# - Default behavior has Memory Blocks for each compute row
# 
# Simplifications from hardware:
# - Each line is 32 uint8 values (not 256-bit packed)
# - No cycle-accurate timing model

import numpy as np

# =============================================================================
# Utility: V and C Partitioning (matches MULTI_ROW_REFERENCE.md exactly)
# =============================================================================

def get_v_partition(r, V, num_rows):
    """
    Get the V dimension partition for row r.
    First (V % num_rows) rows get (V // num_rows + 1) elements.
    Returns: (v_start, v_count)
    """
    v_base = V // num_rows
    v_rem = V % num_rows
    if r < v_rem:
        v_count = v_base + 1
        v_start = r * (v_base + 1)
    else:
        v_count = v_base
        v_start = v_rem * (v_base + 1) + (r - v_rem) * v_base
    return v_start, v_count

def get_c_partition(t, C, num_tiles):
    """
    Get the C dimension partition for tile t.
    First (C % num_tiles) tiles get (C // num_tiles + 1) columns.
    Returns: (c_start, c_count)
    """
    c_base = C // num_tiles
    c_rem = C % num_tiles
    if t < c_rem:
        c_count = c_base + 1
        c_start = t * (c_base + 1)
    else:
        c_count = c_base
        c_start = c_rem * (c_base + 1) + (t - c_rem) * c_base
    return c_start, c_count

# =============================================================================
# Infrastructure Classes
# =============================================================================

class FIFO:
    """Streaming FIFO (Reference Manual: connects Fetcher and Dispatcher)"""
    def __init__(self, maxlen=None):
        self.queue = []
        self.maxlen = maxlen

    def push(self, item):
        if self.maxlen is not None and len(self.queue) >= self.maxlen:
            raise OverflowError("FIFO is full")
        self.queue.append(item)

    def pop(self):
        if not self.queue:
            raise IndexError("FIFO is empty")
        return self.queue.pop(0)

    def empty(self):
        return len(self.queue) == 0

    def __len__(self):
        return len(self.queue)

    def clear(self):
        self.queue.clear()


class MemBlk:
    """
    Memory Block abstraction (Reference Manual: 528 lines simplified to 512)
    Represents data in DDR: 512 lines × 32 elements per line.
    - For activations: stored as (v_count × B) where line[v] contains A[all_b, v]
    - For weights: stored as (v_count × C) where line[v] contains W[v, all_c]
    """
    def __init__(self, num_lines=528, line_size=32):
        self.data = np.zeros((num_lines, line_size), dtype=np.uint8)
        self.num_lines = num_lines
        self.line_size = line_size

    def from_hex(self, hex_file):
        """Load data from a hex file. Each line contains space-separated hex bytes."""
        with open(hex_file, 'r') as f:
            for line_idx, line in enumerate(f):
                if line_idx >= self.num_lines:
                    break
                # Parse hex bytes from the line
                hex_bytes = line.strip().split()
                for col_idx, hex_byte in enumerate(hex_bytes):
                    if col_idx >= self.line_size:
                        break
                    # Convert hex string to uint8
                    self.data[line_idx, col_idx] = int(hex_byte, 16)

    def read_line(self, line_idx):
        """Read an entire line from the memory block"""
        assert 0 <= line_idx < self.num_lines, f"line_idx {line_idx} out of range"
        return self.data[line_idx, :]

    def write_line(self, line_idx, values):
        """Write an entire line to the memory block"""
        assert 0 <= line_idx < self.num_lines, f"line_idx {line_idx} out of range"
        assert len(values) <= self.line_size, f"Too many values: {len(values)} > {self.line_size}"
        self.data[line_idx, :len(values)] = values

    def write_element(self, line, col, value):
        """Write a single element"""
        assert 0 <= line < self.num_lines and 0 <= col < self.line_size, \
            f"Index out of bounds: line={line}, col={col}"
        self.data[line, col] = value

    def read_element(self, line, col):
        assert 0 <= line < self.num_lines and 0 <= col < self.line_size
        return self.data[line, col]

    def clear(self):
        self.data.fill(0)


# =============================================================================
# Dispatcher Control (Fetcher + Dispatcher per row)
# =============================================================================

class Fetcher:
    """
    Fetcher (Reference Manual: DMA engine, streams from DDR to FIFO)
    Simplified: transfers specified number of lines from MemBlk to FIFO.
    """
    def __init__(self):
        self.fifo = FIFO()

    def exec_fetch(self, cmd, memblk):
        """Push num_lines from memblk to the FIFO"""
        # Start Address is the starting line address in the memory block
        assert cmd['op_code'] == 0xF0, f"cmd op_code {cmd['op_code']} does not match FETCH"
        start_addr = cmd['start_addr']
        curr_addr = start_addr
        # Length is the number of lines to fetch
        # Default length is 528 lines
        for i in range(cmd['len']):
            # Read the line from the memory block
            line = memblk.read_line(curr_addr)
            # Push the line to the FIFO
            self.fifo.push(line)
            # Increment the current address
            curr_addr += 1

class Dispatcher:
    """
    Dispatcher (Reference Manual: routes FIFO data to row_bram or mlp_bram)
    - Left (activations): broadcast to row_bram
    - Right (weights): distribute to mlp_brams based on column assignment
    """
    def __init__(self, num_tiles):
        self.num_tiles = num_tiles
        
        # Global write address start, persisted across dispatches
        # Updates only when wrapping around (see exec_dispatch comment for examples)
        # wraddr = wraddr_start + v*4 + l
        self.wraddr_start = 0

    def exec_dispatch(self, cmd, fifo, comp_engine):
        """
        Dispatch data from FIFO to row_bram (left/activations) or mlp_brams (right/weights).
        
        =============================================================================
        MEMORY BLOCK FORMAT (528 lines total, each line is 256-bit = 32 bytes)
        =============================================================================
        - Lines 0-15:   Exponents (16 lines × 32 bytes = 512 exponent bytes)
        - Lines 16-527: Mantissas (512 lines × 32 bytes = 16384 mantissa bytes)
        
        Each Native Vector (NV) contains:
        - 4 exponent bytes (4 groups, 1 byte each)
        - 4 mantissa lines (4 groups × 32 bytes = 128 bytes)
        
        So 128 NVs = 512 exponent bytes (fits in 16 lines) + 512 mantissa lines.
        
        =============================================================================
        DATA LAYOUT: UGD-MAJOR (B-major for left, C-major for right)
        =============================================================================
        The memblk stores data in "UGD-major" order:
        - For LEFT (activations):  B-major → all V values for B=0, then all V for B=1, ...
        - For RIGHT (weights):     C-major → all V values for C=0, then all V for C=1, ...
        
        Example with B=4, V=4 (total 16 NVs = 64 mantissa lines):
            Lines 0-15:   B=0, V=[0,1,2,3]  (4 NVs × 4 lines/NV)
            Lines 16-31:  B=1, V=[0,1,2,3]
            Lines 32-47:  B=2, V=[0,1,2,3]
            Lines 48-63:  B=3, V=[0,1,2,3]
        
        =============================================================================
        V PARTITIONING AND STRIDED ACCESS
        =============================================================================
        V is partitioned across rows. Each row handles a slice: V[v_start:v_start+v_count]
        
        Example: V=4 partitioned across 4 rows
            Row 0: v_start=0, v_count=1 → handles V[0]
            Row 1: v_start=1, v_count=1 → handles V[1]
            Row 2: v_start=2, v_count=1 → handles V[2]
            Row 3: v_start=3, v_count=1 → handles V[3]
        
        PROBLEM: With UGD-major layout, the V slice for each batch is NOT contiguous!
            Row 1 needs: B=0,V[1] (lines 4-7), B=1,V[1] (lines 20-23), B=2,V[1] (lines 36-39)...
            These are scattered with stride = total_V * 4 lines between batches.
        
        SOLUTION: Use indexed buffer access instead of sequential FIFO pops.
            Source line index = ugd_idx * total_V * 4 + actual_v * 4 + l
            where:
                - ugd_idx = batch index (b) for left, or column index (c) for right
                - total_V = original V before partitioning (defines stride)
                - actual_v = v_start + v (the actual V index in original data)
                - l = line within NV (0-3 for the 4 groups)
        
        =============================================================================
        EXPONENT INDEXING
        =============================================================================
        Exponents follow the same UGD-major layout but stored as individual bytes:
            exp_idx = ugd_idx * total_V * 4 + actual_v * 4 + l
        
        Each NV has 4 exponent bytes (one per group), so the indexing parallels mantissas.
        
        =========================================================================
        Extract V partitioning parameters
        =========================================================================
        These parameters control sequential vs strided access.

        PER-ROW MEMBLK MODE (sequential access)
        ======================================
        The emulator assumes per-row memblks where each row's memblk contains
        only the V slice for that row. This matches the hardware model where
        each row has its own GDDR6 memory channel.

        v_start = 0 (data starts at beginning of this row's memblk)
        v_count = this row's V slice size (e.g., 32)
        total_V = v_count (only this row's V in the memblk)

        → Access formula: index = ugd * total_V * 4 + actual_v * 4 + l
            which reduces to sequential reads within each row's memblk.
        """
        assert cmd['op_code'] == 0xF1, f"cmd op_code {cmd['op_code']} does not match DISPATCH"

        # Per-row memblk mode: data for this row starts at the beginning
        # of the memblk and total_V == v_count (sequential access).
        v_start = 0                            # Data starts at beginning of this row's memblk
        v_count = cmd['ugd_len']               # This row's V count (= ugd_len for this row)
        total_V = v_count                      # Per-row mode: total_V equals v_count
        
        # =========================================================================
        # PHASE 1: Buffer all exponents for indexed access
        # =========================================================================
        # Read all 16 exponent lines (512 bytes total) into a flat buffer.
        # This allows random access by index instead of sequential FIFO pops.
        exp_buffer = []
        for i in range(16):
            line = fifo.pop()
            for exp_byte in line:
                exp_buffer.append(exp_byte)
        # exp_buffer[i] = exponent byte at flat index i
        # To access exponent for (ugd_idx, nv_idx, group_idx):
        #   index = ugd_idx * total_V * 4 + nv_idx * 4 + group_idx
        
        # =========================================================================
        # PHASE 2: Buffer all mantissa lines for indexed access
        # =========================================================================
        # Read remaining mantissa lines into a list. Each element is one 32-byte line.
        man_buffer = []
        while not fifo.empty():
            man_buffer.append(fifo.pop())
        # man_buffer[i] = mantissa line (32 bytes) at line index i
        # To access mantissa for (ugd_idx, nv_idx, line_within_nv):
        #   index = ugd_idx * total_V * 4 + nv_idx * 4 + line_within_nv
        
        # =========================================================================
        # PHASE 3: Dispatch data based on direction
        # =========================================================================
        if cmd['disp_right'] == 0:
            # -----------------------------------------------------------------
            # LEFT DISPATCH: Activations → row_bram
            # -----------------------------------------------------------------
            # Data layout: B-major
            # We write to RowBram sequentially (line_idx) and read from
            # man_buffer/exp_buffer using the indexed access formula to extract
            # the V slice for each batch.
            #
            # RowBram destination layout after dispatch:
            #   Lines 0 to (v_count*4-1):           B=0, V[v_start:v_start+v_count]
            #   Lines (v_count*4) to (2*v_count*4-1): B=1, V[v_start:v_start+v_count]
            #   ...
            line_idx = 0  # Sequential write index into row_bram
            
            for b in range(cmd['nv_cnt']):        # Loop over batches (B)
                for v in range(v_count):           # Loop over this row's V slice
                    actual_v = v_start + v         # Map local v to global V index
                    
                    for l in range(4):             # Loop over 4 lines per NV (4 groups)
                        # -----------------------------------------------------
                        # Calculate source indices using stride formula:
                        #   index = b * total_V * 4 + actual_v * 4 + l
                        #
                        # Breakdown:
                        #   b * total_V * 4  = skip past all V*4 lines for batches 0..b-1
                        #   actual_v * 4     = skip past 4 lines for each V before actual_v
                        #   l                = specific line within this NV
                        # -----------------------------------------------------
                        man_line_idx = b * total_V * 4 + actual_v * 4 + l
                        exp_idx = b * total_V * 4 + actual_v * 4 + l
                        
                        curr_man = man_buffer[man_line_idx]
                        curr_exp = exp_buffer[exp_idx]
                        
                        # Write to row_bram at sequential destination
                        comp_engine.RowBram.write(line_idx, curr_exp, curr_man)
                        line_idx += 1
        else:
            # -----------------------------------------------------------------
            # RIGHT DISPATCH: Weights → mlp_brams (distributed across columns)
            # -----------------------------------------------------------------
            # Data layout: C-major
            # We read weights using the indexed access formula and distribute
            # them across mlp_brams according to column assignment.
            #
            # Column distribution:
            #   - Each physical MLP has 2 banks (2 logical columns)
            #   - C values are distributed round-robin across logical columns
            #   - C0 → MLP0 bank0, C1 → MLP0 bank1, C2 → MLP1 bank0, ...
            #
            # Group splitting:
            #   - Each mantissa line has 32 elements (one GFP group)
            #   - Split across 4 MLPRows: each gets 8 elements
            #   - This matches the MLPStack architecture where 4 MLPRows
            #     together process one 32-element group
            col_start = cmd['col_start']
            col_sel = col_start  # Current logical column for round-robin
            
            # Get column configuration from MLP structure
            cols_per_tile = comp_engine.MLPStack.MLPRows[0].mlps[0].mlp_bram.cols_per_tile
            total_logical_cols = self.num_tiles * cols_per_tile
            
            for c in range(cmd['nv_cnt']):         # Loop over columns (C)
                for v in range(v_count):            # Loop over this row's V slice
                    actual_v = v_start + v          # Map local v to global V index
                    
                    for l in range(4):              # Loop over 4 lines per NV
                        # -----------------------------------------------------
                        # Source index calculation (same formula, C-major)
                        # -----------------------------------------------------
                        man_line_idx = c * total_V * 4 + actual_v * 4 + l
                        exp_idx = c * total_V * 4 + actual_v * 4 + l
                        
                        curr_man = man_buffer[man_line_idx]
                        curr_exp = exp_buffer[exp_idx]
                        assert len(curr_man) == 32, f"curr_man length {len(curr_man)} should be 32"
                        
                        # -----------------------------------------------------
                        # Map logical column to physical MLP and bank
                        # -----------------------------------------------------
                        # bank_idx: which bank within the MLP (0 or 1)
                        # real_col_idx: which physical MLP (0 to num_tiles-1)
                        bank_idx = col_sel % cols_per_tile
                        real_col_idx = col_sel // cols_per_tile
                        
                        # -----------------------------------------------------
                        # Calculate write address in mlp_bram
                        # -----------------------------------------------------
                        # wraddr = base + offset within this column's V data
                        # v is the local V index (0 to v_count-1), not actual_v
                        wraddr = self.wraddr_start + v * 4 + l
                        
                        # -----------------------------------------------------
                        # Split 32-element group across 4 MLPRows
                        # -----------------------------------------------------
                        # MLPRow s gets elements [s*8 : (s+1)*8]
                        # Each MLP in each row stores 8 elements per line
                        for s in range(4):
                            comp_engine.MLPStack.MLPRows[s].mlps[real_col_idx].mlp_bram.write(
                                bank_idx, wraddr, curr_exp, curr_man[s*8:(s+1)*8]
                            )
                
                # ---------------------------------------------------------
                # Move to next logical column (round-robin distribution)
                # ---------------------------------------------------------
                if col_sel >= total_logical_cols - 1:
                    # Wrapped around: advance wraddr_start for next round
                    col_sel = 0
                    self.wraddr_start += v_count * 4
                else:
                    col_sel += 1
                            
    def reset_wraddr_start(self):
        self.wraddr_start = 0

class DispatcherControl:
    """
    Dispatcher Control (Reference Manual: couples Fetcher and Dispatcher per row)
    Wrapper class for Fetcher and Dispatcher per row
    Coordinates fetch from DDR (via MemBlk) and dispatch to compute buffers.
    """
    def __init__(self, num_tiles):
        self.num_tiles = num_tiles
        self.fetcher = Fetcher()
        self.dispatcher = Dispatcher(self.num_tiles)

# =============================================================================
# Compute Engine (per row)
# =============================================================================

class RowBram:
    """
    row_bram (Reference Manual: Dedicated Activation Buffer)
    Shared across all tiles in a row. Stores activations.
    Layout: B-major ordering - all V values for each batch are stored together.
            For B batches and V values: line[batch*V*4 + v*4 : batch*V*4 + v*4 + 3] = batch B, V index v
            Each V takes 4 lines (Native Vector = 4 mantissa groups)
    """
    def __init__(self, num_lines=512, line_size=32):
        self.nv_exp = np.zeros((num_lines, 1), dtype=np.uint8)
        self.nv_man = np.zeros((num_lines, line_size), dtype=np.uint8)
        self.num_lines = num_lines
        self.line_size = line_size

    def write(self, line_idx, nv_exp:np.uint8, nv_man:list[np.uint8]):
        assert 0 <= line_idx < self.num_lines, f"line_idx {line_idx} out of range"
        assert len(nv_man) == self.line_size, f"nv_man {nv_man} length incorrect"
        self.nv_exp[line_idx] = nv_exp
        self.nv_man[line_idx] = nv_man

    def read(self, line_idx):
        assert 0 <= line_idx < self.num_lines
        return self.nv_exp[line_idx], self.nv_man[line_idx]

    def clear(self):
        self.nv_exp.fill(0)
        self.nv_man.fill(0)


class MLPBram:
    """
    mlp_bram (Reference Manual: Weight BRAM, per-tile weight storage)
    Each tile has its own mlp_bram storing weights for its assigned columns.
    Layout: bank[bank_idx][line_idx] = weights for this tile's columns at line_idx. 
    bank_idx is 0 or 1. line_idx is 0 to 511.
    """
    def __init__(self, num_lines=512, line_size=8, cols_per_tile=2):
        self.cols_per_tile = cols_per_tile
        # There are cols_per_tile banks in each MLPBram.
        # The default is 2 banks, it is a hard hardware limitation. So it cannot be changed.
        # We call it bank 0 and bank 1. 
        self.nv_exp = np.zeros((cols_per_tile, num_lines, 1), dtype=np.uint8)
        self.nv_man = np.zeros((cols_per_tile, num_lines, line_size), dtype=np.uint8)
        self.num_lines = num_lines
        self.line_size = line_size

    def write(self, bank_idx, line_idx, nv_exp:np.uint8, nv_man:list[np.uint8]):
        """Write weight values for this tile at given V index"""
        assert 0 <= line_idx < self.num_lines
        assert len(nv_man) == self.line_size, f"nv_man {nv_man} length incorrect"
        self.nv_exp[bank_idx, line_idx] = nv_exp
        self.nv_man[bank_idx, line_idx] = nv_man

    def read(self, bank_idx, line_idx):
        assert 0 <= line_idx < self.num_lines
        return self.nv_exp[bank_idx, line_idx], self.nv_man[bank_idx, line_idx]

    def clear(self):
        self.nv_exp.fill(0)
        self.nv_man.fill(0)

class MLP:
    """
    Machine Learning Processor (Reference Manual: dot product compute unit)
    
    Computes 2 dot products, each with 8 element-wise multiplications (16 total).
    - Takes 8 elements from left (row_bram)
    - Takes 16 elements from right (mlp_bram): 8 from bank 0 + 8 from bank 1
    - Outputs 2 results: dot(left[8], right_bank0[8]) and dot(left[8], right_bank1[8])
    
    Inputs: 
    - left_exp: left exponent (1 byte, shared by all 8 left mantissas)
    - left_man: left mantissa (8 bytes)
    - right_exp_0, right_exp_1: right exponents (1 byte each, read from mlp_bram banks)
    - right_man_0, right_man_1: right mantissas (8 bytes each, read from mlp_bram banks)
    
    Outputs:
    - result_0: dot product of left[8] • right_bank0[8] (float)
    - result_1: dot product of left[8] • right_bank1[8] (float)
    """
    def __init__(self, left_exp_bias=15, right_exp_bias=15):
        self.left_exp_bias = left_exp_bias
        self.right_exp_bias = right_exp_bias
        self.mlp_bram = MLPBram()  # MLPBram instance for this 

    def dot(self, left_exp: np.uint8, left_man: list[np.uint8], line_idx: int):
        """
        Compute GFP8 dot product for one MLP (16 elements) with two columns. 
        8 element will come from each bank of the mlp_bram.
        
        Reads weights from MLPBram at the specified line_idx for both banks (0 and 1),
        then computes two dot products:
        - left dot right_0 (bank 0, column 0)
        - left dot right_1 (bank 1, column 1)
        
        Formula derivation (traced from emulator):
        ==========================================
        Each element is represented as: mantissa × 2^(exponent - bias)
        Reference: emulator/src/emulator/group_floating_point.py:633-634
            scales = 2.0 ** (self.exp_data - self.dtype.exp_bias)
            x = self.mantissa_data_signed * scales
        
        Dot product = sum_i (left_man[i] × 2^(left_exp - left_bias)) × 
                           (right_man[i] × 2^(right_exp - right_bias))
        
        When multiplying two GFP values, exponents are added:
        Reference: emulator/src/emulator/group_floating_point.py:716
            e = lhs.exp_data.permute(0, 2, 1) + rhs.exp_data.permute(2, 0, 1)
        
        This simplifies to:
                    = 2^(left_exp + right_exp - left_bias - right_bias) × 
                      sum_i (left_man[i] × right_man[i])
        
        Args:
            left_exp: uint8, shared exponent for left group (1 byte)
            left_man: array of uint8, 8 mantissas for left group (8 bytes)
            line_idx: int, line index in MLPBram to read weights from
        
        Returns:
            tuple[float, float]: (dot_product_bank0, dot_product_bank1) - two float results for two columns
        """
        if self.mlp_bram is None:
            raise ValueError("MLPBram must be set before calling dot()")
        
        # Read weights from both banks at the specified line
        right_exp_0, right_man_0 = self.mlp_bram.read(0, line_idx)  # Bank 0, column 0
        right_exp_1, right_man_1 = self.mlp_bram.read(1, line_idx)  # Bank 1, column 1
        assert len(left_man) == 8, f"left_man {left_man} length incorrect"
        assert len(right_man_0) == 8, f"right_man_0 {right_man_0} length incorrect"
        assert len(right_man_1) == 8, f"right_man_1 {right_man_1} length incorrect"
        
        # Extract scalar exponent values (arrays from BRAM have shape (1,), extract the scalar)
        left_exp_scalar = int(left_exp.item() if isinstance(left_exp, np.ndarray) else left_exp)
        right_exp_0_scalar = int(right_exp_0.item() if isinstance(right_exp_0, np.ndarray) else right_exp_0)
        right_exp_1_scalar = int(right_exp_1.item() if isinstance(right_exp_1, np.ndarray) else right_exp_1)
        
        # Convert mantissas from uint8 to int8 (signed), then upcast to int32 to avoid overflow
        # uint8 range [0, 255] maps to int8 range [-128, 127]
        # Values 0-127 stay the same, values 128-255 become -128 to -1
        # Note: Must use int32 for dot product to avoid overflow in int8
        left_man_signed = np.array(left_man, dtype=np.int8).astype(np.int32)
        right_man_0_signed = np.array(right_man_0, dtype=np.int8).astype(np.int32)
        right_man_1_signed = np.array(right_man_1, dtype=np.int8).astype(np.int32)
        
        # Compute dot product of mantissas for bank 0: sum(left_man[i] * right_man_0[i])
        mantissa_dot_0 = np.dot(left_man_signed, right_man_0_signed)
        
        # Compute dot product of mantissas for bank 1: sum(left_man[i] * right_man_1[i])
        mantissa_dot_1 = np.dot(left_man_signed, right_man_1_signed)
        
        # Compute combined scale factors
        # When multiplying: (m1 × 2^(e1-bias)) × (m2 × 2^(e2-bias)) 
        #                 = (m1 × m2) × 2^(e1+e2-2*bias)
        # Reference: emulator/src/emulator/group_floating_point.py:716 (exponent addition)
        # For dot product with shared exponents:
        # scale = 2^(left_exp + right_exp - left_bias - right_bias)
        # Reference: emulator/src/emulator/group_floating_point.py:633 (scale calculation)
        combined_exp_0 = left_exp_scalar + right_exp_0_scalar - self.left_exp_bias - self.right_exp_bias
        combined_exp_1 = left_exp_scalar + right_exp_1_scalar - self.left_exp_bias - self.right_exp_bias
        scale_0 = 2.0 ** combined_exp_0
        scale_1 = 2.0 ** combined_exp_1
        
        # Final results for both columns
        result_0 = float(mantissa_dot_0 * scale_0)
        result_1 = float(mantissa_dot_1 * scale_1)
        
        return (result_0, result_1)

class MLPRow:
    """
    MLP Row (Reference Manual: row of MLPs)
    
    One MLPRow processes 8 elements (1/4 of a 32-element group).
    Each row has multiple MLPs (columns), each with its own MLPBram.
    The 8 activation elements are broadcast to all MLPs in the row.
    """
    def __init__(self, num_mlps_per_row=8):
        self.num_mlps_per_row = num_mlps_per_row
        # Each MLP has its own MLPBram (8 elements per line per bank)
        self.mlps = [MLP() for _ in range(num_mlps_per_row)]

    def compute(self, act_exp: np.uint8, act_man: list[np.uint8], line_idx: int):
        """
        Compute GFP8 dot product for 8 elements across all MLPs in the row.
        
        Each row has 8 MLPs (columns).
        Each MLP has 2 banks in its BRAM (bank 0 and bank 1).
        So logically, we compute two logical columns per MLP, 16 logical columns total.
        The 8 activation elements are broadcast to all MLPs in the row.
        
        Args:
            act_exp: uint8, shared exponent for this row's sub-group (1 byte)
            act_man: array of uint8, 8 mantissas for this row's sub-group (8 bytes)
            line_idx: int, line index in MLPBram to read weights from (rdaddr)
        
        Returns:
            list of floats: [result_col0, result_col1, ...] for each MLP
            Total of 16 float results (8 MLPs × 2 banks each)
        """
        assert len(act_man) == 8, f"act_man length {len(act_man)} should be 8"
        results = []
        for col_idx in range(self.num_mlps_per_row):
            # Each MLP computes two dot products (one per bank/column)
            result_col0, result_col1 = self.mlps[col_idx].dot(act_exp, act_man, line_idx)
            results.append(result_col0)
            results.append(result_col1)
        assert len(results) == self.num_mlps_per_row * 2, f"results {results} length incorrect"
        return results

class MLPStack:
    """
    MLP Stack (Reference Manual: stack of MLPRows)
    
    Architecture:
    - 4 MLPRows (one per 8-element sub-group)
    - Each MLPRow has 8 MLPs (columns)
    - One 32-element group from RowBram is split across 4 rows (8 elements each)
    - All 4 MLPs in the same column (across 4 rows) together process one complete group
    """
    def __init__(self, num_rows_per_stack=4, num_mlps_per_row=8):
        self.num_rows_per_stack = num_rows_per_stack
        self.num_mlps_per_row = num_mlps_per_row
        self.MLPRows = [MLPRow(num_mlps_per_row=num_mlps_per_row) for _ in range(num_rows_per_stack)]

    def compute(self, act_exp_group: np.uint8, act_man_group: list[np.uint8], line_idx: int):
        """
        Compute GFP8 dot products for one group across all columns.
        
        One Native Vector = 4 groups × 32 elements = 128 elements total.
        Each group (32 elements) is split across 4 MLPRows (8 elements each).
        Results from all 4 rows are summed to produce the final dot product.
        
        Args:
            act_exp_group: 1 exponent (one per group, shared by all 4 rows processing that group)
            act_man_group: 1 mantissa arrays (each 32 bytes, one group per line from RowBram)
            line_idx: base line index in mlp_brams (each row reads from line_idx)
        
        Returns:
            list of 16 floats: dot product results for 8 MLPs × 2 banks
        """
        assert len(act_man_group) == 32, f"act_man_group length {len(act_man_group)} should be 32"
        
        # Initialize results as zeros: 8 MLPs × 2 banks = 16 results
        results = [0.0] * (self.num_mlps_per_row * 2)
        
        # Split the 32-element group across 4 MLPRows (8 elements each)
        for row_idx in range(self.num_rows_per_stack):
            # Each row gets its 8-element portion: row 0 gets [0:8], row 1 gets [8:16], etc.
            act_man_part = act_man_group[row_idx * 8 : (row_idx + 1) * 8]
            
            # Each row reads weights from line_idx
            # All 4 rows processing the same group read from the same mlp_bram line
            row_results = self.MLPRows[row_idx].compute(act_exp_group, act_man_part, line_idx)
            
            # Element-wise addition: accumulate partial results from each row
            results = [results[i] + row_results[i] for i in range(len(results))]
        
        assert len(results) == self.num_mlps_per_row * 2, f"results length {len(results)} should be {self.num_mlps_per_row * 2}"
        return results

class ComputeEngine:
    """
    Compute Engine (Reference Manual: 1-D array of compute tiles per row)
    
    Contains:
    - RowBram: stores activations (32 elements per line = one group)
    - MLPStack: 4 MLPRows × 8 MLPs (columns) = 32 MLPs total
    
    Data flow:
    - RowBram provides 32-element groups (one line)
    - Each group is split across 4 MLPRows (8 elements each)
    - Each MLP computes 2 dot products (one per bank)
    """
    def __init__(self, num_cols):
        self.num_cols = num_cols

        # MLPStack: 4 rows × num_cols MLPs per row
        self.MLPStack = MLPStack(num_rows_per_stack=4, num_mlps_per_row=num_cols)

        # RowBram: 32 elements per line (one complete group)
        self.RowBram = RowBram()

        self.result_fifo = FIFO()

    def compute(self, cmd):
        """
        Compute left_len * right_len dot products.
        Returns: left_len * right_len float results.
        cmd: {
            left_addr,
            right_addr,
            left_len,
            right_len,
            ugd_len,
            left_4b,
            right_4b,
            main_loop_left
        }

        If we have B32 V4,the row bram is arranged as:
        line 00-03: B0 V0
        line 04-07: B0 V1
        line 08-11: B0 V2
        line 12-15: B0 V3
        line 16-19: B1 V0
        line 20-23: B1 V1
        ... 
        line 504-507: B31 V2
        line 508-511: B31 V3

        If we have C16V4 for the mlp brams, it will stop at line 255, arranged as C-major,
        and the rest are garbage.

        Each compute engine will compute B(left_len) and C(right_len) in total. 
        In general, it will perform the matrix multiplication with 
        the outer dimensions of B(left_len) and C(right_len) and the inner dimension of V(ugd_len).
        The V (ugd_len) dimension is handled inside the MLPStack.

        Each MLPStack computes B = 1 batch and C = 16 columns at a time.
        The Compute Engine has one MLPStack.
        At the beginning of the Compute Engine compute process, which is triggered by the MATMUL command,
        the row bram and mlp brams will be loaded as mentioned above.

        For visualization: B4 C22 V2
        row bram:
        Line 0-7  B0
        Line 8-15 B1
        Line 16-23 B2
        Line 24-31 B3
        mlp brams:
                    Col0      | Col1      | Col2      | Col3      |
        Line 0-7    C0        | C1        | C2        | C3        |
        Line 8-15   C4        | C5        | C6        | C7        | 
        Line 16-23  C8        | C9        | C10       | C11       |
        Line 24-31  C12       | C13       | C14       | C15       |
        Line 32-39  C16       | C17       | C18       | C19       |
        Line 40-47  C20       | C21       | EMPTY     | EMPTY     |

        result:
        first round: 
        result_fifo:[B0*C0, B0*C1, B0*C2, B0*C3]
        second round:
        result_fifo:[B0*C4, B0*C5, B0*C6, B0*C7]
        third round:
        result_fifo:[B0*C8, B0*C9, B0*C10, B0*C11]
        fourth round:
        result_fifo:[B0*C12, B0*C13, B0*C14, B0*C15]
        fifth round:
        result_fifo:[B0*C16, B0*C17, B0*C18, B0*C19]
        sixth round:
        result_fifo:[B0*C20, B0*C21, EMPTY, EMPTY]
        seventh round:
        result_fifo:[B1*C0, B1*C1, B1*C2, B1*C3]
        eighth round:
        result_fifo:[B1*C4, B1*C5, B1*C6, B1*C7]
        ninth round:
        result_fifo:[B1*C8, B1*C9, B1*C10, B1*C11]
        tenth round:
        result_fifo:[B1*C12, B1*C13, B1*C14, B1*C15]
        ......
        last round:
        result_fifo:[B3*C16, B3*C17, B3*C18, B3*C19]
        result_fifo:[B3*C20, B3*C21, EMPTY, EMPTY]
        """
        assert cmd['op_code'] == 0xF2, f"cmd op_code {cmd['op_code']} does not match MATMUL"

        left_addr_start = cmd['left_addr']
        right_addr_start = cmd['right_addr']
        V = cmd['ugd_len']
        
        # Each physical MLP has 2 banks, so logical_cols = num_cols * 2
        # This matches the dispatch distribution: C0->col0, C1->col1, ..., C(logical_cols-1)->col(logical_cols-1)
        logical_cols = self.num_cols * 2
        
        # Number of c_groups: ceiling division to handle partial last group
        num_c_groups = (cmd['right_len'] + logical_cols - 1) // logical_cols
        
        # Loop over B (left_len)
        for b in range(cmd['left_len']):
            # Base addr for the current Batch (B) in row_bram
            left_base = left_addr_start + b * V * 4
            
            # Loop over C groups (each group has logical_cols columns)
            for c_group in range(num_c_groups):
                # Base addr for the current C group in mlp_brams
                # All columns in this group share the same line range
                right_base = right_addr_start + c_group * V * 4
                
                # Accumulate V partial results for this (B, C_group) pair
                v_sum = [0.0] * (self.num_cols * 2)
                for v in range(V):
                    # Line index for current V in row_bram (left)
                    left_line_idx = left_base + v * 4
                    # Line index for current V in mlp_brams (right)
                    right_line_idx = right_base + v * 4
                    
                    # For four lines in a NV, each line is a group
                    # Both left (RowBram) and right (mlp_bram) advance by l within the NV
                    for l in range(4):
                        left_exp_group, left_man_group = self.RowBram.read(left_line_idx + l)
                        assert len(left_man_group) == 32, f"left_man_group length {len(left_man_group)} should be 32"
                        # Compute partial dot products with mlp_brams at right_line_idx + l
                        # Each line l within the NV corresponds to the same line index in mlp_brams
                        partial_v = self.MLPStack.compute(left_exp_group, left_man_group, right_line_idx + l)
                        v_sum = [v_sum[i] + partial_v[i] for i in range(len(v_sum))]
                
                # Push results for all num_cols columns at once
                # For the B4 C22 V2 example, each push contains [B*C0, B*C1, B*C2, B*C3]
                self.result_fifo.push(v_sum)


# =============================================================================
# Result Collection (global reduction across rows)
# =============================================================================

class ResultCollector:
    """
    Result Collection (Reference Manual: reduces all row outputs to final result)
    Sums partial results from all rows to produce final output.
    
    Each ComputeEngine pushes lists of (num_cols * 2) floats per c_group.
    For B=4, C=22, num_cols=8 (16 logical columns):
      - num_c_groups = ceiling(22/8) = 3
      - Per batch: 3 pushes, each with 16 floats (last group may have padding)
      - Total pushes per CE: 4 * 3 = 12
    
    We need to flatten the results and extract only valid columns (ignoring padding).
    """
    def __init__(self, num_rows):
        self.num_rows = num_rows

    def reduce(self, cmd, compute_engines:list[ComputeEngine], final_results:list[float]):
        """Sum all row results to produce final output"""
        right_len = cmd['right_len']  # C: total columns
        left_len = cmd['left_len']    # B: batch size
        
        # Collect results from all compute engines
        # Each CE's result_fifo contains lists of (num_cols * 2) floats
        all_ce_flat_results = []
        for compute_engine in compute_engines:
            ce_flat = []
            while not compute_engine.result_fifo.empty():
                # Each pop returns a list of floats for one (batch, c_group) pair
                v_sum = compute_engine.result_fifo.pop()
                ce_flat.extend(v_sum)
            all_ce_flat_results.append(ce_flat)
        
        assert len(all_ce_flat_results) == self.num_rows, \
            f"all_ce_flat_results length {len(all_ce_flat_results)} should be {self.num_rows}"
        
        # Get num_cols from the first compute engine to calculate c_group structure
        if len(compute_engines) > 0:
            num_cols = compute_engines[0].num_cols
            logical_cols = num_cols * 2  # Each MLP produces 2 results (2 banks)
            num_c_groups = (right_len + logical_cols - 1) // logical_cols
        else:
            return
        
        # Expected flat length per CE = left_len * num_c_groups * logical_cols
        expected_flat_len = left_len * num_c_groups * logical_cols
        for r in range(self.num_rows):
            assert len(all_ce_flat_results[r]) == expected_flat_len, \
                f"CE {r} flat results length {len(all_ce_flat_results[r])} should be {expected_flat_len}"
        
        # Sum results across all rows and extract valid columns
        # Output format: [B0*C0, B0*C1, ..., B0*C(right_len-1), B1*C0, ..., B(left_len-1)*C(right_len-1)]
        # 
        # C distribution to logical columns:
        # - C0 -> logical col 0 (MLP0 bank0)
        # - C1 -> logical col 1 (MLP0 bank1)
        # - C2 -> logical col 2 (MLP1 bank0)
        # - ...
        # - C(logical_cols-1) -> logical col (logical_cols-1)
        # - C(logical_cols) -> logical col 0 (next c_group, same MLP0 bank0)
        # 
        # Result ordering from MLPStack.compute: [MLP0b0, MLP0b1, MLP1b0, MLP1b1, ...]
        # which matches the logical column order.
        for b in range(left_len):
            for c in range(right_len):
                # Map (b, c) to flat index within CE results
                # c_group = which group of logical_cols this C belongs to
                # c_within_group = position within that group
                c_group = c // logical_cols
                c_within_group = c % logical_cols
                # Each c_group has logical_cols results; we want the c_within_group-th result
                flat_idx = b * num_c_groups * logical_cols + c_group * logical_cols + c_within_group
                
                result_sum = 0.0
                for r in range(self.num_rows):
                    result_sum += all_ce_flat_results[r][flat_idx]
                final_results.append(result_sum)

# =============================================================================
# Top-Level GEMM Orchestrator (Master Control)
# =============================================================================

class GEMM:
    """
    Top-level GEMM Orchestrator (Reference Manual: Master Control)
    Coordinates all rows and tiles to execute O = A × W.

    Architecture:
    - num_rows rows, each handling a slice of V dimension
    - num_tiles tiles per row, each handling a slice of C dimension
    - Row reduction produces final result
    
    Memory Modes:
    =============
    
    DEFAULT: Per-Row Memblk Mode (recommended)
    ------------------------------------------
    Primary mode matching real hardware where each row has its own GDDR6 channel.
    - Each row has its own memblk (self.memblks[r])
    - Data is pre-partitioned: each row's memblk contains only its V slice
    - Use load_row_memblk() to load data
    - v_start=0 and total_V=v_count → sequential access (no striding needed)
    """
    def __init__(self, num_rows=16, num_cols=8):
        self.num_rows = num_rows    
        self.num_cols = num_cols
        # Per-row memblks
        # Each row has its own memblk, matching real hardware with separate GDDR6 channels
        self.memblks = [MemBlk(num_lines=528, line_size=32) for _ in range(num_rows)]
        
        self.results = [0.0]

        # Create Compute Engines (one per row)
        self.compute_engines = [
            ComputeEngine(num_cols) for r in range(num_rows)
        ]

        # Create Dispatcher Controls (one per row)
        self.dispatcher_controls = [
            DispatcherControl(num_cols) for r in range(num_rows)
        ]

        # Result Collector
        self.result_collector = ResultCollector(num_rows)
    
    def load_row_memblk(self, row: int, data):
        """
        DEFAULT: Load data into a specific row's memory block (recommended).
        
        This is the primary mode matching real hardware where each row has its
        own GDDR6 channel with pre-partitioned data.
        
        Each row's memblk contains only that row's V slice, so:
          - v_start = 0 (data starts at beginning of this row's memblk)
          - total_V = v_count (only this row's V in the memblk)
          - The strided access formula reduces to sequential reads
        
        Args:
            row: Row index (0 to num_rows-1)
            data: Pre-partitioned data for this row
        """
        self.memblks[row].data = data
        # Per-row memblk mode enforced

    def reset_results(self, size=0):
        """Reset the results list to empty or specified size"""
        self.results.clear()
        if size > 0:
            self.results.extend([0.0] * size)
    
    def get_row_partial_results(self, row: int, cmd) -> list[float]:
        """
        Get partial results from a specific row's compute engine.
        
        This extracts results from the row's result_fifo WITHOUT consuming them,
        allowing subsequent reduction to still work.
        
        Returns a flat list of floats representing this row's contribution to
        the final B×C output matrix.
        """
        ce = self.compute_engines[row]
        right_len = cmd['right_len']  # C
        left_len = cmd['left_len']    # B
        num_cols = ce.num_cols
        logical_cols = num_cols * 2
        num_c_groups = (right_len + logical_cols - 1) // logical_cols
        
        # Peek at the result_fifo contents without consuming
        # We need to drain and re-push to peek
        results = []
        temp_storage = []
        while not ce.result_fifo.empty():
            v_sum = ce.result_fifo.pop()
            temp_storage.append(v_sum)
        
        # Re-push back to fifo
        for v_sum in temp_storage:
            ce.result_fifo.push(v_sum)
        
        # Flatten the results
        ce_flat = []
        for v_sum in temp_storage:
            ce_flat.extend(v_sum)
        
        # Extract valid columns (same logic as ResultCollector.reduce)
        for b in range(left_len):
            for c in range(right_len):
                c_group = c // logical_cols
                c_within_group = c % logical_cols
                flat_idx = b * num_c_groups * logical_cols + c_group * logical_cols + c_within_group
                results.append(ce_flat[flat_idx])
        
        return results

    def run(self, cmd):
        """
        Execute a single GEMM command.
        
        V Partitioning Flow:
        ====================
        The inner dimension V is partitioned across rows. Each row handles
        V[v_start:v_start+v_count] where:
          - v_start = starting V index for this row
          - v_count = number of V values this row handles
          - total_V = original V before partitioning (cmd['ugd_len'])
        
        Example: V=4 with 16 rows
          Row 0: v_start=0, v_count=1 → V[0]
          Row 1: v_start=1, v_count=1 → V[1]
          Row 2: v_start=2, v_count=1 → V[2]
          Row 3: v_start=3, v_count=1 → V[3]
          Rows 4-15: v_count=0 (no data)
        
        For each command, we compute the partition for each row and pass:
          - ugd_len = v_count (this row's portion)
          - v_start = starting index (for strided access in dispatch)
          - total_V = original V (for stride calculation)
        """
        if cmd['op_code'] == 0xF0:
            # =================================================================
            # FETCH: Load data from memblk into FIFO
            # =================================================================
            row_cmd = cmd.copy()
            for r in range(self.num_rows):
                v_start, v_count = get_v_partition(r, cmd['ugd_len'], self.num_rows)
                row_cmd['ugd_len'] = v_count
                row_cmd['v_start'] = v_start  # Which V index this row starts at (unused in per-row mode)
                # Clear FIFO before fetch to avoid mixing with unused data from previous dispatch
                # (Dispatch only consumes what it needs: 16 exp + nv_cnt*ugd_len*4 mantissa lines)
                self.dispatcher_controls[r].fetcher.fifo.clear()

                # Per-row memblk mode: each row fetches from its own pre-partitioned memblk
                memblk_to_use = self.memblks[r]
                self.dispatcher_controls[r].fetcher.exec_fetch(row_cmd, memblk_to_use)
        elif cmd['op_code'] == 0xF1:
            # =================================================================
            # DISPATCH: Route data from FIFO to BRAMs
            # =================================================================
            # The dispatch needs three V-related parameters:
            #   - ugd_len (v_count): how many V values this row processes
            #   - v_start: where this row's V slice starts in the global data
            #   - total_V: original V before partitioning, needed for stride calc
            #
            # Dispatch parameters for per-row memblk mode:
            #    - v_start = 0 (data starts at beginning of row's memblk)
            #    - total_V = v_count (only this row's V in memblk)
            #    - Sequential access: index = b * v_count * 4 + v * 4 + l
            row_cmd = cmd.copy()
            total_V_global = cmd['ugd_len']  # Original V before partitioning
            for r in range(self.num_rows):
                v_start, v_count = get_v_partition(r, total_V_global, self.num_rows)
                row_cmd['ugd_len'] = v_count

                # Per-row mode - data is pre-partitioned in each row's memblk.
                row_cmd['v_start'] = 0        # Data starts at beginning of row's memblk
                row_cmd['total_V'] = v_count  # Only this row's V in memblk

                self.dispatcher_controls[r].dispatcher.exec_dispatch(
                    row_cmd,
                    self.dispatcher_controls[r].fetcher.fifo,
                    self.compute_engines[r]
                )
        elif cmd['op_code'] == 0xF2:
            # =================================================================
            # MATMUL: Execute matrix multiplication in compute engines
            # =================================================================
            # Each row computes partial sums for its V slice.
            # Rows with v_count=0 produce zero results (V loop doesn't execute).
            row_cmd = cmd.copy()
            for r in range(self.num_rows):
                row_cmd['ugd_len'] = get_v_partition(r, cmd['ugd_len'], self.num_rows)[1]
                self.compute_engines[r].compute(row_cmd)
        elif cmd['op_code'] == 0xF3:
            # WAIT_DISPATCH: Wait for dispatch to complete (no-op in Python model)
            pass
        elif cmd['op_code'] == 0xF4:
            # WAIT_MATMUL: Wait for matmul to complete (no-op in Python model)
            pass
        elif cmd['op_code'] == 0xF5:
            # =================================================================
            # READOUT: Reduce partial results across all rows
            # =================================================================
            # Each row's compute engine has partial sums in its result_fifo.
            # The result collector sums across all rows to produce final output.
            # Rows with v_count=0 contributed zero partial sums.
            self.reset_results()
            self.result_collector.reduce(cmd, self.compute_engines, self.results)
        else:
            raise ValueError(f"Invalid command opcode: {cmd['op_code']}")

# =============================================================================
# Test Infrastructure
# =============================================================================

def cmd_fetch(cmd_id, start_addr, ugd_len, len, fetch_right):
    """
    Generate a fetch command.
    """
    return {
        'cmd_id': cmd_id,
        'op_code': 0xF0,
        'start_addr': start_addr,
        'ugd_len': ugd_len,
        'len': len,
        'fetch_right': fetch_right
    }

def cmd_dispatch(cmd_id, nv_cnt, ugd_len, tile_addr, col_start, disp_right, broadcast, man_4b):
    """
    Generate a dispatch command.
    """
    return {
        'cmd_id': cmd_id,
        'op_code': 0xF1,
        'nv_cnt': nv_cnt,
        'ugd_len': ugd_len,
        'tile_addr': tile_addr,
        'col_start': col_start,
        'disp_right': disp_right,
        'broadcast': broadcast,
        'man_4b': man_4b
    }

def cmd_matmul(cmd_id, left_addr, right_addr, left_len, right_len, ugd_len, left_4b, right_4b, main_loop_left):
    """
    Generate a matmul command.
    """
    return {
        'cmd_id': cmd_id,
        'op_code': 0xF2,
        'left_addr': left_addr,
        'right_addr': right_addr,
        'left_len': left_len,
        'right_len': right_len,
        'ugd_len': ugd_len,
        'left_4b': left_4b,
        'right_4b': right_4b,
        'main_loop_left': main_loop_left
    }

def cmd_wait_dispatch(cmd_id, wait_id):
    """
    Generate a wait dispatch command.
    """
    return {
        'cmd_id': cmd_id,
        'op_code': 0xF3,
        'wait_id': wait_id
    }

def cmd_wait_matmul(cmd_id, wait_id):
    """
    Generate a wait matmul command.
    """
    return {
        'cmd_id': cmd_id,
        'op_code': 0xF4,
        'wait_id': wait_id
    }

def cmd_readout(cmd_id, left_len, right_len, ugd_len):
    """
    Generate a readout command.
    """
    return {
        'cmd_id': cmd_id,
        'op_code': 0xF5,
        'left_len': left_len,
        'right_len': right_len,
        'ugd_len': ugd_len
    }



def debug_partitioning(V, C, num_rows, num_tiles):
    """Debug helper to visualize V and C partitioning"""
    print(f"\nV Partitioning (V={V}, num_rows={num_rows}):")
    total_v = 0
    for r in range(num_rows):
        v_start, v_count = get_v_partition(r, V, num_rows)
        if v_count > 0:
            print(f"  Row {r:2d}: V[{v_start:3d}:{v_start+v_count:3d}] (count={v_count})")
            total_v += v_count
    print(f"  Total V covered: {total_v} (expected: {V})")

    print(f"\nC Partitioning (C={C}, num_tiles={num_tiles}):")
    total_c = 0
    for t in range(num_tiles):
        c_start, c_count = get_c_partition(t, C, num_tiles)
        if c_count > 0:
            print(f"  Tile {t:2d}: C[{c_start:3d}:{c_start+c_count:3d}] (count={c_count})")
            total_c += c_count
    print(f"  Total C covered: {total_c} (expected: {C})")


def verify_per_row_memblk():
    """
    Test with per-row memblks (pre-partitioned data).
    
    This test uses the hex/B4_C4_V32/ folder which contains:
    - 16 pairs of left_r.hex and right_r.hex (one per row)
    - 16 golden files golden_B4_C4_V32_r.hex (partial results per row)
    
    Test Configuration:
    - B=4 (batches), C=4 (columns), V=32 per row
    - Total V across all rows = 32 * 16 = 512
    - Each row's memblk contains pre-partitioned data (only its V slice)
    
    Verification:
    1. Each row's partial result vs golden_B4_C4_V32_r.hex
    2. Final sum vs sum of all golden files
    """
    hex_path = '/home/dev/Dev/elastix_gemm/hex/B4_C4_V32'
    B, C, V_per_row = 4, 4, 32
    num_rows = 16
    num_cols = 8
    total_V = V_per_row * num_rows  # 512
    
    print("=" * 70)
    print("Per-Row Memblk Verification (Pre-Partitioned Data)")
    print("=" * 70)
    print(f"Configuration: B={B}, C={C}, V_per_row={V_per_row}, total_V={total_V}")
    
    engine = GEMM(num_rows=num_rows, num_cols=num_cols)
    
    # =========================================================================
    # Load per-row data (pre-partitioned)
    # =========================================================================
    print("\nLoading per-row memblks...")
    for r in range(num_rows):
        # Load right (weights) for this row
        right_memblk = MemBlk(num_lines=528, line_size=32)
        right_memblk.from_hex(f'{hex_path}/right_{r}.hex')
        engine.load_row_memblk(r, right_memblk.data)
    
    # =========================================================================
    # FETCH and DISPATCH right (weights)
    # =========================================================================
    # Command specifies total_V = 512, which gets partitioned to 32 per row
    cmd = cmd_fetch(cmd_id=0, start_addr=0, ugd_len=total_V, len=528, fetch_right=1)
    engine.run(cmd)
    cmd = cmd_dispatch(cmd_id=0, nv_cnt=C, ugd_len=total_V, tile_addr=0, col_start=0, disp_right=1, broadcast=0, man_4b=0)
    engine.run(cmd)
    
    # =========================================================================
    # Load left (activations) for each row
    # =========================================================================
    for r in range(num_rows):
        left_memblk = MemBlk(num_lines=528, line_size=32)
        left_memblk.from_hex(f'{hex_path}/left_{r}.hex')
        engine.load_row_memblk(r, left_memblk.data)
    
    # =========================================================================
    # FETCH and DISPATCH left (activations)
    # =========================================================================
    cmd = cmd_fetch(cmd_id=0, start_addr=0, ugd_len=total_V, len=528, fetch_right=0)
    engine.run(cmd)
    cmd = cmd_dispatch(cmd_id=0, nv_cnt=B, ugd_len=total_V, tile_addr=0, col_start=0, disp_right=0, broadcast=1, man_4b=0)
    engine.run(cmd)
    
    # =========================================================================
    # MATMUL: Compute with V_per_row for each row
    # =========================================================================
    cmd = cmd_matmul(cmd_id=0, left_addr=0, right_addr=0, left_len=B, right_len=C, 
                     ugd_len=total_V, left_4b=0, right_4b=0, main_loop_left=1)
    engine.run(cmd)
    
    # =========================================================================
    # Verify partial results BEFORE reduction
    # =========================================================================
    print("\n--- Verifying Per-Row Partial Results ---")
    all_passed = True
    all_golden_partials = []
    
    # Create a cmd dict for get_row_partial_results
    partial_cmd = {'left_len': B, 'right_len': C}
    
    for r in range(num_rows):
        # Get this row's partial results
        partial_results = engine.get_row_partial_results(r, partial_cmd)
        
        # Load golden for this row
        golden_file = f'{hex_path}/golden_B4_C4_V32_{r}.hex'
        with open(golden_file, 'r') as f:
            hex_lines = [line.strip() for line in f if line.strip()]
        golden_uint16 = np.array([int(h, 16) for h in hex_lines], dtype=np.uint16)
        golden_partial = golden_uint16.view(np.float16).tolist()
        all_golden_partials.append(golden_partial)
        
        # Compare with relaxed tolerance for partial results
        # V=32 per row leads to more accumulation and higher precision variation
        # compared to smaller V tests. rtol=3% is appropriate for GFP8 precision.
        row_passed = True
        for i in range(len(partial_results)):
            if not np.allclose(partial_results[i], golden_partial[i], rtol=3e-2, atol=1e-5):
                if row_passed:  # Only print first mismatch per row
                    print(f"  Row {r}: MISMATCH at index {i}: got {partial_results[i]}, expected {golden_partial[i]}")
                row_passed = False
                all_passed = False
        
        if row_passed:
            print(f"  Row {r:2d}: PASSED (partial results match golden)")
    
    # =========================================================================
    # READOUT: Reduce and verify final sum
    # =========================================================================
    print("\n--- Verifying Final Sum ---")
    cmd = cmd_readout(cmd_id=0, left_len=B, right_len=C, ugd_len=total_V)
    engine.run(cmd)
    
    # Compute expected final sum from all golden partials
    expected_len = B * C
    golden_sum = [0.0] * expected_len
    for r in range(num_rows):
        for i in range(expected_len):
            golden_sum[i] += all_golden_partials[r][i]
    
    # Compare final results
    # Final sum accumulates 16 rows × 32 V per row = 512 operations.
    # For small values, absolute errors from accumulation can dominate relative errors.
    # Use larger atol (0.001) to handle cases where many small differences accumulate.
    assert len(engine.results) == expected_len, f"Results length {len(engine.results)} should be {expected_len}"
    final_passed = True
    for i in range(expected_len):
        if not np.allclose(engine.results[i], golden_sum[i], rtol=5e-2, atol=1e-3):
            print(f"  MISMATCH at index {i}: got {engine.results[i]}, expected {golden_sum[i]}")
            final_passed = False
            all_passed = False
    
    if final_passed:
        print(f"  PASSED: Final sum of all {num_rows} rows matches!")
    
    return all_passed


if __name__ == "__main__":
    # Run per-row memblk verification (canonical mode)
    print("Running per-row memblk test...")
    verify_per_row_memblk()

    # Optionally debug partitioning
    # debug_partitioning(V=29, C=31, num_rows=16, num_tiles=16)
