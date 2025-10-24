# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Python emulator for Group Floating Point (GFP) operations on FPGA. The project simulates FPGA-based matrix multiplication accelerators that use a custom floating-point format optimized for hardware implementation. It includes both the core GFP data type and tensor operations, as well as hardware emulation for GEMM arrays and external memory systems.

## Build and Development Commands

### Setup and Installation
```bash
# Install dependencies (requires Python 3.12+)
pip install -e .

# Install development dependencies
pip install -e .[dev]
```

### Testing
```bash
# Run all tests
pytest

# Run specific test file
python src/emulator/main_test.py
python src/emulator/test_palettized_gfp_tensor.py

# Run main demo
python src/emulator/main.py

# Run GFP memory layout analysis (new)
python dot_product_example.py
python inspect_memory_layout.py
```

### Code Quality
```bash
# Format code
black src/
isort src/

# Type checking
mypy src/

# Linting
ruff check src/

# Test coverage
coverage run -m pytest
coverage report
```

## Architecture Overview

### Core Components

**Group Floating Point (GFP) System** (`group_floating_point.py`):
- `GFPDataType`: Defines custom floating-point format with configurable mantissa/exponent bits
- `GFPTensor`: Grouped floating-point tensor with shared exponents per group
- `GFPGemm`: Matrix multiplication operation for GFP tensors
- `GFPElmwiseAdd`: Element-wise addition for GFP tensors
- `GFPGemmTiled`: Tiled GEMM implementation for memory-efficient computation

**Hardware Emulation** (`api.py`):
- `GemmTile`: Single processing tile with local memory (left/right operands)
- `GemmArray`: Array of tiles forming a systolic-like compute fabric
- `ExternalMem`: External memory system with blocking and addressing
- `GemmTileConfig`: Configuration for tile parameters (group size, memory depth, etc.)

**Palettized Tensors** (`palettized_gfp_tensor.py`):
- `PalettizedGFPTensor`: Memory-efficient GFP representation using palette indices
- Reduces storage by sharing common mantissa values across tensor elements

### Key Design Patterns

**Quantization Pipeline**:
1. Float tensors → GFP tensors (quantization with shared group exponents)
2. GFP tensors → Hardware memory layout (blocking, distribution across tiles)
3. GEMM computation → GFP result tensors
4. GFP tensors → Float tensors (dequantization)

**Memory Hierarchy**:
- External memory (`ExternalMem`) simulates off-chip storage with channels and blocking
- Tile memory provides on-chip buffers for operands
- Data movement between memory levels via descriptors and fetching operations

**Tiling Strategy**:
- Matrices divided into tiles that fit in hardware buffers
- Nested loops handle batch, column, and row dimensions
- Accumulation across tiles for final results

## Development Notes

### GFP Format Details
- Mantissa can be signed or unsigned (with separate sign bit)
- Exponents shared per group reduce storage overhead
- Configurable bias and bit widths for different precision/range trade-offs
- Hardware-friendly operations (shifts, adds, limited multiplies)

### Hardware Simulation Accuracy
- Emulates FPGA constraints: limited memory depths, fixed tile sizes
- Models data movement costs and memory access patterns
- Simulates multi-tile coordination and result collection

### Test Organization
- `main_test.py`: Core GFP operations and accuracy validation
- `test_palettized_gfp_tensor.py`: Palettized tensor functionality
- `main.py`: Full GEMM pipeline demonstration
- `l31_8b_attn.py`: LLaMA attention layer simulation

### Memory Layout Analysis Tools

**`calculate_external_memory_layout.py`**: External memory layout calculator
- **Main function**: `calculate_memory_layout(tensor_rows, tensor_cols)`
- **Interactive calculator**: Computes memory requirements for any tensor dimensions
- **Block organization analysis**: Shows exact memory layout following ExternalMem format
- **Compression analysis**: Compares GFP storage vs FP32 baseline
- **Hardware addressing**: Provides memory entry ranges and block boundaries
- **Configuration**: Fixed for 32-element groups, 128-element native vectors, 128 native vectors per block
- **Example usage**:
```python
# Default examples with detailed analysis
python calculate_external_memory_layout.py

# For interactive mode, uncomment main() call in script
layout = calculate_memory_layout(4096, 4096)  # 1,024 blocks, 16.5 MB, 3.9× compression
```

**`external_memory_demo.py`**: ExternalMem class demonstration with real hardware simulation
- **Main function**: `demonstrate_external_memory()`
- **Real hardware simulation**: Uses actual ExternalMem and GemmTileConfig classes from api.py
- **Multi-channel memory**: Demonstrates distribution across 8 memory channels
- **Block-based storage**: Shows exponent/mantissa separation with burst alignment
- **Data integrity verification**: Validates quantization accuracy with RMSE analysis
- **Seed 42 reproducibility**: All random data generated with fixed seed for consistency
- **Multiple tensor sizes**: Tests small (128×256), medium (512×512), and large (1024×2048) tensors
- **Example usage**:
```python
# Complete ExternalMem demonstration with hardware constraints
python external_memory_demo.py
```

**`dot_product_example.py`**: Simple GFP dot product demonstration
- Creates two 128-element vectors with 8-bit mantissa/exponent
- Demonstrates quantization, GEMM operation, and accuracy analysis
- Tests different group sizes and their precision trade-offs
- Example usage:
```python
# Default: 128 elements, 8m/8e, group_size=32
python dot_product_example.py
```

**`inspect_memory_layout.py`**: Comprehensive GFP memory layout analyzer
- **Main function**: `main(vector_length=128, mantissa_bits=8, exp_bits=8, group_size=8)`
- **Complete bit-level analysis**: Shows exact FPGA memory representation
- **Hardware memory mapping**: Demonstrates actual memory addresses and layouts
- **Configurable parameters**: Experiment with different GFP configurations
- **Three analysis modes**:
  1. `inspect_gfp_memory_layout()`: Detailed memory structure and bit patterns
  2. `inspect_dot_product_memory()`: GEMM operation analysis with memory layouts
  3. `show_hardware_memory_format()`: FPGA-ready memory organization

**Key Features**:
- Shows all 16 groups with complete bit-level representation
- Demonstrates compression ratios (3.6× for 8m/8e/g8, 4.3× for 6m/6e/g4)
- Validates quantization accuracy (RMSE typically < 0.05)
- Provides FPGA memory addresses and burst access patterns
- Example usage:
```python
# Run with default parameters
python inspect_memory_layout.py

# Custom configuration in code
main(vector_length=64, mantissa_bits=6, exp_bits=6, group_size=4)
```

**Output Analysis**:
- **Memory Layout**: Mantissa/exponent data organization by groups
- **Bit-Level Representation**: Exact binary patterns for FPGA implementation
- **Reconstruction Accuracy**: Original vs reconstructed values with error analysis
- **Hardware Format**: Memory word layouts with addresses for FPGA design
- **Compression Analysis**: Storage efficiency compared to IEEE FP32

Use these tools to:
- Understand GFP memory organization before RTL implementation
- Validate precision/compression trade-offs for specific applications
- Generate FPGA memory interface specifications
- Debug quantization accuracy and hardware constraints

## ExternalMem Block Organization

The `ExternalMem` class in `api.py` implements a blocked memory layout optimized for FPGA burst access patterns. Understanding this organization is crucial for RTL implementation.

### Configuration Example
```python
# Typical configuration for large tensors
gfp_group_size = 32           # Elements per group
native_vector_size = 128      # Elements per native vector (4 groups)
block_size = 128              # Native vectors per block
mantissa_bits = 8             # Mantissa width
exponent_bits = 8             # Exponent width
channel_bytes = 32            # Memory burst alignment
```

### Block Memory Layout
Each block in external memory is organized as:
```
Block Structure (528 memory entries × 32 bytes = 16,896 bytes):
┌─────────────────────────────────────────────────────────────┐
│ EXPONENT SECTION (entries 0-15)                            │
│   - 128 native vectors × 4 exponents = 512 bytes           │
│   - Padded to 16 entries (512 ÷ 32 = 16)                   │
│   - block_mantissa_offset = 16                             │
├─────────────────────────────────────────────────────────────┤
│ MANTISSA SECTION (entries 16-527)                          │
│   - 128 native vectors × 128 bytes = 16,384 bytes          │
│   - Stored as 512 entries (16,384 ÷ 32 = 512)              │
│   - Total block_depth = 16 + 512 = 528 entries             │
└─────────────────────────────────────────────────────────────┘
```

### Memory Addressing
```python
# Block addressing scheme (from write_tensor method)
block_start_addr = target_address + (block_id × block_depth)
block_end_addr = block_start_addr + block_depth - 1

# For 4096×4096 tensor: 128k native vectors = 1k blocks
total_blocks = 1024
total_memory_entries = 1024 × 528 = 540,672 entries
```

### Hardware Benefits
- **Separate Access**: Exponents and mantissas can be accessed independently
- **Burst Efficiency**: All data aligned to 32-byte boundaries for optimal memory bandwidth
- **Parallel Processing**: Exponent alignment and mantissa arithmetic can overlap
- **Scalable**: Block size configurable based on on-chip buffer sizes

### Implementation Notes
- Exponents stored first for priority access during alignment operations
- Mantissa data follows immediately for sequential burst reads
- Padding ensures all memory accesses are burst-aligned
- Block descriptor (`ExtMemTensorDescriptor`) tracks all layout parameters

This blocked organization enables efficient FPGA implementations where memory controllers can prefetch entire blocks while processing units work on previously loaded data.

Use this emulator to prototype FPGA implementations, validate GFP algorithms, and analyze hardware trade-offs before RTL development.