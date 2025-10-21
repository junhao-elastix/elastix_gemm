# How to decode the HEX files
## File format
The Hex files, `left.hex` and `right.hex` represents two memory blocks (BLK) that contains matrix information. We call them Matrix A and Matrix B. Each line is 256 bits. The numbers are stored in Group Floating Point (GFP) format. 

Comman parameters:

Grouped Dimenion (GD): Along which dimension are the numbers grouped. In Matrix A (Activation) numbers are grouped along the rows; in Matrix B, Activation numbers are grouped along cols. 

Ungrouped Dimension (UGD): Along which dimension are the numbers NOT grouped. 

Group size (GS): How many numbers are grouped together in GFP format. Default is 32

Native Vector (NV): How many numbers are multiplied together, atomically, in one dot-product tile. Default size is 128. 

Block size (BS): the size of Native Vectors in one memory block. Default is 128. 

### Exponent
The first 16 lines pack 512 exponents. The exponents can be either 5-bit or 8-bit, but they are always byte-aligned. 8-bit will fit perfectly. We need to pad the 3 MSB for the 5-bit exponents to align them to 8-bit.

Currently, assume 5-bit exponent.
 
Since each line is 256 bits, it can pack 32 8-bit numbers: 

| Line # | [255:248] | [247:240] | [239:232] | ... |    [15:8] |     [7:0] |
|--------|-----------|-----------|-----------|-----|-----------|-----------|
| 0      | Exp 31    | Exp 30    | Exp 29    | ... | Exp 1     | Exp 0     |
| 1      | Exp 63    | Exp 62    | Exp 61    | ... | Exp 33    | Exp 32    |
| ...    | ... ||||||
| 15     | Exp 511   | Exp 510   | Exp 509   | ... | Exp 481   | Exp 480   |

Because there are 128 NV in one BLK, and each NV has 4 groups (4 x 32 = 128), there are 512 exponents in the first 16 lines. 

**Important**: Each group of 32 numbers shares 1 exponent. This is why there are exactly 512 exponents (128 NVs × 4 groups per NV = 512 groups, each with 1 shared exponent).

### Mantissa
The remaining 512 lines in a BLK are all mantissas. Each 8 bit alignement represents one mantissa. Each memory line is 256 bits, so it packs 32 mantissas. One NV needs four lines to represent. 512 lines contain 128 NVs. 

Table is omitted. 

## Accee pattern.
Notice the memory layout is a flattene 1-D array of 128 NVs. Reverting back to the original matrix is controled at runtime by the host.

We have four parameter:

Number of NVs (V): How many NVs in the inner dimension.
Number of Columns (C): how many columns in the output.
Number of Bathces (B): how many rows in the output. 
Number of Results (N): how many result blocks. Forced to 1 for now. 

**Matrix Dimensions**: The actual matrix dimensions are configurable via B, C, and V parameters:
- **Matrix A**: B × (128 × V) - Activation matrix
- **Matrix B**: (128 × V) × C - Weight matrix (stored transposed)
- **Result**: B × C - Output matrix

**Important**: Matrix B is stored transposed, meaning that the first line of mantissas for both A and B represents one group of 32 8-bit numbers. For Matrix A, this group is along the row; for Matrix B, this group is along the column.

**Access Pattern**: Both Matrix A and Matrix B are always read horizontally, line-by-line. This is designed to benefit the matrix multiplication process: each aligned byte of Matrix A and Matrix B will be multiplied together in hardware.

In a matrix multiplication, if we describe this operation in C-style pseudo code:
```c++
int result_matrix[N][B][C];
for (int n = 0; n < N; n ++) { // Forced to 1
    for (int b = 0; b < B; b ++) {
        for (int c = 0; c < C; c ++) {
            int acc = 0;
            for (int v = 0; v < V; v ++){
                for (int i = 0; i < NV; i ++){ // Forced to 128
                    acc += Matrix_A[n*b*v*NV + i] * Matrix_B[n*c*v*NV + i];
                }
            }
            result_matrix[n][b][c] = acc;
        }
    }
}
```
Therefore, notice that the access pattern for Matrix A and Matrix B are affected by N, B, C, and V. V has to be the same for both because it is the inner dimension. For now, you can assume N is always 1. B and C are configurable. Therefore, when reading Matrix A, you will read B times V number of NVs, and for Matrix B, you will read C times V number of NVs. Apparently, the result will have the dimension B x C. 

## Implementation Notes

**Last Updated**: Sat Oct 4 06:40:18 PM PDT 2025

### GFP Format Details
- **Group Structure**: Each group of 32 numbers shares 1 exponent
- **Exponent Count**: 512 exponents total (128 NVs × 4 groups per NV)
- **Exponent Storage**: 16 lines × 32 exponents per line = 512 exponents
- **Mantissa Storage**: 512 lines × 32 mantissas per line = 16,384 mantissas

### Data Format Specifications

#### Mantissa Format (8-bit)
- **Encoding**: 2's complement signed integer
- **Range**: [-128, 127] (note: hardware uses [-128, 127], not [-127, 127])
- **Bit Width**: 8 bits
- **Storage**: One byte per mantissa, packed 32 per line

#### Exponent Format (5-bit, padded to 8-bit)
- **Encoding**: Unsigned integer, padded to byte alignment
- **Range**: [0, 31] (5-bit values)
- **Bias**: 15 (calculated as 2^(5-1) - 1)
- **Padding**: Upper 3 bits are don't-care, mask with 0x1F to extract
- **Storage**: One byte per exponent, but only lower 5 bits are significant

#### GFP to Float Conversion Formula
```
float_value = mantissa × 2^(exponent - bias)
```
- Special case: If exponent == 0, treat as zero value
- Bias = 15 for 5-bit exponents
- Example: mantissa=100, exponent=10 → 100 × 2^(10-15) = 100 × 2^-5 = 3.125

### Byte Ordering (Critical Implementation Detail)

**Hex File Display Format**:
- Lines show bytes from **left to right** as: `[byte_31] [byte_30] ... [byte_1] [byte_0]`
- Display order: MSB (Most Significant Byte) on left → LSB (Least Significant Byte) on right
- Example line: `0a 0a 09 09 ... 0a 0a` (byte 31 is leftmost, byte 0 is rightmost)

**Element Indexing**:
- Element[0] corresponds to **byte_0** (rightmost in display)
- Element[31] corresponds to **byte_31** (leftmost in display)
- **Implementation**: Must reverse byte order when parsing hex lines to match element indexing

### Matrix Dimensions and V Parameter

The V parameter expands the **inner dimension** (the reduction dimension in GEMM):

- **Matrix A dimensions**: B rows × (128×V) columns
  - Each row is formed by concatenating V consecutive Native Vectors
  - Physical layout: Uses B×V Native Vectors from storage
  
- **Matrix B dimensions**: (128×V) rows × C columns (stored transposed)
  - Each column (after transpose) is formed by V consecutive Native Vectors
  - Physical layout: Uses C×V Native Vectors from storage
  
- **Result dimensions**: B rows × C columns

**Memory Access Pattern**:
- Matrix A row b uses Native Vectors: [b×V, b×V+1, ..., b×V+V-1]
- Matrix B column c uses Native Vectors: [c×V, c×V+1, ..., c×V+V-1]
- Both matrices read horizontally (line-by-line) from physical storage
- Total NVs used: B×V (for A) + C×V (for B) must be ≤ 128

### Matrix Access Pattern
- **Reading Method**: Always horizontal, line-by-line for both matrices
- **Hardware Benefit**: Aligned byte multiplication for efficiency
- **Transpose Handling**: Matrix B transpose is handled by data organization, not access pattern
- **Memory Layout**: Flattened 1-D array of 128 NVs, configurable dimensions at runtime

### Exponent-Mantissa Mapping

The mapping between exponents and mantissas is **1:1 by line number**:

- **Mantissa line N** (lines 16-527, 0-indexed) uses **exponent index N** (from flattened exponent array)
- **Exponent array**: 512 exponents flattened from 16 lines × 32 bytes
- **Exponent layout**: Reshape flattened array to [128 NVs, 4 groups per NV]
- **Column grouping**: For each row, columns are divided into 4 groups of 32 elements each
  - Group 0: columns [0:31], Group 1: columns [32:63], Group 2: columns [64:95], Group 3: columns [96:127]

### Verification and Test Results

**Test Session**: Sat Oct 4 06:40:18 PM PDT 2025

Comprehensive testing with various B, C, V combinations confirms correct implementation:

| B | C | V | Matrix A | Matrix B | Result | Max Rel Error | Status |
|---|---|---|----------|----------|--------|---------------|--------|
| 1 | 1 | 1 | 1×128 | 128×1 | 1×1 | 0.000% | ✓ PASS |
| 4 | 1 | 32 | 4×4096 | 4096×1 | 4×1 | 0.313% | ✓ PASS |
| 8 | 1 | 8 | 8×1024 | 1024×1 | 8×1 | 0.035% | ✓ PASS |
| 3 | 5 | 4 | 3×512 | 512×5 | 3×5 | 0.557% | ✓ PASS |

**Accuracy**: GFP GEMM results match floating-point reference within < 1% relative error for most cases, with errors primarily due to quantization (8-bit mantissa precision loss).

**Key Validated Features**:
- ✓ Byte order reversal (LSB→MSB element indexing)
- ✓ 2's complement mantissa decoding  
- ✓ 5-bit exponent masking and bias handling
- ✓ GFP to float conversion formula
- ✓ Matrix B transpose handling
- ✓ Variable B, C, V parameter dimensions
- ✓ Native Vector concatenation for V > 1