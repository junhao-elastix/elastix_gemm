# MLP Column Data Distribution Reference

**Scope**: Data flow strategy from row_bram to MLP columns during compute phase

---

## Architecture

- **8 MLP primitives** × 2 columns each = **16 logical columns**
- Each MLP handles two adjacent columns (e.g., MLP 0 handles columns 0 and 1)

---

## Two-Phase Operation

### Phase 1: Weight Fill (ST_FILL)

**Strategy**: Load weights into MLP internal BRAMs before compute begins.

**Loading Order**: Column-major
- Load all V NVs for column 0
- Then all V NVs for column 1
- Continue through column 15

**Mapping**: Column c → MLP[c/2], internal bank[c%2]

### Phase 2: Compute (ST_COMPUTE)

**Strategy**: Stream activations to all MLPs while they read stored weights.

**Data Flow**:
- Activations broadcast to all 8 MLPs simultaneously
- Each MLP computes dot products using its stored weights
- 16 results produced per batch (one per column)

**Control Signals**:
- `new_dot`: Reset accumulator at start of each batch
- `last_nv`: Trigger output after final NV of batch

---

## Column Group Processing (C > 16)

For matrices with more than 16 columns, process in sequential groups.

**Strategy**: Iterate FILL → COMPUTE for each group of 16 columns

| C | Groups | Processing |
|---|--------|------------|
| 16 | 1 | FILL → COMPUTE → DONE |
| 32 | 2 | FILL(0-15) → COMPUTE → FILL(16-31) → COMPUTE → DONE |
| 64 | 4 | 4 iterations of FILL → COMPUTE |

**Memory Layout**: Weights stored contiguously in row_bram, partitioned by column group.

---

## Output

- **Per batch**: 16 FP16 results (256 bits)
- **Per MATMUL**: B × C total FP16 results

---

## Design Rationale

1. **Column-major weight loading**: Minimizes MLP BRAM address switching during fill
2. **Activation broadcast**: Same data to all MLPs enables SIMD-style parallelism
3. **Sequential column groups**: Allows arbitrary C dimension with fixed 16-column hardware
4. **4-stack parallelism**: 4× throughput vs single-stack design (4 cycles per NV)
