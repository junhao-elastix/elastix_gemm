# GFP Conversion Modules Reference

## 1. gfp_norm - Group Floating Point Normalizer

### Purpose
Normalizes floating-point elements within a group to share a common (maximum) exponent, enabling GFP representation.

### Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| `MAN_WIDTH` | 11 | Mantissa width |
| `EXP_WIDTH` | 5 | Exponent width |
| `IN_ELEMENTS` | 16 | Elements per word |
| `GROUP_WORDS` | 2 | Words per group (determines normalization scope) |

### Interfaces

**Inputs:**
| Signal | Width | Description |
|--------|-------|-------------|
| `i_data_in_val` | 1 | Input data valid |
| `i_data_in` | `IN_ELEMENTS × (EXP+MAN)` | Input FP elements |
| `i_data_in_pad` | `log2(IN_ELEMENTS+1)` | Number of padding elements |
| `i_data_in_last` | 1 | Last word in stream |
| `i_data_out_ack` | 1 | Downstream ready |

**Outputs:**
| Signal | Width | Description |
|--------|-------|-------------|
| `o_data_in_ack` | 1 | Ready to accept input |
| `o_data_out_val` | 1 | Output valid |
| `o_data_out` | `IN_ELEMENTS × (EXP+MAN)` | Normalized elements |
| `o_data_out_last` | 1 | Last word marker |
| `o_data_out_pad` | `log2(IN_ELEMENTS+1)` | Padding count |

### Calculation
1. **Max Exponent Detection**: For each incoming word, find `max_exp` across all valid elements
2. **Group Accumulation**: Track `data_max_exp = max(data_max_exp, word_max_exp)` across `GROUP_WORDS`
3. **Mantissa Shift**: For each element:
   - If `elem.exp == group_max_exp`: no shift
   - Else: `norm_man = elem.man >> (group_max_exp - elem.exp)`

---

## 2. gfp_up_align - Element Count Alignment

### Purpose
Converts streams with `IN_ELEMENTS` per word to `OUT_ELEMENTS` per word using a double-buffer scheme.

### Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| `DATA_WIDTH` | 16 | Width per element |
| `IN_ELEMENTS` | 14 | Input elements per word |
| `OUT_ELEMENTS` | 16 | Output elements per word |

### Interfaces

**Inputs:**
| Signal | Width | Description |
|--------|-------|-------------|
| `i_data_val` | 1 | Input valid |
| `i_data` | `IN_ELEMENTS × DATA_WIDTH` | Input elements |
| `i_data_pad` | `log2(IN_ELEMENTS+1)` | Valid element count |
| `i_data_last` | 1 | Last word in stream |

**Outputs:**
| Signal | Width | Description |
|--------|-------|-------------|
| `o_data_ack` | 1 | Upstream acknowledgment |
| `o_data_val` | 1 | Output valid |
| `o_data` | `OUT_ELEMENTS × DATA_WIDTH` | Aligned output |
| `o_data_last` | 1 | Last word marker |
| `o_data_pad` | `log2(OUT_ELEMENTS+1)` | Padding count |

### Calculation
1. **Double Buffer**: Maintains `2 × OUT_ELEMENTS` buffer
2. **Write**: Append `IN_ELEMENTS - i_data_pad` valid elements at `buff_wr_ptr`
3. **Read**: When bottom half full (`buff_wr_ptr >= OUT_ELEMENTS`), output bottom; when top half full, output top
4. **Flush**: On `last_flag`, output remaining elements with calculated padding

---

## 3. virtual_queue - Dynamic Block-Based Queue Manager

### Purpose
Manages multiple virtual queues over shared memory using linked-list block allocation.

### Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| `DATA_WIDTH` | 16×14 | Data word width |
| `MEM_DEPTH` | 1024×16 | Total memory entries |
| `BLOCK_SIZE` | 32 | Entries per block |
| `MAX_QUEUE_CNT` | 64 | Number of virtual queues |

### Interfaces

**Write Interface:**
| Signal | Width | Description |
|--------|-------|-------------|
| `i_wr_en` | 1 | Write enable |
| `i_wr_queue_id` | `log2(MAX_QUEUE_CNT+1)` | Target queue ID |
| `i_wr_data` | `DATA_WIDTH` | Write data |
| `o_wr_af` | 1 | Almost full |

**Read Command Interface:**
| Signal | Width | Description |
|--------|-------|-------------|
| `i_cmd_val` | 1 | Command valid |
| `i_cmd` | `queue_read_cmd_t` | Read command (queue_id, length) |
| `o_cmd_ack` | 1 | Command acknowledged |

**Read Data Interface:**
| Signal | Width | Description |
|--------|-------|-------------|
| `i_rd_ack` | 1 | Read acknowledge |
| `o_rd_data` | `DATA_WIDTH` | Read data |
| `o_rd_empty` | 1 | Egress queue empty |

### Architecture
```
                    ┌─────────────────────────────────────┐
   i_wr_data ──────►│  Ingress FIFO                       │
   i_wr_queue_id ──►│  (queue_id, data)                   │
                    └────────────┬────────────────────────┘
                                 │
                                 ▼
                    ┌─────────────────────────────────────┐
                    │  Main Memory (MEM_DEPTH entries)    │
                    │  Organized as NUM_BLOCKS blocks     │
                    └────────────┬────────────────────────┘
                                 │
                                 ▼
                    ┌─────────────────────────────────────┐
   o_rd_data ◄──────│  Egress FIFO                        │
                    └─────────────────────────────────────┘
```

### Data Structures
- **queue_write_desc_mem[queue_id]**: `{block_id, offset}` - Current write position per queue
- **queue_read_desc_mem[queue_id]**: `{block_id, offset}` - Current read position per queue
- **block_next_ptr_mem[block_id]**: `{next_block_id}` - Linked list next pointer
- **free_block_q**: FIFO of available block IDs

### Operation
1. **Initialization**:
   - Free block queue populated with blocks `[MAX_QUEUE_CNT, NUM_BLOCKS-1]`
   - Each queue gets initial block `queue_id` with offset 0

2. **Write**:
   - Look up `queue_write_desc_mem[queue_id]` for current `{block_id, offset}`
   - Write to `mem[block_id × BLOCK_SIZE + offset]`
   - If `offset == BLOCK_SIZE-1`: allocate new block from free queue, update `block_next_ptr_mem`

3. **Read**:
   - Accept command `{queue_id, length}`
   - Read `length` entries starting from `queue_read_desc_mem[queue_id]`
   - When block exhausted: follow `block_next_ptr_mem`, release old block to free queue
