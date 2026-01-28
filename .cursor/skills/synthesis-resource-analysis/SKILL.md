---
name: synthesis-resource-analysis
description: Analyzes FPGA synthesis resource utilization (LRAM, BRAM, LUT4/LUT6) from Achronix ACE hierarchical area CSV and resourceusage.rpt. Maps report modules to RTL sources and documents in syn_area.md. Use after synthesis is done, when the user asks to analyze resource utilization, LRAM, BRAM, or LUT usage, or to create/update syn_area.md from synthesis reports.
---

# Synthesis Resource Utilization Analysis

Performs the same analysis done for elastix_gemm_top: top-level summary, per-resource (LRAM, BRAM, LUT) top consumers, RTL mapping, hierarchy cross-check, and documentation in `syn_area.md`.

---

## 1. Locate Report Files

After ACE/ACX synthesis, reports are under:

- **Hierarchical area CSV:**  
  `{build_dir}/results/ace/impl_1/syn/rev_acx/synlog/report/{top_name}_impl_1_fpga_mapper_hier_area.csv`
- **Resource usage (top-level):**  
  `{build_dir}/results/ace/impl_1/syn/rev_acx/synlog/report/{top_name}_impl_1_fpga_mapper_resourceusage.rpt`

`{build_dir}` is usually `gemm/build` or project `build/`; `{top_name}` is the top RTL module (e.g. `elastix_gemm_top`).

**CSV columns:** Module name, LUT4, LUT6, DFF, ALU8, BRAM, LRAM, MLP, PADS. Rows may have a leading `.` and tabs for hierarchy depth.

---

## 2. Top-Level Resource Summary

Read `*_resourceusage.rpt`. Extract:

- **Cell usage:** LUT4, LUT6, DFF, ALU8, BRAM (e.g. BRAM72K_SDP, ACX_BRAM72K_SDP), LRAM (LRAM2K_SDP), MLP/DSP.
- **RAM/ROM summary:** Total BRAM, Total LRAM (main + blackbox).
- **DSP summary:** Total DSP.
- **Mapping Summary:** Total LUT (LUT4+LUT6; may include blackbox LUT).

Build a table:

| Resource | Used | Available | Util % |
|----------|------|------------|--------|
| LUT (LUT4+LUT6) | (from rpt) | 691,200 | % |
| LUT4 | ... | - | - |
| LUT6 | ... | - | - |
| DFF | ... | 1,382,400 | % |
| ALU8 | ... | 172,800 | % |
| BRAM | ... | 2,560 | % |
| LRAM | ... | 2,560 | % |
| MLP (DSP) | ... | 2,560 | % |

Note: `Available` is for AC7t1500; adjust if targeting another part.

---

## 3. LRAM Analysis

### 3.1 Top LRAM Consumers (from CSV)

1. Parse the hierarchical CSV; sort or filter by LRAM (column index 6) descending.
2. Build a table: Report module | LRAM | RTL source.
3. For each significant row, identify the RTL module name (strip parameter suffixes like `_16s_64s_0` to get `flex_fifo`, `comp_row_bram`, etc.). Note replication (e.g. `x16`).

### 3.2 RTL Locations for LRAM

In `src/rtl/` (or project RTL root), find arrays that map to LRAM:

- **Attributions:** `(* ram_style="block" *)` on `mem` or register arrays.
- **Small/medium arrays:** FIFO `mem[0:DEPTH-1]`, `ar_fifo`, `exp_bram`, and similar. LRAM is used when depth/width fits LRAM2K; larger arrays go to BRAM.
- **Inferred:** Arrays without `ram_style` may still map to LRAM; check hierarchy to see which report block contains them.

Build a table:

| File | Line(s) | Array / logic | Size | LRAM/inst |
|------|---------|---------------|------|------------|
| **flex_fifo.sv** | N | `mem[0:DEPTH-1]` (ram_style=block) | Wb x D | 1 |
| ... | ... | ... | ... | ... |

Add a note when a large FIFO in the same RTL is implemented as BRAM, not LRAM (e.g. 256x1024 flex_fifo).

### 3.3 LRAM Hierarchy Check

For key parent blocks (e.g. `engine_top_2d`, `compute_engine_2d`, `dispatcher_control_2d`):

- Parent LRAM = sum of relevant children.
- Leaf sum: add distinct leaf contributions (e.g. 256x flex_fifo + 16x8 comp_row_bram + 16x2 dispatcher_2d + 16x1 fetcher + 1 cmd_fifo) and compare to parent/top. Note encrypted/IP blocks (e.g. acx_device_manager) and any remainder (probe/snapshot, etc.).

---

## 4. BRAM Analysis

### 4.1 Top BRAM Consumers (from CSV)

1. From the CSV, filter/sort by BRAM (column index 5).
2. Table: Report module | BRAM | RTL source.

### 4.2 RTL Locations for BRAM

In RTL, look for:

- **Instantiated BRAM:** `ACX_BRAM72K*`, `BRAM72K*`, or similar macros.
- **Inferred RAM:** Larger `mem` or register arrays, `ram_style="block"` or `"auto"` on wide/deep structures; 256x1024 FIFOs, row/col BRAMs.
- **resourceusage.rpt:** Lists `BRAM72K_SDP`, `ACX_BRAM72K_SDP`, etc. Use that to confirm what is BRAM vs LRAM.

| File | Line(s) | Array / logic | Size / role | BRAM/inst |
|------|---------|---------------|-------------|------------|
| ... | ... | ... | ... | ... |

### 4.3 BRAM Hierarchy Check

Same as LRAM: parent BRAM = sum of children; reconcile with top and with resourceusage.rpt (including blackbox BRAM if any).

---

## 5. LUT Analysis

### 5.1 Top LUT Consumers (from CSV)

1. For each row, LUT total = LUT4 + LUT6 (columns 1 and 2).
2. Sort by LUT total descending; build:

| Report module | LUT4 | LUT6 | LUT total | RTL / notes |
|---------------|------|------|-----------|-------------|
| elastix_gemm_top | ... | ... | ... | (total) |
| engine_top_2d | ... | ... | ... | engine_top_2d.sv |
| compute_engine_2d (x16) | ... | ... | ... each | compute_engine_2d.sv |
| ... | ... | ... | ... | ... |

Include top, engine, compute engines, `comp_MLPStack`, `result_collector`, `comp_fp_adder_pipeline`, `master_control`, `dispatcher_control`, `dispatcher`, `fetcher`, `comp_row_bram`, `comp_MLPStack_oFIFO`, `flex_fifo`, `cmd_fifo`, and any IP (acx_device_manager, BW_BMC_IF). In the notes, reference resourceusage.rpt if LUT total differs (e.g. 430,828 + 113 in blackboxes = 430,941).

### 5.2 RTL Sources for Main LUT Blocks

LUTs are not mapped to single RTL lines; they come from the whole module. For each major block, describe what generates LUT:

- **FSMs:** state registers and next-state logic.
- **Counters:** b_cnt, cg_cnt, v_cnt, l_cnt, burst counters, etc.
- **Datapaths:** fp_to_int, int_adder_tree, int_to_fp, muxes, pack/unpack.
- **Glue:** address/decode, handshaking, read/write mux for FIFOs/BRAMs.

Use a short bullet list per RTL file, e.g.:

- **compute_engine_2d.sv** (~Xk LUT each): FSM, command depack, counters, row_bram/MLP/oFIFO wiring. Children: comp_MLPStack, comp_MLPStack_oFIFO, comp_row_bram.
- **comp_MLPStack.sv** (~Xk LUT each): comp_MLPRow stacks, comp_fp_adder_pipeline (fp_to_int, int_adder_tree, int_to_fp), weight depack, activation/control. MLP primitives are hard IP.
- **comp_fp_adder_pipeline.sv** (~Xk LUT each): fp_to_int, int_adder_tree, int_to_fp.
- **result_collector_2d.sv**: FSM, result gather, comp_fp_adder_pipeline, flex_fifo.
- **dispatcher_control_2d.sv**, **dispatcher_2d.sv**, **fetcher_2d.sv**: FSMs, address/param, AXI/FIFO control.
- **comp_row_bram.sv**, **comp_MLPStack_oFIFO.sv**: pack/unpack, decode, muxes (storage is BRAM/LRAM).
- **flex_fifo.sv**, **cmd_fifo.sv**: pointers, count, full/empty/afull; memory in LRAM or BRAM.
- **master_control_2d.sv**: FSM, command routing, dispatch, interfaces.

### 5.3 LUT Hierarchy Check

- engine_top_2d = 16x compute_engine_2d + master_control_2d + result_collector_2d + 16x dispatcher_control_2d + cmd_fifo + other (BMC, NAP, etc.).
- compute_engine_2d = comp_MLPStack + comp_MLPStack_oFIFO + comp_row_bram + CE FSM and wiring.

Use approximate per-instance LUT counts so the sum is consistent with the CSV.

---

## 6. Write syn_area.md

**Location:** `{build_dir}/syn_area.md` (e.g. `gemm/build/syn_area.md`).

**Structure:**

```markdown
# Synthesis Area Analysis: {top_name}

**Source report:** `results/ace/impl_1/syn/rev_acx/synlog/report/{top_name}_impl_1_fpga_mapper_hier_area.csv`
**Resource summary:** `.../{top_name}_impl_1_fpga_mapper_resourceusage.rpt`
**Generated:** {output of `date`}

CSV columns: Module name, LUT4, LUT6, DFF, ALU8, BRAM, LRAM, MLP, PADS.

---

## 1. Top-Level Resource Summary
[Table from section 2]

---

## 2. LRAM Analysis
Total LRAM: **{N}**. Hierarchy and RTL sources cross-checked with the hierarchical area CSV.

### 2.1 Top LRAM Consumers (by hierarchy)
[Table]

### 2.2 RTL Locations for LRAM
[Table and notes]

### 2.3 LRAM Hierarchy Check
[Bullet checks]

---

## 3. BRAM Analysis
Total BRAM: **{N}**. ...

### 3.1 Top BRAM Consumers (by hierarchy)
[Table]

### 3.2 RTL Locations for BRAM
[Table and notes]

### 3.3 BRAM Hierarchy Check
[Bullet checks]

---

## 4. LUT Analysis
Total LUT: **{N}** (LUT4: ...; LUT6: ...). [Note resourceusage.rpt if different.]

### 4.1 Top LUT Consumers (LUT4 + LUT6)
[Table]

### 4.2 RTL Sources for Main LUT Blocks
[Bullet list per RTL file]

### 4.3 LUT Hierarchy Check
[Bullet checks]

---

## 5. Report and Paths
- Hierarchical area (CSV): `{full path}`
- Resource usage: `{full path}`

All module names and counts from the CSV and resourceusage.rpt.
```

**Timestamp:** Run `date` and paste the exact output into `**Generated:**`.

---

## 7. Workflow Checklist

- [ ] Locate `*_fpga_mapper_hier_area.csv` and `*_fpga_mapper_resourceusage.rpt`
- [ ] Fill top-level summary from resourceusage.rpt
- [ ] LRAM: top consumers (CSV), RTL locations (grep ram_style, arrays, FIFOs), hierarchy check
- [ ] BRAM: top consumers (CSV), RTL locations (BRAM72K, large arrays/FIFOs), hierarchy check
- [ ] LUT: top consumers (CSV, LUT4+LUT6), RTL sources (FSM, counters, datapaths, glue), hierarchy check
- [ ] Write `syn_area.md` with `date` for Generated
- [ ] Use plain ASCII only (no Unicode symbols) in tables and text

---

## Reference: elastix_gemm Example

The `gemm/build/syn_area.md` in this repo is a full example for `elastix_gemm_top`, with LRAM (sect. 2), LUT (sect. 3), and a top-level summary that includes BRAM. Use it as a concrete pattern; add a dedicated BRAM section (3.x) if you need the same depth of analysis for BRAM as for LRAM and LUT.
