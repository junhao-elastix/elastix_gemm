# This file is public domain, it can be freely copied without restrictions.
# SPDX-License-Identifier: CC0-1.0
"""
Simulation runner for mlp_bram_col_ctrl.sv testbench.

Tests Native Vector weight loading and vector-matrix multiplication.

Usage:
    cd mlp_jeremy/src/acx_mlp
    uv run pytest sim/test_mlp_bram_col_ctrl.py -s
    # or
    uv run sim/test_mlp_bram_col_ctrl.py
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

from sim_utils.build_misc import get_acx_vlog_flags
from cocotb_tools.runner import get_runner


def test_mlp_bram_col_ctrl_runner():
    """Simulate mlp_bram_col_ctrl using the Python runner."""
    hdl_toplevel_lang = os.getenv("HDL_TOPLEVEL_LANG", "verilog")
    sim = os.getenv("SIM", "riviera")
    sources = []

    proj_path = Path(__file__).resolve().parent.parent

    # RTL files in dependency order
    rtl_files = [
        "mlp_dot16_int8.sv",
        "mlp_dot16_bfp8.sv",
        "weight_bram.sv",
        "mlp_bram.sv",
        "mlp_bram_col.sv",
        "mlp_bram_col_ctrl.sv",  # Top-level DUT
    ]
    for f in rtl_files:
        sources.append(proj_path / "rtl" / f)

    print("RTL sources:")
    for s in sources:
        print(f"  {s}")

    build_args = []
    if sim in ["riviera", "activehdl"]:
        build_args = ["-sv2k12"]

    acx_build_args = get_acx_vlog_flags()

    extra_args = []
    if sim == "ghdl":
        extra_args = ["--std=08"]
    elif sim == "xcelium":
        extra_args = ["-v200x"]

    parameters = {
        "NUM_MLPS": 8,  # 8 MLPs = 16 columns
    }

    runner = get_runner(sim)

    # Riviera runner calls 'alog' for EVERY source file, which is slow.
    # Only pass top-level as a source file, pass the rest as build_args
    top_level_source = sources.pop(-1)

    runner.build(
        hdl_toplevel="mlp_bram_col_ctrl",
        sources=[top_level_source],
        build_args=build_args + extra_args + acx_build_args + [str(s) for s in sources],
        parameters=parameters,
        always=True,  # Set to True when iterating verilog, False when only changing tests
    )

    # Location of 'test_module' (passed to runner.test)
    sys.path.append(str(proj_path / "tests"))

    print("Running tests...")
    runner.test(
        hdl_toplevel="mlp_bram_col_ctrl",
        hdl_toplevel_lang=hdl_toplevel_lang,
        test_module="acx_mlp_tests_nv",
        test_args=extra_args,
        results_xml=proj_path / "mlp_bram_col_ctrl_results.xml",
    )


if __name__ == "__main__":
    test_mlp_bram_col_ctrl_runner()
