# This file is public domain, it can be freely copied without restrictions.
# SPDX-License-Identifier: CC0-1.0
from __future__ import annotations

import os
import sys
from pathlib import Path

from sim_utils.build_misc import get_acx_vlog_flags
from cocotb_tools.runner import get_runner

# Test import dependencies:
# import torch
# from emulator import group_floating_point as gfp

def test_acx_mlp_runner():
    """Simulate acx_mlp  using the Python runner.

    This file can be run directly or via pytest discovery, e.g.
    uv run pytest -s
    uv run sim/test_acx_mlp.py
    """
    hdl_toplevel_lang = os.getenv("HDL_TOPLEVEL_LANG", "verilog")
    sim = os.getenv("SIM", "riviera")
    sources = []

    proj_path = Path(__file__).resolve().parent.parent

    # Order matters, glob won't guarantee it
    # sources = proj_path.glob("rtl/*.sv")
    rtl_files = [
        "mlp_dot16_int8.sv",
        "mlp_dot16_bfp8.sv",
        "weight_bram.sv",
        "mlp_bram.sv",
        "mlp_bram_col.sv",
    ]
    for f in rtl_files:
        sources.append(proj_path / "rtl" / f)

    print("sources =")
    for s in sources:
        print(s)

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
        "NUM_MLPS": 4,
        "dump_waves": 1,
    }

    runner = get_runner(sim)
    # Riviera runner calls 'alog' for EVERY source file, which is super slow.
    # Only pass top-level as a source file, pass the rest as build_args
    top_level_source = sources.pop(-1)

    runner.build(
        hdl_toplevel="mlp_bram_col",
        sources=[top_level_source],
        build_args=build_args + extra_args + acx_build_args + [str(s) for s in sources],
        parameters=parameters,
        always=False, # <-- (!) Set to True when iterating verilog, False when only changing tests
    )

    # Location of 'test_module' (passed to runner.test)
    sys.path.append(str(proj_path / "tests"))

    print("Calling runnner test()...")
    runner.test(
        hdl_toplevel="mlp_bram_col",
        hdl_toplevel_lang=hdl_toplevel_lang,
        test_module="acx_mlp_tests",
        test_args=extra_args, # + ["-advdataflow"],
        results_xml=proj_path / "mlp_bram_col_results.xml",
    )


if __name__ == "__main__":
    test_acx_mlp_runner()
