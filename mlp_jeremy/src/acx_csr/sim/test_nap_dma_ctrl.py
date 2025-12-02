# This file is public domain, it can be freely copied without restrictions.
# SPDX-License-Identifier: CC0-1.0
from __future__ import annotations

import os
import sys
from pathlib import Path

from sim_utils.build_misc import get_acx_vlog_flags
from cocotb_tools.runner import get_runner


def test_runner():
    """Simulate using the Python runner.

    This file can be run directly or via pytest discovery, e.g.
    uv run pytest -s
    """
    hdl_toplevel_lang = os.getenv("HDL_TOPLEVEL_LANG", "verilog")
    sim = os.getenv("SIM", "riviera")
    sources = []

    proj_path = Path(__file__).resolve().parent.parent

    include_dirs = [proj_path / "include"]

    include_files = [
        proj_path.parent / "acx_common/sdpram_infer.sv",
    ]

    for f in include_files:
        sources.append(f)

    # Order matters, glob won't guarantee it
    # sources = proj_path.glob("rtl/*.sv")
    rtl_files = [
        "nap_initiator_wrapper.sv",
        "nap_responder_wrapper.sv",
        "nap_dma_ctrl.sv",
    ]

    for f in rtl_files:
        sources.append(proj_path / "rtl" / f)

    # Only pass top-level as a source file, pass the rest as build_args
    top_level_source = sources.pop(-1)
    top_level_module = "nap_dma_ctrl"
    build_dir = proj_path / "sim_builds" / (top_level_module + "_build")

    build_args = []

    if sim in ["riviera", "activehdl"]:
        build_args = ["-sv2k12"]


    acx_build_args = get_acx_vlog_flags()
    for incdir in include_dirs:
        acx_build_args.append(f"+incdir+{str(incdir)}")

    extra_args = []
    if sim == "ghdl":
        extra_args = ["--std=08"]
    elif sim == "xcelium":
        extra_args = ["-v200x"]

    parameters = {
        "NUM_USER_REGS": 12,
        "DUMP_WAVES": 1,
    }

    runner = get_runner(sim)
    # Riviera runner calls 'alog' for EVERY source file, only pass top-level RTL as 'sources'
    runner.build(
        hdl_toplevel=top_level_module,
        sources=[top_level_source],
        build_args=build_args + extra_args + acx_build_args + [str(s) for s in sources],
        parameters=parameters,
        always=True, # <-- (!) Set to True when iterating verilog, False when only changing tests
        build_dir=build_dir,
    )

    # Location of 'test_module' (passed to runner.test)
    sys.path.append(str(proj_path / "tests"))

    print("Calling runnner test()...")
    runner.test(
        hdl_toplevel=top_level_module,
        hdl_toplevel_lang=hdl_toplevel_lang,
        test_module="nap_dma_ctrl_tests",
        test_args=extra_args, # + ["-advdataflow"],
        build_dir=build_dir,
    )


if __name__ == "__main__":
    test_runner()
