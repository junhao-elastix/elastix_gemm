#!/usr/bin/env python3
"""Cocotb test runner for group_max_exp_finder module."""

import os
import sys
from pathlib import Path

# Add project root to Python path for test module imports
proj_path = Path(__file__).resolve().parents[2]
if str(proj_path) not in sys.path:
    sys.path.insert(0, str(proj_path))

# Set PYTHONPATH for cocotb subprocess
os.environ["PYTHONPATH"] = str(proj_path) + ":" + os.environ.get("PYTHONPATH", "")

try:
    from cocotb_tools.runner import get_runner
except ImportError:
    from cocotb.runner import get_runner


def get_build_args(sim: str) -> list[str]:
    args = []
    if sim in ["riviera", "activehdl"]:
        args = ["-sv2k12"]
    elif sim == "questa":
        args = ["-sv"]
    return args


def run_test():
    sim = os.getenv("SIM", "riviera")
    runner = get_runner(sim)

    proj_path = Path(__file__).resolve().parents[2]
    rtl_path = proj_path / "rtl"
    results_path = proj_path / "results"
    results_path.mkdir(exist_ok=True)

    sources = [rtl_path / "group_max_exp_finder.sv"]

    # GFP16 format parameters
    parameters = {
        "EXP_WIDTH": 5,      # GFP16: 5-bit exponent
        "IN_ELEMENTS": 8,
        "GROUP_WORDS": 2,
        "MAN_BITS": 11,      # GFP16: 11-bit signed mantissa
    }

    print(f"\n{'='*60}")
    print(f"Running group_max_exp_finder tests")
    print(f"Parameters: {parameters}")
    print(f"{'='*60}\n")

    runner.build(
        hdl_toplevel="group_max_exp_finder",
        sources=[str(s) for s in sources],
        build_args=get_build_args(sim),
        parameters=parameters,
        always=True,
    )

    runner.test(
        hdl_toplevel="group_max_exp_finder",
        hdl_toplevel_lang="verilog",
        test_module="tests.unit.test_group_max_exp_finder",
        results_xml=str(results_path / "group_max_exp_finder_results.xml"),
    )


if __name__ == "__main__":
    run_test()
