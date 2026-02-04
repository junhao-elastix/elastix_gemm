#!/usr/bin/env python3
"""
Cocotb test runner for gfp16_extract module.

Usage:
    SIM=riviera python run_gfp16_extract.py
"""

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
    """Get simulator-specific build arguments."""
    args = []
    if sim in ["riviera", "activehdl"]:
        args = ["-sv2k12"]
    elif sim == "questa":
        args = ["-sv"]
    return args


def run_test():
    """Run gfp16_extract tests."""
    sim = os.getenv("SIM", "riviera")
    runner = get_runner(sim)

    proj_path = Path(__file__).resolve().parents[2]
    rtl_path = proj_path / "rtl"
    results_path = proj_path / "results"
    results_path.mkdir(exist_ok=True)

    sources = [rtl_path / "gfp16_extract.sv"]

    # GFP16 format parameters
    parameters = {
        "GFP16_TOTAL_BITS": 16,
        "GFP16_EXP_BITS": 5,
        "GFP16_MAN_BITS": 11,
        "IN_ELEMENTS": 8,
    }

    print(f"\n{'='*60}")
    print("Running gfp16_extract tests")
    print(f"Parameters: {parameters}")
    print(f"{'='*60}\n")

    runner.build(
        hdl_toplevel="gfp16_extract",
        sources=[str(s) for s in sources],
        build_args=get_build_args(sim),
        parameters=parameters,
        always=True,
    )

    runner.test(
        hdl_toplevel="gfp16_extract",
        hdl_toplevel_lang="verilog",
        test_module="tests.unit.test_gfp16_extract",
        results_xml=str(results_path / "gfp16_extract_results.xml"),
    )


if __name__ == "__main__":
    run_test()
