#!/usr/bin/env python3
"""
Cocotb test runner for gfp8_quantizer module.

Usage:
    SIM=riviera python run_gfp8_quantizer.py
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
    """Run gfp8_quantizer tests."""
    sim = os.getenv("SIM", "riviera")
    runner = get_runner(sim)

    proj_path = Path(__file__).resolve().parents[2]
    rtl_path = proj_path / "rtl"
    results_path = proj_path / "results"
    results_path.mkdir(exist_ok=True)

    sources = [rtl_path / "gfp8_quantizer.sv"]

    # GFP16 to GFP8 parameters
    parameters = {
        "IN_MAN_BITS": 11,   # GFP16 mantissa
        "OUT_MAN_BITS": 8,   # GFP8 mantissa
        "IN_ELEMENTS": 8,
    }

    print(f"\n{'='*60}")
    print("Running gfp8_quantizer tests")
    print(f"Parameters: {parameters}")
    print(f"{'='*60}\n")

    runner.build(
        hdl_toplevel="gfp8_quantizer",
        sources=[str(s) for s in sources],
        build_args=get_build_args(sim),
        parameters=parameters,
        always=True,
    )

    runner.test(
        hdl_toplevel="gfp8_quantizer",
        hdl_toplevel_lang="verilog",
        test_module="tests.unit.test_gfp8_quantizer",
        results_xml=str(results_path / "gfp8_quantizer_results.xml"),
    )


if __name__ == "__main__":
    run_test()
