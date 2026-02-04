#!/usr/bin/env python3
"""
Cocotb test runner for signed_aligner module.

Usage:
    SIM=riviera python run_signed_aligner.py
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
    """Run signed_aligner tests."""
    sim = os.getenv("SIM", "riviera")
    runner = get_runner(sim)

    proj_path = Path(__file__).resolve().parents[2]
    rtl_path = proj_path / "rtl"
    results_path = proj_path / "results"
    results_path.mkdir(exist_ok=True)

    sources = [rtl_path / "signed_aligner.sv"]

    # GFP16 format parameters
    parameters = {
        "EXP_BITS": 5,
        "MAN_BITS": 11,
        "IN_ELEMENTS": 8,
    }

    print(f"\n{'='*60}")
    print("Running signed_aligner tests")
    print(f"Parameters: {parameters}")
    print(f"{'='*60}\n")

    runner.build(
        hdl_toplevel="signed_aligner",
        sources=[str(s) for s in sources],
        build_args=get_build_args(sim),
        parameters=parameters,
        always=True,
    )

    runner.test(
        hdl_toplevel="signed_aligner",
        hdl_toplevel_lang="verilog",
        test_module="tests.unit.test_signed_aligner",
        results_xml=str(results_path / "signed_aligner_results.xml"),
    )


if __name__ == "__main__":
    run_test()
