#!/usr/bin/env python3
"""
Cocotb test runner for gfp_norm_quant integration module.
GFP16 -> GFP8 normalize and quantize.

Usage:
    SIM=riviera python run_gfp_norm_quant.py
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
    common_path = proj_path.parent / "common"  # fp_convertor/common/
    results_path = proj_path / "results"
    results_path.mkdir(exist_ok=True)

    # All RTL sources including common FIFOs
    sources = [
        # Common utilities
        common_path / "fifo.sv",
        common_path / "one_fifo.sv",
        common_path / "two_fifo.sv",
        # Sub-modules for GFP16 -> GFP8
        rtl_path / "gfp16_extract.sv",
        rtl_path / "signed_aligner.sv",
        rtl_path / "gfp8_quantizer.sv",
        rtl_path / "group_max_exp_finder.sv",
        # Top-level
        rtl_path / "gfp_norm_quant.sv",
    ]

    # GFP16 -> GFP8 parameters
    parameters = {
        # GFP16 input format
        "GFP16_TOTAL_BITS": 16,
        "GFP16_EXP_BITS": 5,
        "GFP16_MAN_BITS": 11,
        # GFP8 output format
        "GFP8_MAN_BITS": 8,
        "GFP8_EXP_BITS": 5,
        # Streaming parameters
        "IN_ELEMENTS": 8,
        "INGRESS_FIFO_ELS": 4,
        "DATA_FIFO_ELS": 4,
        "EGRESS_FIFO_ELS": 2,
    }

    print(f"\n{'='*60}")
    print("Running gfp_norm_quant integration tests (GFP16 -> GFP8)")
    print(f"Parameters: {parameters}")
    print(f"{'='*60}\n")

    runner.build(
        hdl_toplevel="gfp_norm_quant",
        sources=[str(s) for s in sources],
        build_args=get_build_args(sim),
        parameters=parameters,
        always=True,
    )

    runner.test(
        hdl_toplevel="gfp_norm_quant",
        hdl_toplevel_lang="verilog",
        test_module="tests.unit.test_gfp_norm_quant",
        results_xml=str(results_path / "gfp_norm_quant_results.xml"),
    )


if __name__ == "__main__":
    run_test()
