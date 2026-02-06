#!/usr/bin/env python3
"""
Cocotb test runner for gfp_norm_quant integration module.
GFP11e5 -> GFP8e5 normalize and quantize.

Usage:
    SIM=riviera python run_gfp_norm_quant.py
"""

import os
import sys
from pathlib import Path

# Add cocotb directory and project root to Python path
cocotb_path = Path(__file__).resolve().parent
proj_path = Path(__file__).resolve().parents[2]
for p in [cocotb_path, proj_path]:
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

# Set PYTHONPATH for cocotb subprocess
os.environ["PYTHONPATH"] = f"{cocotb_path}:{proj_path}:" + os.environ.get("PYTHONPATH", "")

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
        common_path / "two_fifo.sv",
        # Sub-modules for GFP11e5 -> GFP8e5
        rtl_path / "gfp_align_quant.sv",  # Merged aligner + quantizer
        rtl_path / "gfp_find_max_exp.sv",
        # Top-level
        rtl_path / "gfp_norm_quant.sv",
    ]

    # GFP11e5 -> GFP8e5 parameters
    parameters = {
        # GFP11e5 input format (11-bit mantissa + 5-bit exponent = 16 bits)
        "GFP11e5_TOTAL_BITS": 16,
        "GFP11e5_EXP_BITS": 5,
        "GFP11e5_MAN_BITS": 11,
        # GFP8e5 output format (8-bit mantissa + 5-bit exponent = 13 bits)
        "GFP8e5_MAN_BITS": 8,
        "GFP8e5_EXP_BITS": 5,
        # Streaming parameters
        "IN_ELEMENTS": 32,        # 32 GFP11e5 elements per word
        "INGRESS_FIFO_ELS": 8,
        "DATA_FIFO_ELS": 8,
        "EGRESS_FIFO_ELS": 4,
    }

    print(f"\n{'='*60}")
    print("Running gfp_norm_quant integration tests (GFP11e5 -> GFP8e5)")
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
        test_module="test_gfp_norm_quant",
        results_xml=str(results_path / "gfp_norm_quant_results.xml"),
    )


if __name__ == "__main__":
    run_test()
