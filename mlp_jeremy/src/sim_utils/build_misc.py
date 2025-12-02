# This file is public domain, it can be freely copied without restrictions.
# SPDX-License-Identifier: CC0-1.0
from __future__ import annotations

import os

def get_acx_vlog_flags(acx_device="AC7t1500") -> list[str]:
    """Get Achronix includes & build flags (this is all copied from ACX Makefiles)."""
    VLOG_FLAGS = []
    ace_install_dir = os.getenv("ACE_INSTALL_DIR", "")
    if (not ace_install_dir):
        raise EnvironmentError("ACE_INSTALL_DIR not set, check ACE installation.")

    acx_device_dir = f"{ace_install_dir}/system/data/{acx_device}"
    # This ENV shows up in the ACE include files, and must be set to compile them
    os.environ["ACX_DEVICE_INSTALL_DIR"] = acx_device_dir

    VLOG_FLAGS.append(f"+incdir+{ace_install_dir}/libraries")
    VLOG_FLAGS.append(f"+incdir+{acx_device_dir}/sim")
    VLOG_FLAGS.append("+define+RIVIERA")
    #VLOG_FLAGS.append("+define+ACX_DUMP_SIM_SIGNALS")
    device_lower = acx_device.lower()
    VLOG_FLAGS.append(f"-f {acx_device_dir}/sim/{device_lower}_dsm_incdirs.f")
    VLOG_FLAGS.append(f"{acx_device_dir}/sim/{device_lower}_dsm_filelist.v")
    # Device simulation models
    VLOG_FLAGS.append(f"{ace_install_dir}/libraries/device_models/{acx_device}_simmodels.sv")
    # Suppress VCP3005 and VCP7079 from ACX sim models
    for WARN in ["VCP3005", "VCP7079"]:
        VLOG_FLAGS.append(f"-err {WARN} W9")

    return VLOG_FLAGS

def int_to_float24(value):
    sign = (value >> 23) & 0x1
    exponent = (value >> 15) & 0xFF
    mantissa = value & 0x7FFF

    if exponent == 0:
        if mantissa == 0:
            return -0.0 if sign else 0.0
        else:
            # Subnormal numbers (NOTE: ACX converts subnormals to ZERO (!))
            return (-1) ** sign * (mantissa / 32768.0) * (2 ** -127)
    elif exponent == 255:
        if mantissa == 0:
            return float('-inf') if sign else float('inf')
        else:
            return float('nan')
    else:
        # Normal numbers
        normalized_mantissa = 1.0 + (mantissa / 32768.0)
        return (-1) ** sign * normalized_mantissa * (2 ** (exponent - 127))
 