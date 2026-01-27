# This file is public domain, it can be freely copied without restrictions.
# SPDX-License-Identifier: CC0-1.0
from __future__ import annotations

import pytest

from build_misc import int_to_float24

@pytest.mark.parametrize(
    "value, expected",
    [
        (0x000000, 0.0),         # +0
        (0x800000, -0.0),        # -0
        (0x3F8000, 1.0),         # +1
        (0xBF8000, -1.0),        # -1
        (0x412000, 10.0),        # +10
        (0xC12000, -10.0),       # -10
        (0x7F7FFF, 2**128 - 2**112),  # max normal positive
        (0x000001, 2**-126),   # min normal positive
        (0x7F8000, float('inf')),    # +inf
        (0xFF8000, float('-inf')),   # -inf
        (0x7F8001, float('nan')),    # nan
        (0xFF8001, float('nan')),    # nan
        (0x000001, 2 ** -126 / 32768), # smallest positive subnormal
        (0x800001, -2 ** -126 / 32768), # smallest negative subnormal
    ]
)
def test_int_to_float24(value, expected):
    result = int_to_float24(value)
    if isinstance(expected, float) and (expected != expected):  # nan
        assert result != result
    elif expected in (float('inf'), float('-inf')):
        assert result == expected
    else:
        assert abs(result - expected) < 1e-5
