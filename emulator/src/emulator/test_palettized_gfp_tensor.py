import random

import numpy as np
import torch

from emulator import group_floating_point as gfp
from emulator import palettized_gfp_tensor as pgt


def test_palettized_gfp_tensor(
    exp_bits=3, mantissa_bits=5, num_palette_entries=16, num_groups=3, group_size=5
):
    # Create the dtype
    gfp_dtype = gfp.GFPDataType(
        mantissa_bits=mantissa_bits, exp_bits=exp_bits, mantissa_signed=False
    )

    # Initialize the palette with a simple scaling operation
    palette = [x * 2 for x in range(num_palette_entries)]

    rows = num_groups
    cols = group_size

    # Create the palettized mantissa and expected de-palettized output
    palettized_np = np.zeros((rows, cols), dtype=np.int32)
    exponents = []
    expected_np = np.zeros((rows, cols), dtype=np.float32)
    for row in range(rows):
        # Choose a random exponent for this row and group
        group_exp = random.randint(0, (2**exp_bits) - 1)
        exponents.append(group_exp)

        for elem_idx in range(cols):
            # Choose a random palette index
            palette_idx = random.randint(0, num_palette_entries - 1)
            palettized_np[row, elem_idx] = palette_idx

            # Calculate the expected de-palettized value
            mantissa = palette[palette_idx]
            expected = mantissa * (2 ** (group_exp - gfp_dtype.exp_bias))
            expected_np[row, elem_idx] = expected

    palettized = pgt.PalettizedGFPTensor(
        original_shape=torch.Size((rows, cols)),
        group_axis=-1,
        group_size=group_size,
        dtype=gfp_dtype,
        palette_indices=torch.tensor(palettized_np, dtype=torch.int32).unsqueeze(
            1
        ),  # Add group dimension
        palette=torch.tensor(palette),
        exp_data=torch.tensor(exponents)
        .unsqueeze(-1)
        .reshape(num_groups, 1, 1),  # Shape: [num_groups, 1, 1]
    )

    result = palettized.dequantize()
    expected = torch.tensor(expected_np)

    if (result != expected).any():
        raise ValueError("Palettized GFP result does not match expected")


if __name__ == "__main__":
    test_palettized_gfp_tensor()
