import torch

from emulator import group_floating_point as gfp


class PalettizedGFPTensor(gfp.GFPTensorBase):
    """
    GFP tensor with palettized mantissa values. Instead of storing raw mantissa
    and sign data, stores palette indices and a shared palette of values.
    Exponents are still shared per group.
    """

    def __init__(
        self,
        original_shape: torch.Size,
        group_axis: int,
        group_size: int,
        dtype: gfp.GFPDataType,
        *,
        palette_indices: torch.Tensor,
        palette: torch.Tensor,
        exp_data: torch.Tensor,
    ) -> None:
        super().__init__(original_shape, group_axis, group_size, dtype)

        if palette_indices is not None and palette is not None and exp_data is not None:
            self.palette_indices = palette_indices
            self.palette = palette
            self.exp_data = exp_data
        else:
            raise ValueError("Invalid initialization parameters")

        self._verify()

    def _verify(self):
        """Verify the palettized GFP tensor for correctness and validity."""
        super()._verify()

        # Check palette indices shape
        if self.palette_indices.shape != self.mantissa_shape:
            raise ValueError(
                f"palette_indices shape mismatch - expected: {self.mantissa_shape}, "
                f"got: {self.palette_indices.shape}"
            )

        # Check exponent shape
        if self.exp_data.shape != self.exp_shape:
            raise ValueError(
                f"exp_data shape mismatch - expected: {self.exp_shape}, "
                f"got: {self.exp_data.shape}"
            )

        # Check palette indices are valid
        if (self.palette_indices < 0).any() or (
            self.palette_indices >= len(self.palette)
        ).any():
            raise ValueError(
                f"palette_indices out of range [0, {len(self.palette)-1}], "
                f"min: {self.palette_indices.min()}, max: {self.palette_indices.max()}"
            )

        if (self.palette < self.dtype.bottom_mantissa).any() or (
            self.palette > self.dtype.top_mantissa
        ).any():
            raise ValueError(
                f"palette out of range [{self.dtype.bottom_mantissa}, {self.dtype.top_mantissa}], "
                f"min: {self.palette.min()}, max: {self.palette.max()}"
            )

        # Check exponent range
        if (self.exp_data < self.dtype.bottom_exp).any() or (
            self.exp_data > self.dtype.top_exp
        ).any():
            raise ValueError(
                f"exp_data out of range [{self.dtype.bottom_exp}, {self.dtype.top_exp}], "
                f"min: {self.exp_data.min()}, max: {self.exp_data.max()}"
            )

    def dequantize(self) -> torch.Tensor:
        """
        Dequantize the palettized GFP data back to float.
        """
        return self.depalettize().dequantize()

    def depalettize(self) -> gfp.GFPTensor:
        """
        Convert back to standard GFP tensor by expanding palette indices.
        """
        # Reconstruct mantissa data from palette
        mantissa_values = self.palette[self.palette_indices]

        # Separate into mantissa and sign for unsigned mantissa types
        if self.dtype.mantissa_signed:
            mantissa_data = mantissa_values
            sign_data = None
        else:
            mantissa_data = mantissa_values.abs()
            sign_data = mantissa_values.sign()

        return gfp.GFPTensor(
            self.original_shape,
            self.group_axis,
            self.group_size,
            self.dtype,
            mantissa_data=mantissa_data,
            exp_data=self.exp_data,
            sign_data=sign_data,
        )
