from __future__ import annotations

import logging
import math

import torch
import torch.nn.functional as F


def clamp_with_logging(
    x: torch.Tensor,
    min: float | None = None,
    max: float | None = None,
    prefix: str = "",
) -> torch.Tensor:
    """Clamp with logging"""
    if min is not None and (x < min).any():
        logging.warning(f"{prefix} underflow clamping detected: {x[x < min]}")
    if max is not None and (x > max).any():
        logging.error(f"{prefix} overflow clamping detected: {x[x > max]}")
    return x.clamp(min, max)


class GFPDataType:
    """
    Elastix Group Floating Point (GFP) type. If mantissa_signed is True, the
    mantissa is signed; otherwise, it is unsigned and we use a extra sign bit
    to represent the sign.
    """

    def __init__(
        self,
        mantissa_bits: int,
        exp_bits: int,
        exp_bias: int | None = None,
        mantissa_signed: bool = True,
    ) -> None:
        self.mantissa_bits = mantissa_bits
        self.exp_bits = exp_bits
        self.exp_bias = exp_bias if exp_bias is not None else 2 ** (exp_bits - 1)
        self.mantissa_signed = mantissa_signed

        self._verify()

    def __str__(self) -> str:
        return (
            f"GFPDataType("
            f"bits={self.mantissa_bits}m/{self.exp_bits}e"
            f"{'/1s' if not self.mantissa_signed else ''}, "
            f"exp_bias={self.exp_bias})"
        )

    def __eq__(self, value: object) -> bool:
        if not isinstance(value, GFPDataType):
            return False
        return (
            self.mantissa_bits == value.mantissa_bits
            and self.exp_bits == value.exp_bits
            and self.exp_bias == value.exp_bias
            and self.mantissa_signed == value.mantissa_signed
        )

    def _verify(self):
        """Verify the GFP type for correctness and validity"""
        if self.mantissa_bits <= 0 or self.exp_bits <= 0:
            raise ValueError(
                f"Invalid bit width - mantissa_bits: {self.mantissa_bits}, exp_bits: {self.exp_bits}"
            )

        if self.exp_bias < 0 or self.exp_bias > self.top_exp:
            raise ValueError(
                f"Invalid exp_bias: {self.exp_bias}, should be in [0, {self.top_exp}]"
            )

    @property
    def effective_mantissa_bits(self) -> int:
        """Effective mantissa bits, i.e., mantissa_bits - 1 for signed mantissa,
        mantissa_bits for unsigned mantissa"""
        if self.mantissa_signed:
            return self.mantissa_bits - 1
        else:
            return self.mantissa_bits

    @property
    def top_exp(self) -> int:
        """Top exponent value, i.e., 2**exp_bits - 1"""
        return 2**self.exp_bits - 1

    @property
    def top_exp_biased(self) -> int:
        """Top exponent value biased by exp_bias, i.e., top_exp - exp_bias"""
        return self.top_exp - self.exp_bias

    @property
    def bottom_exp(self) -> int:
        """Bottom exponent value, i.e., 0"""
        return 0

    @property
    def bottom_exp_biased(self) -> int:
        """Bottom exponent value biased by exp_bias, i.e., -exp_bias"""
        return self.bottom_exp - self.exp_bias

    @property
    def top_mantissa(self) -> int:
        """
        Top mantissa value, i.e., 2**effective_mantissa_bits - 1
        """
        return 2**self.effective_mantissa_bits - 1

    @property
    def bottom_mantissa(self) -> int:
        """
        Bottom mantissa value, i.e., -2**effective_mantissa_bits for signed
        mantissa, 0 for unsigned mantissa
        """
        if self.mantissa_signed:
            return -(2**self.effective_mantissa_bits)
        else:
            return 0

    @property
    def bottom_mantissa_signed(self) -> int:
        """
        Bottom signed mantissa value, i.e., bottom_mantissa for signed mantissa,
        -top_mantissa for unsigned mantissa
        """
        if self.mantissa_signed:
            return self.bottom_mantissa
        else:
            return -self.top_mantissa

    @property
    def top_val(self) -> float:
        """Maximum value, i.e., 2**top_exp_biased * top_mantissa"""
        return 2**self.top_exp_biased * self.top_mantissa

    @property
    def bottom_val(self) -> float:
        """Non-zero minimum value, i.e., 2**top_exp_biased * bottom_mantissa_signed"""
        return 2**self.top_exp_biased * self.bottom_mantissa_signed


class GFPTensorBase:
    """
    Elastix Group Floating Point (GFP) tensor base class
    """

    def __init__(
        self,
        original_shape: torch.Size,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
    ) -> None:
        self.original_shape = original_shape
        self.group_axis = group_axis
        self.group_size = group_size
        self.dtype = dtype

    def __str__(self) -> str:
        return (
            f"GFPTensor("
            f"original_shape={list(self.original_shape)}, "
            f"group_axis={self.group_axis}, "
            f"group_size={self.group_size}, "
            f"dtype={self.dtype})"
        )

    def __eq__(self, value: object) -> bool:
        if not isinstance(value, GFPTensorBase):
            return False
        return (
            self.original_shape == value.original_shape
            and self.group_axis == value.group_axis
            and self.group_size == value.group_size
            and self.dtype == value.dtype
        )

    def _verify(self):
        """Verify the GFP configuration for correctness and validity"""
        if self.group_size <= 0:
            raise ValueError(f"Invalid group_size: {self.group_size}")

        if (
            self.group_axis >= self.original_ndim
            or self.group_axis < -self.original_ndim
        ):
            raise ValueError(
                f"Invalid group_axis {self.group_axis} for tensor with {self.original_ndim} dimensions"
            )

    def get_grouped_slices(self, slices: list[slice | int]) -> list[slice | int]:
        group_axis_slice = slices[self.group_axis]
        if isinstance(group_axis_slice, slice):
            if group_axis_slice.step not in (1, None):
                raise ValueError("Step is not supported for group axis")

            # Handle the case when start/stop is not specified
            start = group_axis_slice.start if group_axis_slice.start is not None else 0
            stop = (
                group_axis_slice.stop
                if group_axis_slice.stop is not None
                else self.group_axis_size
            )

            # Handle the case when padding is needed
            if stop == self.group_axis_size:
                stop = self.num_groups * self.group_size

            # Check the validity of the slice
            if stop - start < self.group_size:
                raise ValueError(
                    f"Group axis slice length must be at least {self.group_size}"
                )
            if start % self.group_size != 0 or stop % self.group_size != 0:
                raise ValueError(
                    f"Group axis slice start/stop must be divisible by {self.group_size}"
                )

            # Calculate the group index axis and group axis slices
            group_idx_axis_slice: slice | int = slice(
                start // self.group_size, stop // self.group_size, 1
            )
            group_axis_slice = slice(0, self.group_size, 1)
        elif isinstance(group_axis_slice, int):
            if self.group_size != 1:
                raise ValueError("Group axis slice must be a slice for group_size > 1")

            group_idx_axis_slice = group_axis_slice
            group_axis_slice = 0
        else:
            raise ValueError(f"Invalid key type: {type(group_axis_slice)}")

        slices[self.group_axis] = slices[-1]
        slices = slices[:-1] + [group_idx_axis_slice, group_axis_slice]
        return slices

    @property
    def original_ndim(self) -> int:
        """Rank of the original data"""
        return len(self.original_shape)

    @property
    def grouped_ndim(self) -> int:
        """Rank of the grouped data"""
        return self.original_ndim + 1

    @property
    def grouped_shape(self) -> torch.Size:
        """Shape of the grouped data"""
        x = torch.empty(self.original_shape, device="meta")

        # Transpose the group dimension to the last dimension
        if self.group_axis != -1:
            x = x.transpose(-1, self.group_axis)

        # Pad if needed to make last dimension divisible by group_size
        if self.pad_size > 0:
            x = F.pad(x, (0, self.pad_size))

        # Separate the last dimension into (num_groups, group_size)
        x = x.unflatten(-1, (self.num_groups, self.group_size))

        return x.shape

    @property
    def mantissa_shape(self) -> torch.Size:
        """Shape of the mantissa data"""
        return self.grouped_shape

    @property
    def exp_shape(self) -> torch.Size:
        """Shape of the exponent data"""
        return self.grouped_shape[:-1] + (1,)

    @property
    def sign_shape(self) -> torch.Size:
        """Shape of the sign data"""
        return self.grouped_shape

    @property
    def group_axis_size(self) -> int:
        """Size of the group dimension"""
        return self.original_shape[self.group_axis]

    @property
    def num_groups(self) -> int:
        """Number of groups"""
        return math.ceil(self.group_axis_size / self.group_size)

    @property
    def pad_size(self) -> int:
        """Pad size of the grouped original data"""
        if self.group_axis_size % self.group_size != 0:
            return self.group_size - (self.group_axis_size % self.group_size)
        return 0


class GFPTensor(GFPTensorBase):
    """
    Elastix Group Floating Point (GFP) tensor
    """

    def __init__(
        self,
        original_shape: torch.Size,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
        *,
        mantissa_data: torch.Tensor | None = None,
        exp_data: torch.Tensor | None = None,
        sign_data: torch.Tensor | None = None,
        original_data: torch.Tensor | None = None,
        gfp_data: "GFPTensor" | None = None,
    ) -> None:
        super().__init__(original_shape, group_axis, group_size, dtype)

        if (
            mantissa_data is not None
            and exp_data is not None
            and (sign_data is not None or self.dtype.mantissa_signed)
        ):
            self.mantissa_data = mantissa_data
            self.exp_data = exp_data
            self.sign_data = sign_data
        elif original_data is not None:
            self.mantissa_data, self.exp_data, self.sign_data = (
                self._quantize_from_float(original_data)
            )
        elif gfp_data is not None:
            self.mantissa_data, self.exp_data, self.sign_data = (
                self._normalize_from_gfp(gfp_data)
            )
        else:
            raise ValueError("Invalid initialization parameters")

        self._verify()

    def __getitem__(self, key: slice | int | tuple[slice | int, ...]) -> "GFPTensor":
        """Get a slice of the GFP tensor"""
        slices = list(key) if isinstance(key, tuple) else [key]
        if len(slices) != self.original_ndim:
            raise ValueError(
                f"Invalid key length: {len(slices)} != {self.original_ndim}"
            )

        original_shape = []
        for axis, axis_slice in enumerate(slices):
            if isinstance(axis_slice, slice):
                start = axis_slice.start if axis_slice.start is not None else 0
                stop = (
                    axis_slice.stop
                    if axis_slice.stop is not None
                    else self.original_shape[axis]
                )
                original_shape.append(stop - start)
            elif isinstance(axis_slice, int):
                original_shape.append(1)
            else:
                raise ValueError(f"Invalid key type: {type(axis_slice)}")

        slices = self.get_grouped_slices(slices)
        m = self.mantissa_data[tuple(slices)]
        s = self.sign_data[tuple(slices)] if self.sign_data is not None else None

        slices[-1] = slice(0, 1, 1)
        e = self.exp_data[tuple(slices)]

        return GFPTensor(
            original_shape=torch.Size(original_shape),
            group_axis=self.group_axis,
            group_size=self.group_size,
            dtype=self.dtype,
            mantissa_data=m,
            exp_data=e,
            sign_data=s,
        )

    def __setitem__(
        self, key: slice | int | tuple[slice | int, ...], value: "GFPTensor"
    ):
        """Set a slice of the GFP tensor"""
        slices = list(key) if isinstance(key, tuple) else [key]
        if len(slices) != self.original_ndim:
            raise ValueError(
                f"Invalid key length: {len(slices)} != {self.original_ndim}"
            )

        if self.group_axis != value.group_axis:
            raise ValueError(
                f"Group axis mismatch - expected: {self.group_axis}, got: {value.group_axis}"
            )
        if self.group_size != value.group_size:
            raise ValueError(
                f"Group size mismatch - expected: {self.group_size}, got: {value.group_size}"
            )
        if self.dtype != value.dtype:
            raise ValueError(
                f"Data type mismatch - expected: {self.dtype}, got: {value.dtype}"
            )

        slices = self.get_grouped_slices(slices)
        self.mantissa_data[tuple(slices)] = value.mantissa_data
        if self.sign_data is not None and value.sign_data is not None:
            self.sign_data[tuple(slices)] = value.sign_data

        slices[-1] = slice(0, 1, 1)
        self.exp_data[tuple(slices)] = value.exp_data

        self._verify()

    def copy(self) -> "GFPTensor":
        return GFPTensor(
            self.original_shape,
            self.group_axis,
            self.group_size,
            self.dtype,
            mantissa_data=self.mantissa_data.clone(),
            exp_data=self.exp_data.clone(),
            sign_data=self.sign_data.clone() if self.sign_data is not None else None,
        )

    def _verify(self):
        """
        Verify the GFP tensor for correctness and validity.
        """
        super()._verify()

        # 1. Check group dimension and shape consistency
        if self.mantissa_data.shape != self.mantissa_shape:
            raise ValueError(
                f"mantissa_data shape mismatch - expected: {self.mantissa_shape}, got: {self.mantissa_data.shape}"
            )

        if self.exp_data.shape != self.exp_shape:
            raise ValueError(
                f"exp_data shape mismatch - expected: {self.exp_shape}, got: {self.exp_data.shape}"
            )

        if not self.dtype.mantissa_signed:
            if self.sign_data is None:
                raise ValueError("sign_data is required for unsigned mantissa")
            elif self.sign_data.shape != self.sign_shape:
                raise ValueError(
                    f"sign_data shape mismatch - expected: {self.sign_shape}, got: {self.sign_data.shape}"
                )
        else:
            if self.sign_data is not None:
                raise ValueError("sign_data is not allowed for signed mantissa")

        # 2. Check value ranges
        # Mantissa should be in [0, top_mantissa]
        if (self.mantissa_data < self.dtype.bottom_mantissa).any() or (
            self.mantissa_data > self.dtype.top_mantissa
        ).any():
            raise ValueError(
                f"mantissa_data out of range [{self.dtype.bottom_mantissa}, {self.dtype.top_mantissa}]"
                f", min value: {self.mantissa_data.min()}, max value: {self.mantissa_data.max()}"
            )

        # Exponent should be in [0, top_exp]
        if (self.exp_data < self.dtype.bottom_exp).any() or (
            self.exp_data > self.dtype.top_exp
        ).any():
            raise ValueError(
                f"exp_data out of range [0, {self.dtype.top_exp}]"
                f", min value: {self.exp_data.min()}, max value: {self.exp_data.max()}"
            )

        # Sign should be in {-1, 0, 1}
        if not self.dtype.mantissa_signed:
            valid_signs = torch.tensor(
                [-1, 0, 1], dtype=self.sign_data.dtype, device=self.sign_data.device
            )
            if not torch.isin(self.sign_data, valid_signs).all():
                unique_signs = torch.unique(self.sign_data)
                raise ValueError(
                    f"sign_data contains invalid values. Found: {unique_signs.tolist()}, expected: [-1, 0, 1]"
                )

    def _quantize_from_float(
        self, original_data: torch.Tensor
    ) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor | None]:
        """
        Quantize from float to GFP format. This procedure should always happen
        in the host. For example, pre-quantize the weights before sending them
        to the FPGA.
        """
        x = original_data

        # Transpose the group dimension to the last dimension
        if self.group_axis != -1:
            x = x.transpose(-1, self.group_axis)

        # Pad if needed to make last dimension divisible by group_size
        if self.pad_size > 0:
            logging.warning(
                "Group dimension size doesn't match group_size and requires padding: "
                f"group_axis_size: {self.group_axis_size}, group_size: {self.group_size}"
            )
            x = F.pad(x, (0, self.pad_size))

        # Separate the last dimension into (num_groups, group_size)
        x = x.unflatten(-1, (self.num_groups, self.group_size))

        # Find maximal value in each group and clamp to dynamic range
        x_max = x.abs().max(-1, keepdim=True)[0]
        x_max = x_max.clamp(min=2**self.dtype.bottom_exp_biased)

        # Calculate shared exponent for each group
        # The x_scale is introduced for two purposes:
        #   1. Because the range of mantissa should be [0, 2^mantissa_bits - 1],
        #      x_scale can avoid mantissa overflow to 2^mantissa_bits.
        #   2. When x_max is power of 2, e should be log2(x_max) + 1 instead of
        #      log2(x_max). x_scale can avoid these cases.
        x_scale = (self.dtype.top_mantissa + 1) / self.dtype.top_mantissa
        e = (
            (x_max * x_scale).log2().ceil()
            - self.dtype.effective_mantissa_bits
            + self.dtype.exp_bias
        )
        e = e.clamp(min=self.dtype.bottom_exp)
        e = clamp_with_logging(
            e.int(),
            max=self.dtype.top_exp,
            prefix="exponent quant",
        )

        # Calculate mantissa data
        scales = 2.0 ** (e - self.dtype.exp_bias)
        m = (x / scales).round()
        m = m.abs() if not self.dtype.mantissa_signed else m
        m = clamp_with_logging(
            m.int(),
            min=self.dtype.bottom_mantissa,
            max=self.dtype.top_mantissa,
            prefix="mantissa quant",
        )

        # Calculate sign data
        s = x.sign().int() if not self.dtype.mantissa_signed else None

        return m, e, s

    def _normalize_from_gfp(
        self, gfp_data: "GFPTensor"
    ) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor | None]:
        """
        Re-quantize the GFP data to a different GFP data with the given config.
        This procedure should happen in the FPGA, thus any operation apart from
        multiplcation, addition, and bit shifting should be avoided. This
        procedure always loses precision as we often downscale the mantissa to
        reduce its bit width.
        """
        if gfp_data.group_axis != -1 or gfp_data.group_size != 1:
            raise ValueError(
                "Currently, the normalization only supports group_axis = -1 and group_size = 1"
            )

        m = gfp_data.mantissa_data.squeeze(-1)
        e = gfp_data.exp_data.squeeze(-1) - gfp_data.dtype.exp_bias
        s = gfp_data.sign_data.squeeze(-1) if gfp_data.sign_data is not None else None

        # Transpose the group dimension to the last dimension
        if self.group_axis != -1:
            m = m.transpose(-1, self.group_axis)
            e = e.transpose(-1, self.group_axis)
            if s is not None:
                s = s.transpose(-1, self.group_axis)

        # Pad if needed to make last dimension divisible by group_size
        if self.pad_size > 0:
            logging.warning(
                "Group dimension size doesn't match group_size and requires padding: "
                f"group_axis_size: {self.group_axis_size}, group_size: {self.group_size}"
            )
            m = F.pad(m, (0, self.pad_size))
            e = F.pad(e, (0, self.pad_size))
            if s is not None:
                s = F.pad(s, (0, self.pad_size))

        # Separate the last dimension into (num_groups, group_size)
        m = m.unflatten(-1, (self.num_groups, self.group_size))
        e = e.unflatten(-1, (self.num_groups, self.group_size))
        if s is not None:
            s = s.unflatten(-1, (self.num_groups, self.group_size))

        # Find the largest exponent of each group and calculate exponent
        # difference, and scale mantissa by 2^exp_diff to align them to the
        # largest exponent
        e_shared = e.max(-1, keepdim=True)[0]
        e_diff = e_shared - e
        m = m >> e_diff

        # Calculate how many bits to shift left/right to fit m_max into output
        # mantissa_bits. We should limit e_shift to avoid exp overflow and
        # underflow.
        #
        # On hardware, this log2 operation can be efficiently implemented by
        # detecting how many leading zeros are there in the mantissa
        m_max = m.abs().max(-1, keepdim=True)[0]
        e_shift = (m_max + 1).log2().ceil().int() - self.dtype.effective_mantissa_bits
        e_shift = e_shift.clamp(
            min=self.dtype.bottom_exp_biased - e_shared,
            max=self.dtype.top_exp_biased - e_shared,
        )

        # Update exponent
        e = e_shared + e_shift + self.dtype.exp_bias
        e = clamp_with_logging(
            e, min=self.dtype.bottom_exp, max=self.dtype.top_exp, prefix="exponent norm"
        )

        # Shift mantissa left/right to fit m_max into output mantissa_bits
        m = torch.where(e_shift > 0, m >> e_shift, m << -e_shift)
        m = clamp_with_logging(
            m,
            min=self.dtype.bottom_mantissa,
            max=self.dtype.top_mantissa,
            prefix="mantissa norm",
        )

        return m, e, s

    def dequantize(self) -> torch.Tensor:
        """
        Dequantize the quantized data to original data. Similar to the quantize
        procedure, this should always happen in the host.
        """
        # Convert mantissa to float
        scales = 2.0 ** (self.exp_data - self.dtype.exp_bias)
        x = self.mantissa_data_signed * scales

        # Revert group reshaping
        x = x.flatten(-2, -1)

        # Trim padding if needed
        if self.pad_size > 0:
            x = x[..., : self.group_axis_size]

        # Transpose back to original shape
        if self.group_axis != -1:
            x = x.transpose(-1, self.group_axis)

        return x

    @property
    def mantissa_data_signed(self) -> torch.Tensor:
        """Mantissa data with sign, i.e., mantissa_data for signed mantissa,
        mantissa_data * sign_data for unsigned mantissa"""
        if self.sign_data is None:
            return self.mantissa_data
        else:
            return self.mantissa_data * self.sign_data


class GFPGemm:
    """
    Elastix Group Floating Point (GFP) GEMM operator
    """

    def __init__(
        self,
        accum_dtype: GFPDataType,
        product_dtype: GFPDataType,
    ) -> None:
        self.accum_dtype = accum_dtype
        self.product_dtype = product_dtype

    def __call__(
        self,
        lhs: GFPTensor,
        rhs: GFPTensor,
    ) -> GFPTensor:
        """
        Emulate the GEMM operation between two GFP tensors.

        Symbols:
        B = Batch
        C = Columns (reduction dimension)
        R = Rows
        G = Group size
        N = Number of groups (C / G)

        Input dimensions:
        Original LHS: [B, C]
        Quantized LHS: mantissa [B, N, G], exponent [B, N, 1], sign [B, N, G]
        Original RHS: [R, C]
        Quantized RHS: mantissa [R, N, G], exponent [R, N, 1], sign [R, N, G]

        Output dimensions:
        Result (G = 1): mantissa [B, R, 1], exponent [B, R, 1], sign [B, R, 1]
        """
        self._verify(lhs, rhs)

        # Calculate dot product along the group dimension
        # [B, N, G] * [R, N, G] = [B, R, N]
        m = torch.einsum(
            "bng, rng -> brn",
            lhs.mantissa_data_signed,
            rhs.mantissa_data_signed,
        )
        m = clamp_with_logging(
            m,
            min=self.product_dtype.bottom_mantissa_signed,
            max=self.product_dtype.top_mantissa,
            prefix="mantissa product",
        )

        # Permute exponents for broadcasting and calculate result exponent
        # LHS: [B, N, 1] -> [B, 1, N]
        # RHS: [R, N, 1] -> [1, R, N]
        # Result: [B, R, N]
        e = lhs.exp_data.permute(0, 2, 1) + rhs.exp_data.permute(2, 0, 1)
        e = clamp_with_logging(
            e,
            min=self.product_dtype.bottom_exp,
            max=self.product_dtype.top_exp,
            prefix="exponent product",
        )

        # Find the largest exponent for each [B, R] position across all N groups
        # and calculate exponent difference for each group, scale mantissa
        # by 2^e_diff to align them to the largest exponent, and accumulate
        # along the N dimension
        #
        # On hardware, we actually don't need to materialize the e_min; instead,
        # we can finish the accumulation with an adder-tree and do the shifting
        # before each addition.
        e_shared = e.max(-1, keepdim=True)[0]  # [B, R, 1]
        e_diff = e_shared - e  # [B, R, N]
        m = (m >> e_diff).sum(-1)  # [B, R]

        # Calculate the final results
        s = m.sign().unsqueeze(-1) if not self.accum_dtype.mantissa_signed else None

        m = (
            m.abs().unsqueeze(-1)
            if not self.accum_dtype.mantissa_signed
            else m.unsqueeze(-1)
        )
        m = clamp_with_logging(
            m,
            min=self.accum_dtype.bottom_mantissa,
            max=self.accum_dtype.top_mantissa,
            prefix="mantissa accum",
        )

        e = (
            e_shared
            - lhs.dtype.exp_bias
            - rhs.dtype.exp_bias
            + self.accum_dtype.exp_bias
        )
        e = clamp_with_logging(
            e,
            min=self.accum_dtype.bottom_exp,
            max=self.accum_dtype.top_exp,
            prefix="exponent accum",
        )

        return GFPTensor(
            original_shape=lhs.original_shape[:-1] + rhs.original_shape[1:],
            group_axis=-1,
            group_size=1,
            dtype=self.accum_dtype,
            mantissa_data=m,
            exp_data=e,
            sign_data=s,
        )

    def _verify(self, lhs: GFPTensor, rhs: GFPTensor):
        """
        Verify the GEMM operation for correctness and validity.
        """
        if lhs.original_ndim != 2 or rhs.original_ndim != 2:
            raise ValueError(
                f"Original dimension must be 2, got {lhs.original_ndim} and {rhs.original_ndim}"
            )

        if lhs.original_shape[1] != rhs.original_shape[0]:
            raise ValueError(
                f"Columns dimension mismatch: {lhs.original_shape[1]} != {rhs.original_shape[0]}"
            )

        if lhs.group_size != rhs.group_size:
            raise ValueError(
                f"Group size mismatch: {lhs.group_size} != {rhs.group_size}"
            )

        if lhs.group_axis not in (1, -1) or rhs.group_axis not in (0, -2):
            raise ValueError(
                f"Group dimension must be 1/-1 and 0/-2, got {lhs.group_axis} and {rhs.group_axis}"
            )


class GFPElmwiseAdd:
    """
    Elastix Group Floating Point (GFP) element-wise addition operator
    """

    def __init__(self, output_dtype: GFPDataType) -> None:
        self.output_dtype = output_dtype

    def __call__(self, lhs: GFPTensor, rhs: GFPTensor) -> GFPTensor:
        """
        Emulate the GFP element-wise addition operation between two GFP tensors.
        """
        self._verify(lhs, rhs)

        lhs_e = lhs.exp_data - lhs.dtype.exp_bias
        rhs_e = rhs.exp_data - rhs.dtype.exp_bias
        e_shared = torch.max(lhs_e, rhs_e)

        lhs_e_diff = e_shared - lhs_e
        rhs_e_diff = e_shared - rhs_e

        lhs_m = lhs.mantissa_data >> lhs_e_diff
        rhs_m = rhs.mantissa_data >> rhs_e_diff

        if lhs.sign_data is not None and rhs.sign_data is not None:
            m = lhs_m * lhs.sign_data + rhs_m * rhs.sign_data
        else:
            m = lhs_m + rhs_m

        s = m.sign() if not self.output_dtype.mantissa_signed else None
        m = m.abs() if not self.output_dtype.mantissa_signed else m
        m = clamp_with_logging(
            m,
            min=self.output_dtype.bottom_mantissa,
            max=self.output_dtype.top_mantissa,
            prefix="mantissa add",
        )

        e = e_shared + self.output_dtype.exp_bias
        e = clamp_with_logging(
            e,
            min=self.output_dtype.bottom_exp,
            max=self.output_dtype.top_exp,
            prefix="exponent add",
        )

        return GFPTensor(
            original_shape=lhs.original_shape,
            group_axis=lhs.group_axis,
            group_size=lhs.group_size,
            dtype=self.output_dtype,
            mantissa_data=m,
            exp_data=e,
            sign_data=s,
        )

    def _verify(self, lhs: GFPTensor, rhs: GFPTensor):
        """
        Verify the GFP element-wise addition operation for correctness and validity.
        """
        if lhs.original_shape != rhs.original_shape:
            raise ValueError(
                f"Original shape mismatch: {lhs.original_shape} != {rhs.original_shape}"
            )

        if lhs.group_axis != rhs.group_axis:
            raise ValueError(
                f"Group dimension mismatch: {lhs.group_axis} != {rhs.group_axis}"
            )

        if lhs.group_size != rhs.group_size:
            raise ValueError(
                f"Group size mismatch: {lhs.group_size} != {rhs.group_size}"
            )


class GFPGemmTiled(GFPGemm):
    """
    Elastix Group Floating Point (GFP) GEMM operator with tiling
    """

    def __init__(
        self,
        accum_dtype: GFPDataType,
        product_dtype: GFPDataType,
        batch_buffer_size: int,
        col_buffer_size: int,
        row_buffer_size: int,
        batch_num_tiles: int,
        col_num_tiles: int,
        row_num_tiles: int,
    ) -> None:
        super().__init__(accum_dtype, product_dtype)
        self.batch_buffer_size = batch_buffer_size
        self.col_buffer_size = col_buffer_size
        self.row_buffer_size = row_buffer_size
        self.batch_num_tiles = batch_num_tiles
        self.col_num_tiles = col_num_tiles
        self.row_num_tiles = row_num_tiles
        self.elmwise_add = GFPElmwiseAdd(accum_dtype)

        if (
            batch_buffer_size < batch_num_tiles
            or batch_buffer_size % batch_num_tiles != 0
        ):
            raise ValueError(
                f"Batch buffer size must be divisible by number of batch tiles, got {batch_buffer_size} and {batch_num_tiles}"
            )
        if col_buffer_size < col_num_tiles or col_buffer_size % col_num_tiles != 0:
            raise ValueError(
                f"Column buffer size must be divisible by number of column tiles, got {col_buffer_size} and {col_num_tiles}"
            )
        if row_buffer_size < row_num_tiles or row_buffer_size % row_num_tiles != 0:
            raise ValueError(
                f"Row buffer size must be divisible by number of row tiles, got {row_buffer_size} and {row_num_tiles}"
            )

        self.batch_tile_size = batch_buffer_size // batch_num_tiles
        self.col_tile_size = col_buffer_size // col_num_tiles
        self.row_tile_size = row_buffer_size // row_num_tiles

    def __call__(
        self,
        lhs: GFPTensor,
        rhs: GFPTensor,
    ) -> GFPTensor:
        """
        Emulate the tiled GEMM operation between two GFP tensors

        Symbols:
        B = Batch
        C = Columns (reduction dimension)
        R = Rows
        G = Group size
        N = Number of groups (C / G)

        Input dimensions:
        Original LHS: [B, C]
        Quantized LHS: mantissa [B, N, G], exponent [B, N, 1], sign [B, N, G]
        Original RHS: [R, C]
        Quantized RHS: mantissa [R, N, G], exponent [R, N, 1], sign [R, N, G]

        Output dimensions:
        Result (G = 1): mantissa [B, R, 1], exponent [B, R, 1], sign [B, R, 1]
        """
        self._verify(lhs, rhs)

        batch_size = lhs.original_shape[0]
        col_size = lhs.original_shape[1]
        row_size = rhs.original_shape[1]

        result_shape = torch.Size([batch_size, row_size])
        result = GFPTensor(
            original_shape=result_shape,
            group_axis=-1,
            group_size=1,
            dtype=self.accum_dtype,
            original_data=torch.zeros(result_shape),
        )

        for batch_buffer_start in range(0, batch_size, self.batch_buffer_size):
            for col_buffer_start in range(0, col_size, self.col_buffer_size):
                for row_buffer_start in range(0, row_size, self.row_buffer_size):
                    batch_buffer_stop = min(
                        batch_buffer_start + self.batch_buffer_size, batch_size
                    )
                    col_buffer_stop = min(
                        col_buffer_start + self.col_buffer_size, col_size
                    )
                    row_buffer_stop = min(
                        row_buffer_start + self.row_buffer_size, row_size
                    )

                    batch_buffer_slice = slice(batch_buffer_start, batch_buffer_stop)
                    col_buffer_slice = slice(col_buffer_start, col_buffer_stop)
                    row_buffer_slice = slice(row_buffer_start, row_buffer_stop)

                    # Emulate loading LHS, RHS, and current result from external memory to on-chip buffers
                    lhs_buffer = lhs[batch_buffer_slice, col_buffer_slice]
                    rhs_buffer = rhs[col_buffer_slice, row_buffer_slice]
                    result_buffer = result[batch_buffer_slice, row_buffer_slice]

                    # Emulate multi-tile GEMM operation against on-chip buffers
                    for batch_tile_start in range(
                        0, self.batch_buffer_size, self.batch_tile_size
                    ):
                        for col_tile_start in range(
                            0, self.col_buffer_size, self.col_tile_size
                        ):
                            for row_tile_start in range(
                                0, self.row_buffer_size, self.row_tile_size
                            ):
                                batch_tile_stop = (
                                    batch_tile_start + self.batch_tile_size
                                )
                                col_tile_stop = col_tile_start + self.col_tile_size
                                row_tile_stop = row_tile_start + self.row_tile_size

                                batch_tile_slice = slice(
                                    batch_tile_start, batch_tile_stop
                                )
                                col_tile_slice = slice(col_tile_start, col_tile_stop)
                                row_tile_slice = slice(row_tile_start, row_tile_stop)

                                # Emulate loading LHS, RHS, and current result from on-chip buffers to GEMM engine
                                lhs_tile = lhs_buffer[batch_tile_slice, col_tile_slice]
                                rhs_tile = rhs_buffer[col_tile_slice, row_tile_slice]
                                result_tile = result_buffer[
                                    batch_tile_slice, row_tile_slice
                                ]

                                # Emulate GEMM operation between LHS and RHS
                                partial_tile = super().__call__(lhs_tile, rhs_tile)

                                # Emulate accumulation of current result with partial result
                                result_tile = self.elmwise_add(
                                    result_tile, partial_tile
                                )

                                # Emulate storing the partial result back to on-chip buffers
                                result_buffer[batch_tile_slice, row_tile_slice] = (
                                    result_tile
                                )

                    # Emulate storing the partial result back to external memory
                    result[batch_buffer_slice, row_buffer_slice] = result_buffer

        return result

    def _verify(self, lhs: GFPTensor, rhs: GFPTensor):
        """
        Verify the tiled GEMM operation for correctness and validity.
        """
        super()._verify(lhs, rhs)

        if self.col_tile_size != lhs.group_size:
            raise ValueError(
                f"Column tile size must equal to group size, got {self.col_tile_size} and {lhs.group_size}"
            )
