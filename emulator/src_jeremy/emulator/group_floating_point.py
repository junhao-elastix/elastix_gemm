from __future__ import annotations

import copy
import logging
import math

import numpy as np
import torch
import torch.nn.functional as F


def clamp_with_logging(
    x: torch.Tensor,
    min: float | None = None,
    max: float | None = None,
    prefix: str = "",
) -> torch.Tensor:
    """Clamp tensor values to a range with overflow/underflow logging.

    Args:
        x: Input tensor to clamp.
        min: Minimum value. If None, no lower bound is applied.
        max: Maximum value. If None, no upper bound is applied.
        prefix: Prefix string for log messages.

    Returns:
        Clamped tensor with values in [min, max].
    """
    if min is not None and (x < min).any():
        logging.warning(f"{prefix} underflow clamping detected: {x[x < min]}")
    if max is not None and (x > max).any():
        logging.error(f"{prefix} overflow clamping detected: {x[x > max]}")
    return x.clamp(min, max)


def torch_dtype_for_bits(bits: int, signed: bool) -> torch.dtype:
    """Return the appropriate PyTorch dtype for the given bit width.

    Args:
        bits: Number of bits required.
        signed: Whether the dtype should be signed.

    Returns:
        PyTorch dtype that can hold the specified number of bits.

    Raises:
        ValueError: If bits is greater than 64.
    """
    if bits <= 8:
        return torch.int8 if signed else torch.uint8
    elif bits <= 16:
        return torch.int16 if signed else torch.uint16
    elif bits <= 32:
        return torch.int32 if signed else torch.uint32
    elif bits <= 64:
        return torch.int64 if signed else torch.uint64
    else:
        raise ValueError(f"Invalid bits: {bits}")


def np_dtype_for_bits(bits: int, signed: bool) -> np.dtype:
    """Return the appropriate NumPy dtype for the given bit width.

    Args:
        bits: Number of bits required.
        signed: Whether the dtype should be signed.

    Returns:
        NumPy dtype that can hold the specified number of bits.

    Raises:
        ValueError: If bits is greater than 64.
    """
    if bits <= 8:
        return np.dtype(np.int8) if signed else np.dtype(np.uint8)
    elif bits <= 16:
        return np.dtype(np.int16) if signed else np.dtype(np.uint16)
    elif bits <= 32:
        return np.dtype(np.int32) if signed else np.dtype(np.uint32)
    elif bits <= 64:
        return np.dtype(np.int64) if signed else np.dtype(np.uint64)
    else:
        raise ValueError(f"Invalid bits: {bits}")


class GFPDataType:
    """Elastix Group Floating Point (GFP) data type.

    If mantissa_signed is True, the mantissa is signed; otherwise, it is
    unsigned and we use an extra sign bit to represent the sign.
    """

    def __init__(
        self,
        mantissa_bits: int,
        exp_bits: int,
        exp_bias: int | None = None,
        mantissa_signed: bool = True,
        verify: bool = False,
    ) -> None:
        """Initialize GFP data type configuration.

        Args:
            mantissa_bits: Number of bits for mantissa representation.
            exp_bits: Number of bits for exponent representation.
            exp_bias: Exponent bias. If None, defaults to 2^(exp_bits-1).
            mantissa_signed: If True, mantissa is signed; otherwise unsigned with separate sign bit.
            verify: If True, verify configuration validity on initialization.
        """
        self.mantissa_bits: int = mantissa_bits
        self.exp_bits: int = exp_bits
        # IEEE standard: bias = 2^(exp_bits-1) - 1 (e.g., 127 for 8-bit, 15 for 5-bit)
        self.exp_bias: int = exp_bias if exp_bias is not None else 2 ** (exp_bits - 1) - 1
        self.mantissa_signed: bool = mantissa_signed

        if verify:
            self.verify()

    def __str__(self) -> str:
        """Return string representation of GFP data type."""
        return (
            f"GFPDataType("
            f"bits={self.mantissa_bits}m/{self.exp_bits}e"
            f"{'/1s' if not self.mantissa_signed else ''}, "
            f"exp_bias={self.exp_bias})"
        )

    def __eq__(self, value: object) -> bool:
        """Check equality with another GFPDataType instance.

        Args:
            value: Object to compare with.

        Returns:
            True if all fields match, False otherwise.
        """
        if not isinstance(value, GFPDataType):
            return False
        return (
            self.mantissa_bits == value.mantissa_bits
            and self.exp_bits == value.exp_bits
            and self.exp_bias == value.exp_bias
            and self.mantissa_signed == value.mantissa_signed
        )

    def verify(self):
        """Verify the GFP type for correctness and validity."""
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
        """Effective mantissa bits.

        Returns mantissa_bits - 1 for signed mantissa, mantissa_bits for
        unsigned mantissa.
        """
        if self.mantissa_signed:
            return self.mantissa_bits - 1
        else:
            return self.mantissa_bits

    @property
    def top_exp(self) -> int:
        """Top exponent value, i.e., 2**exp_bits - 1."""
        return 2**self.exp_bits - 1

    @property
    def top_exp_biased(self) -> int:
        """Top exponent value biased by exp_bias, i.e., top_exp - exp_bias."""
        return self.top_exp - self.exp_bias

    @property
    def bottom_exp(self) -> int:
        """Bottom exponent value, i.e., 0."""
        return 0

    @property
    def bottom_exp_biased(self) -> int:
        """Bottom exponent value biased by exp_bias, i.e., -exp_bias."""
        return self.bottom_exp - self.exp_bias

    @property
    def top_mantissa(self) -> int:
        """Top mantissa value, i.e., 2**effective_mantissa_bits - 1."""
        return 2**self.effective_mantissa_bits - 1

    @property
    def bottom_mantissa(self) -> int:
        """Bottom mantissa value.

        Returns -2**effective_mantissa_bits for signed mantissa, 0 for
        unsigned mantissa.
        """
        if self.mantissa_signed:
            return -(2**self.effective_mantissa_bits)
        else:
            return 0

    @property
    def bottom_mantissa_signed(self) -> int:
        """Bottom signed mantissa value.

        Returns bottom_mantissa for signed mantissa, -top_mantissa for
        unsigned mantissa.
        """
        if self.mantissa_signed:
            return self.bottom_mantissa
        else:
            return -self.top_mantissa

    @property
    def top_val(self) -> float:
        """Maximum value, i.e., 2**top_exp_biased * top_mantissa."""
        return 2**self.top_exp_biased * self.top_mantissa

    @property
    def bottom_val(self) -> float:
        """Non-zero minimum value, i.e., 2**top_exp_biased * bottom_mantissa_signed."""
        return 2**self.top_exp_biased * self.bottom_mantissa_signed

    @property
    def mantissa_np_dtype(self) -> np.dtype:
        """NumPy dtype for mantissa data."""
        return np_dtype_for_bits(self.mantissa_bits, self.mantissa_signed)

    @property
    def mantissa_torch_dtype(self) -> torch.dtype:
        """PyTorch dtype for mantissa data."""
        return torch_dtype_for_bits(self.mantissa_bits, self.mantissa_signed)

    @property
    def exp_np_dtype(self) -> np.dtype:
        """NumPy dtype for exponent data."""
        return np_dtype_for_bits(self.exp_bits, False)

    @property
    def exp_torch_dtype(self) -> torch.dtype:
        """PyTorch dtype for exponent data."""
        return torch_dtype_for_bits(self.exp_bits, False)


class GFPTensorBase:
    """Elastix Group Floating Point (GFP) tensor base class."""

    def __init__(
        self,
        original_shape: torch.Size,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
    ) -> None:
        """Initialize GFP tensor base configuration.

        Args:
            original_shape: Shape of the tensor before quantization.
            group_axis: Axis along which grouping is performed.
            group_size: Number of elements in each group.
            dtype: GFP data type configuration.
        """
        self.original_shape: torch.Size = original_shape
        self.group_axis: int = group_axis
        self.group_size: int = group_size
        self.dtype: GFPDataType = dtype

    def __str__(self) -> str:
        """Return string representation of GFP tensor base."""
        return (
            f"GFPTensor("
            f"original_shape={list(self.original_shape)}, "
            f"group_axis={self.group_axis}, "
            f"group_size={self.group_size}, "
            f"dtype={self.dtype})"
        )

    def __eq__(self, value: object) -> bool:
        """Check equality with another GFPTensorBase instance.

        Args:
            value: Object to compare with.

        Returns:
            True if all configuration fields match, False otherwise.
        """
        if not isinstance(value, GFPTensorBase):
            return False
        return (
            self.original_shape == value.original_shape
            and self.group_axis == value.group_axis
            and self.group_size == value.group_size
            and self.dtype == value.dtype
        )

    def verify(self):
        """Verify the GFP configuration for correctness and validity."""
        if self.group_size <= 0:
            raise ValueError(f"Invalid group_size: {self.group_size}")

        if (
            self.group_axis >= self.original_ndim
            or self.group_axis < -self.original_ndim
        ):
            raise ValueError(
                f"Invalid group_axis {self.group_axis} for tensor with {self.original_ndim} dimensions"
            )

    def get_grouped_slices(
        self, slices: tuple[slice | int, ...]
    ) -> tuple[slice | int, ...]:
        """Convert slices on original shape to slices on grouped data.

        Args:
            slices: Tuple of slices/indices for the original shape.

        Returns:
            Tuple of slices/indices for the grouped data shape.

        Raises:
            ValueError: If slices are incompatible with group configuration.
        """
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

        slices_list = list(slices)
        slices_list[self.group_axis] = slices_list[-1]
        slices_list = slices_list[:-1] + [group_idx_axis_slice, group_axis_slice]
        return tuple(slices_list)

    @property
    def original_ndim(self) -> int:
        """Rank of the original data."""
        return len(self.original_shape)

    @property
    def grouped_ndim(self) -> int:
        """Rank of the grouped data."""
        return self.original_ndim + 1

    @property
    def grouped_shape(self) -> torch.Size:
        """Shape of the grouped data."""
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
        """Shape of the mantissa data."""
        return self.grouped_shape

    @property
    def exp_shape(self) -> torch.Size:
        """Shape of the exponent data."""
        return self.grouped_shape[:-1] + (1,)

    @property
    def sign_shape(self) -> torch.Size:
        """Shape of the sign data."""
        return self.grouped_shape

    @property
    def group_axis_size(self) -> int:
        """Size of the group dimension."""
        return self.original_shape[self.group_axis]

    @property
    def num_groups(self) -> int:
        """Number of groups."""
        return math.ceil(self.group_axis_size / self.group_size)

    @property
    def pad_size(self) -> int:
        """Pad size of the grouped original data."""
        if self.group_axis_size % self.group_size != 0:
            return self.group_size - (self.group_axis_size % self.group_size)
        return 0

    @property
    def non_neg_group_axis(self) -> int:
        """Non-negative group axis."""
        return (
            self.group_axis
            if self.group_axis >= 0
            else self.group_axis + self.original_ndim
        )


class GFPTensor(GFPTensorBase):
    """Elastix Group Floating Point (GFP) tensor.

    Attributes:
        original_shape: The original shape of the tensor before quantization.
        group_axis: The axis along which the tensor is grouped.
        group_size: The size of the group.
        dtype: The data type of the tensor.
        mantissa_data: The mantissa data of the tensor.
        exp_data: The exponent data of the tensor.
        sign_data: The sign data of the tensor.
    """

    def __init__(
        self,
        original_shape: torch.Size,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
        mantissa_data: torch.Tensor,
        exp_data: torch.Tensor,
        sign_data: torch.Tensor | None = None,
        verify: bool = False,
    ) -> None:
        """Initialize GFP tensor with quantized data.

        Args:
            original_shape: Shape of the tensor before quantization.
            group_axis: Axis along which grouping is performed.
            group_size: Number of elements in each group.
            dtype: GFP data type configuration.
            mantissa_data: Quantized mantissa values.
            exp_data: Shared exponent values for each group.
            sign_data: Sign data (required for unsigned mantissa only).
            verify: If True, verify tensor validity on initialization.

        Raises:
            ValueError: If sign_data is missing for unsigned mantissa.
        """
        super().__init__(original_shape, group_axis, group_size, dtype)

        if sign_data is None and not self.dtype.mantissa_signed:
            raise ValueError("sign_data is required for unsigned mantissa")

        self.mantissa_data = mantissa_data
        self.exp_data = exp_data
        self.sign_data = sign_data

        if verify:
            self.verify()

    def __getitem__(self, key: slice | int | tuple[slice | int, ...]) -> "GFPTensor":
        """Get a slice of the GFP tensor.

        Args:
            key: Slice or index for each dimension.

        Returns:
            New GFPTensor containing the sliced data.

        Raises:
            ValueError: If key length exceeds tensor dimensions or slice is invalid.
        """
        slices = list(key) if isinstance(key, tuple) else [key]
        if len(slices) > self.original_ndim:
            raise ValueError(
                f"Invalid key length: {len(slices)} != {self.original_ndim}"
            )
        if len(slices) < self.original_ndim:
            slices = slices + [slice(None)] * (self.original_ndim - len(slices))

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

        grouped_slices = self.get_grouped_slices(tuple(slices))
        m = self.mantissa_data[grouped_slices]
        s = self.sign_data[grouped_slices] if self.sign_data is not None else None

        grouped_slices = grouped_slices[:-1] + (slice(0, 1, 1),)
        e = self.exp_data[grouped_slices]

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
        """Set a slice of the GFP tensor.

        Args:
            key: Slice or index for each dimension.
            value: GFPTensor to assign to the slice.

        Raises:
            ValueError: If key is invalid or value has incompatible configuration.
        """
        slices = list(key) if isinstance(key, tuple) else [key]
        if len(slices) > self.original_ndim:
            raise ValueError(
                f"Invalid key length: {len(slices)} != {self.original_ndim}"
            )
        if len(slices) < self.original_ndim:
            slices = slices + [slice(None)] * (self.original_ndim - len(slices))

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

        grouped_slices = self.get_grouped_slices(tuple(slices))
        self.mantissa_data[grouped_slices] = value.mantissa_data
        if self.sign_data is not None and value.sign_data is not None:
            self.sign_data[grouped_slices] = value.sign_data

        grouped_slices = grouped_slices[:-1] + (slice(0, 1, 1),)
        self.exp_data[grouped_slices] = value.exp_data

    def copy(self) -> "GFPTensor":
        """Create a deep copy of this GFP tensor.

        Returns:
            New GFPTensor with cloned data.
        """
        return GFPTensor(
            original_shape=copy.copy(self.original_shape),
            group_axis=self.group_axis,
            group_size=self.group_size,
            dtype=copy.copy(self.dtype),
            mantissa_data=self.mantissa_data.clone(),
            exp_data=self.exp_data.clone(),
            sign_data=self.sign_data.clone() if self.sign_data is not None else None,
        )

    def copy_from(self, other: "GFPTensor"):
        """Copy data from another GFP tensor into this one.

        Args:
            other: Source GFPTensor to copy from.
        """
        self.original_shape = copy.copy(other.original_shape)
        self.group_axis = other.group_axis
        self.group_size = other.group_size
        self.dtype = copy.copy(other.dtype)
        self.mantissa_data = other.mantissa_data.clone()
        self.exp_data = other.exp_data.clone()
        self.sign_data = (
            other.sign_data.clone() if other.sign_data is not None else None
        )

    def verify(self):
        """Verify the GFP tensor for correctness and validity."""
        super().verify()

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

    @classmethod
    def quantize_from_float(
        cls,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
        original_data: torch.Tensor,
    ) -> "GFPTensor":
        """Quantize floating-point tensor to GFP format.

        This procedure should always happen on the host (e.g., pre-quantize weights
        before sending to FPGA).

        Args:
            group_axis: Axis along which grouping is performed.
            group_size: Number of elements in each group.
            dtype: Target GFP data type configuration.
            original_data: Floating-point tensor to quantize.

        Returns:
            Quantized GFPTensor.
        """
        original_shape = original_data.shape

        obj = cls.__new__(cls)
        GFPTensorBase.__init__(
            obj,
            original_shape=original_shape,
            group_axis=group_axis,
            group_size=group_size,
            dtype=dtype,
        )

        x = original_data

        # Transpose the group dimension to the last dimension
        if obj.group_axis != -1:
            x = x.transpose(-1, obj.group_axis)

        # Pad if needed to make last dimension divisible by group_size
        if obj.pad_size > 0:
            logging.warning(
                "Group dimension size doesn't match group_size and requires padding: "
                f"group_axis_size: {obj.group_axis_size}, group_size: {obj.group_size}"
            )
            x = F.pad(x, (0, obj.pad_size))

        # Separate the last dimension into (num_groups, group_size)
        x = x.unflatten(-1, (obj.num_groups, obj.group_size))

        # Find maximal value in each group and clamp to dynamic range
        x_max = x.abs().max(-1, keepdim=True)[0]
        x_max = x_max.clamp(min=2**obj.dtype.bottom_exp_biased)

        # Calculate shared exponent for each group
        # The x_scale is introduced for two purposes:
        #   1. Because the range of mantissa should be [0, 2^mantissa_bits - 1],
        #      x_scale can avoid mantissa overflow to 2^mantissa_bits.
        #   2. When x_max is power of 2, e should be log2(x_max) + 1 instead of
        #      log2(x_max). x_scale can avoid these cases.
        x_scale = (obj.dtype.top_mantissa + 1) / obj.dtype.top_mantissa
        e = (
            (x_max * x_scale).log2().ceil()
            - obj.dtype.effective_mantissa_bits
            + obj.dtype.exp_bias
        )
        e = e.clamp(min=obj.dtype.bottom_exp)
        e = clamp_with_logging(
            e.int(),
            max=obj.dtype.top_exp,
            prefix="exponent quant",
        )

        # Calculate mantissa data
        scales = 2.0 ** (e - obj.dtype.exp_bias)
        m = (x / scales).round()
        m = m.abs() if not obj.dtype.mantissa_signed else m
        m = clamp_with_logging(
            m.int(),
            min=obj.dtype.bottom_mantissa,
            max=obj.dtype.top_mantissa,
            prefix="mantissa quant",
        )

        # Calculate sign data
        s = x.sign().int() if not obj.dtype.mantissa_signed else None

        obj.mantissa_data = m
        obj.exp_data = e
        obj.sign_data = s

        return obj

    @classmethod
    def normalize_from_gfp(
        cls,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
        gfp_data: "GFPTensor",
    ) -> "GFPTensor":
        """Re-quantize GFP tensor to different configuration.

        This procedure should happen on FPGA, so only multiplication, addition,
        and bit shifting are used. Precision is typically lost when downscaling
        mantissa bit width.

        Args:
            group_axis: Target group axis.
            group_size: Target group size.
            dtype: Target GFP data type configuration.
            gfp_data: Source GFP tensor to normalize.

        Returns:
            Normalized GFPTensor with new configuration.

        Raises:
            ValueError: If input doesn't have group_axis=-1 and group_size=1.
        """
        original_shape = gfp_data.original_shape

        obj = cls.__new__(cls)
        GFPTensorBase.__init__(
            obj,
            original_shape=original_shape,
            group_axis=group_axis,
            group_size=group_size,
            dtype=dtype,
        )

        if gfp_data.group_axis != -1 or gfp_data.group_size != 1:
            raise ValueError(
                "Currently, the normalization only supports group_axis = -1 and group_size = 1"
            )

        m = gfp_data.mantissa_data.squeeze(-1)
        e = gfp_data.exp_data.squeeze(-1) - gfp_data.dtype.exp_bias
        s = gfp_data.sign_data.squeeze(-1) if gfp_data.sign_data is not None else None

        # Transpose the group dimension to the last dimension
        if obj.group_axis != -1:
            m = m.transpose(-1, obj.group_axis)
            e = e.transpose(-1, obj.group_axis)
            if s is not None:
                s = s.transpose(-1, obj.group_axis)

        # Pad if needed to make last dimension divisible by group_size
        if obj.pad_size > 0:
            logging.warning(
                "Group dimension size doesn't match group_size and requires padding: "
                f"group_axis_size: {obj.group_axis_size}, group_size: {obj.group_size}"
            )
            m = F.pad(m, (0, obj.pad_size))
            e = F.pad(e, (0, obj.pad_size))
            if s is not None:
                s = F.pad(s, (0, obj.pad_size))

        # Separate the last dimension into (num_groups, group_size)
        m = m.unflatten(-1, (obj.num_groups, obj.group_size))
        e = e.unflatten(-1, (obj.num_groups, obj.group_size))
        if s is not None:
            s = s.unflatten(-1, (obj.num_groups, obj.group_size))

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
        e_shift = (m_max + 1).log2().ceil().int() - obj.dtype.effective_mantissa_bits
        e_shift = e_shift.clamp(
            min=obj.dtype.bottom_exp_biased - e_shared,
            max=obj.dtype.top_exp_biased - e_shared,
        )

        # Update exponent
        e = e_shared + e_shift + obj.dtype.exp_bias
        e = clamp_with_logging(
            e, min=obj.dtype.bottom_exp, max=obj.dtype.top_exp, prefix="exponent norm"
        )

        # Shift mantissa left/right to fit m_max into output mantissa_bits
        m = torch.where(e_shift > 0, m >> e_shift, m << -e_shift)
        m = clamp_with_logging(
            m,
            min=obj.dtype.bottom_mantissa,
            max=obj.dtype.top_mantissa,
            prefix="mantissa norm",
        )

        obj.mantissa_data = m
        obj.exp_data = e
        obj.sign_data = s

        return obj

    def dequantize(self) -> torch.Tensor:
        """Dequantize GFP tensor back to floating-point.

        Similar to quantization, this should always happen on the host.

        Returns:
            Floating-point tensor with original shape.
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

    def t_(self) -> GFPTensor:
        """Transpose the tensor in-place (2D tensors only).

        Since the group axis is already transposed to the last dimension,
        only metadata needs to be updated.

        Returns:
            Self after in-place transpose.

        Raises:
            ValueError: If tensor is not 2D.
        """
        if len(self.original_shape) != 2:
            raise ValueError("Only 2D tensors can be transposed.")

        self.group_axis = -1 if self.group_axis == -2 else -2
        self.original_shape = torch.Size(self.original_shape[::-1])

        return self

    def pad_to_block_sizes(self, block_sizes: tuple[int, ...]) -> GFPTensor:
        """Pad tensor to align with block sizes.

        Args:
            block_sizes: Block size for each dimension (must match original shape length).

        Returns:
            Original tensor if no padding needed, otherwise new padded GFPTensor.

        Raises:
            ValueError: If block_sizes length doesn't match shape or group axis
                block size is not divisible by group_size.
        """
        # copy the shape and turn into list of int
        shape = list(self.original_shape)

        if len(block_sizes) != len(shape):
            raise ValueError("Block sizes must have the same length as the shape")
        if block_sizes[self.group_axis] % self.group_size != 0:
            raise ValueError(
                f"Block size at dim={self.group_axis} must be divisible by group size."
                f"Got {block_sizes[self.group_axis]} and {self.group_size}"
            )

        shape[self.group_axis] += self.pad_size
        assert shape[self.group_axis] % self.group_size == 0

        pad_sizes = [-shape[i] % block_sizes[i] for i in range(len(shape))]
        shape = [shape[i] + pad_sizes[i] for i in range(len(shape))]

        if all(pad == 0 for pad in pad_sizes):
            # No padding needed
            return self

        # Now we know how much the original data should've been padded
        # Since the GFP data is transposed, we need to transpose our padding sizes
        if self.group_axis != -1:
            pad_sizes[self.group_axis], pad_sizes[-1] = (
                pad_sizes[-1],
                pad_sizes[self.group_axis],
            )

        # Divide the last dimension by group size and add a 0 for the group dimension
        # Note: We already verified that the last dimension is divisible by group size
        gfp_pad_sizes = pad_sizes[:-1] + [pad_sizes[-1] // self.group_size, 0]

        # We now know how much we want to pad each dimension of every tensor on the left by
        # To use F.pad, we need to reverse it and add 0s to the left so it becomes a right pad
        # [3, 1, 4, 0] -> [0, 0, 0, 4, 0, 1, 0, 3]
        # so we reverse the order, add 0s on the left, and finally flatten it
        pad_size_arg = [x for p in gfp_pad_sizes[::-1] for x in (0, p)]

        mantissa = F.pad(self.mantissa_data, pad_size_arg)
        exp = F.pad(self.exp_data, pad_size_arg)
        sign = (
            F.pad(self.sign_data, pad_size_arg) if self.sign_data is not None else None
        )

        return GFPTensor(
            original_shape=torch.Size(shape),
            group_axis=self.group_axis,
            group_size=self.group_size,
            mantissa_data=mantissa,
            exp_data=exp,
            sign_data=sign,
            dtype=self.dtype,
        )

    def block(
        self, block_shape: torch.Size, block_alignment: int | None = None
    ) -> BlockedGFPTensor:
        """Block the tensor into a blocked GFP tensor.

        Args:
            block_shape: Shape of each block.
            block_alignment: Optional alignment for mantissa and exponent data
                within each block (must be divisible by group_size).
        """
        return BlockedGFPTensor.block_from_raw(
            original_shape=self.original_shape,
            group_axis=self.group_axis,
            group_size=self.group_size,
            dtype=self.dtype,
            block_shape=block_shape,
            mantissa_data=self.mantissa_data,
            exp_data=self.exp_data,
            block_alignment=block_alignment,
        )

    @property
    def mantissa_data_signed(self) -> torch.Tensor:
        """Mantissa data with sign.

        Returns mantissa_data for signed mantissa, mantissa_data * sign_data
        for unsigned mantissa.
        """
        if self.sign_data is None:
            return self.mantissa_data
        else:
            return self.mantissa_data * self.sign_data


class BlockedGFPTensorBase(GFPTensorBase):
    """Base class for blocked GFP tensors with block-based storage layout."""

    def __init__(
        self,
        original_shape: torch.Size,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
        block_shape: torch.Size,
        block_alignment: int | None = None,
    ) -> None:
        """Initialize blocked GFP tensor base configuration.

        Args:
            original_shape: Shape of the tensor before quantization.
            group_axis: Axis along which grouping is performed.
            group_size: Number of elements in each group.
            dtype: GFP data type configuration (must use signed mantissa).
            block_shape: Shape of each block.
            block_alignment: Optional alignment for mantissa and exponent data
                within each block (must be divisible by group_size).

        Raises:
            ValueError: If mantissa is unsigned or block configuration is invalid.
        """
        if not dtype.mantissa_signed:
            raise ValueError("BlockedGFPTensor does not support unsigned mantissa")
        super().__init__(
            original_shape=original_shape,
            group_axis=group_axis,
            group_size=group_size,
            dtype=dtype,
        )

        if len(original_shape) != len(block_shape):
            raise ValueError(
                f"Original shape {original_shape} and block shape {block_shape} have different number of dimensions"
            )
        self.shape = torch.Size(
            [
                int(math.ceil(size / block_size))
                for size, block_size in zip(original_shape, block_shape)
            ]
        )

        if block_shape[group_axis] % group_size != 0:
            raise ValueError(
                f"Block group axis size {block_shape[group_axis]} is not divisible by group size {group_size}"
            )
        self.block_shape = block_shape

        if block_alignment is not None:
            if block_alignment % group_size != 0:
                raise ValueError(
                    f"Block alignment {block_alignment} is not divisible by group size {group_size}"
                )
        self.block_alignment = block_alignment

    def __str__(self) -> str:
        """Return string representation of blocked GFP tensor base."""
        return (
            f"BlockedGFPTensor("
            f"shape={list(self.shape)}, "
            f"block_shape={list(self.block_shape)}, "
            f"original_shape={list(self.original_shape)}, "
            f"group_axis={self.group_axis}, "
            f"group_size={self.group_size}, "
            f"dtype={self.dtype})"
        )

    def __eq__(self, value: object) -> bool:
        """Check equality with another BlockedGFPTensorBase instance.

        Args:
            value: Object to compare with.

        Returns:
            True if all configuration fields match, False otherwise.
        """
        if not isinstance(value, BlockedGFPTensorBase):
            return False
        return super().__eq__(value) and self.block_shape == value.block_shape

    @property
    def ndim(self) -> int:
        """Number of dimensions in block grid."""
        return len(self.shape)

    @property
    def block_ndim(self) -> int:
        """Number of dimensions in each block."""
        return len(self.block_shape)

    @property
    def block_grouped_ndim(self) -> int:
        """Number of dimensions in block after grouping."""
        return self.block_ndim + 1

    @property
    def block_group_axis_size(self) -> int:
        """Size of group axis within each block."""
        return self.block_shape[self.group_axis]

    @property
    def block_num_groups(self) -> int:
        """Number of groups within each block."""
        assert self.block_group_axis_size % self.group_size == 0
        return self.block_group_axis_size // self.group_size

    @property
    def block_grouped_shape(self) -> torch.Size:
        """Shape of a single block after grouping."""
        x = torch.empty(self.block_shape, device="meta")
        if self.group_axis != -1:
            x = x.transpose(-1, self.group_axis)
        x = x.unflatten(-1, (self.block_num_groups, self.group_size))
        return x.shape

    @property
    def block_mantissa_shape(self) -> torch.Size:
        """Shape of mantissa data within a single block."""
        return self.block_grouped_shape

    @property
    def block_exp_shape(self) -> torch.Size:
        """Shape of exponent data within a single block."""
        return self.block_grouped_shape[:-1] + (1,)

    @property
    def block_cpp_dtype(self) -> np.dtype:
        """NumPy structured dtype for C++ interop (mantissa + exponent)."""
        dtype_fields = []
        dtype_fields.append(
            ("exponent", self.dtype.exp_np_dtype, tuple(self.block_exp_shape))
        )

        if self.block_alignment is not None:
            block_exp_pad_size = self.block_alignment // self.group_size - int(
                np.prod(self.block_exp_shape)
            )
            if block_exp_pad_size > 0:
                dtype_fields.append(
                    ("exponent_pad", self.dtype.exp_np_dtype, (block_exp_pad_size,))
                )

        dtype_fields.append(
            ("mantissa", self.dtype.mantissa_np_dtype, tuple(self.block_mantissa_shape))
        )
        if self.block_alignment is not None:
            block_mantissa_pad_size = self.block_alignment - int(
                np.prod(self.block_mantissa_shape)
            )
            if block_mantissa_pad_size > 0:
                dtype_fields.append(
                    (
                        "mantissa_pad",
                        self.dtype.mantissa_np_dtype,
                        (block_mantissa_pad_size,),
                    )
                )

        return np.dtype(dtype_fields)

    @property
    def padded_original_shape(self) -> torch.Size:
        """Original shape after padding to block boundaries."""
        return torch.Size(
            [
                size * block_size
                for size, block_size in zip(self.shape, self.block_shape)
            ]
        )

    def get_block_slices(self, block_indices: tuple[int, ...]) -> tuple[slice, ...]:
        """Convert block indices to slices on padded original shape.

        Args:
            block_indices: Indices of the block in the block grid.

        Returns:
            Tuple of slices for extracting the block from padded original data.
        """
        block_slices = []
        for block_idx, block_size in zip(block_indices, self.block_shape):
            start = block_idx * block_size
            end = start + block_size
            block_slices.append(slice(start, end))
        return tuple(block_slices)


class BlockedGFPTensor(BlockedGFPTensorBase):
    """
    Blocked GFP tensor with data stored in block-structured NumPy array.

    On hardware, we handle data in blocks for better memory access patterns.
    In GFP format, each block contains two fields: exponent data and mantissa
    data. For example, assuming a block size of 16384 and group size of 32,
    we should have 16384 / 32 = 512 exponent values and 16384 mantissa values
    in each block:
    |----------------------|
    |                      | <- 512 Exponents
    |                      |
    |----------------------|
    |                      | <- 16384 Mantissas
    |                      |
    |                      |
    |                      |
    |----------------------|

    At Python level, a single block is represented as a customized NumpPy dtype
    with two fields: "exponent" and "mantissa":
    ```python
    np.dtype([
        ("exponent", np.uint8, exponent_shape),
        ("mantissa", np.int8, mantissa_shape)
    ])
    ```
    where `exponent_shape` could be any shape as long as the total number of elements
    matches the number of exponents in the block, e.g., 512 in the above example.
    Similarly, `mantissa_shape` could be any shape as long as the total number of
    elements matches the number of mantissas in the block, e.g., 16384 in the above
    example. **We define `block_shape` as the mantissa shape of each block, and the
    exponent shape can be derived from `block_shape` and `group_size`.**

    Therefore, you may have the following block definition:
    ```python
    np.dtype([
        ("exponent", np.uint8, (128, 4, 1)),
        ("mantissa", np.int8, (128, 4, 32)),
    ])
    ```
    which is corresponding to the following memory layout:
    |----------------------|
    |                      | <- exponent[0, 0, 0] ~ exponent[127, 3, 0]
    |                      |
    |----------------------|
    |                      | <- mantissa[0, 0, 0] ~ mantissa[127, 3, 31]
    |                      |
    |                      |
    |                      |
    |----------------------|

    However, in actual hardware implementation, we may not always have full blocks.
    For example, we may have the following block definition:
    ```python
    np.dtype([
        ("exponent", np.uint8, (128, 2, 1)),
        ("mantissa", np.int8, (128, 2, 32)),
    ])
    ```
    which only occupies half of the block memory. By default, the data layout will be
    tightly packed without any padding:
    |----------------------|
    |                      | <- exponent[0, 0, 0] ~ exponent[127, 1, 0]
    |----------------------|
    |                      | <- mantissa[0, 0, 0] ~ mantissa[127, 1, 31]
    |                      |
    |----------------------|

    This may lead to inefficient memory access on hardware because the address offset
    of mantissa data is not fixed from the start address of the block. To resolve this
    issue, we can optionally add paddings to after the exponent data and mantissa data
    to align them to certain boundaries. For example, given the block size is 16384, an
    aligned block definition could be:
    ```python
    np.dtype([
        ("exponent", np.uint8, (128, 2, 1)),
        ("exponent_pad", np.uint8, (256,)),
        ("mantissa", np.int8, (128, 2, 32)),
        ("mantissa_pad", np.int8, (8192,)),
    ])
    ```
    |----------------------|
    |                      | <- exponent[0, 0, 0] ~ exponent[127, 1, 0]
    |0000000000000000000000| <- exponent_pad[0] ~ exponent_pad[255]
    |----------------------|
    |                      | <- mantissa[0, 0, 0] ~ mantissa[127, 1, 31]
    |                      |
    |0000000000000000000000| <- mantissa_pad[0] ~ mantissa_pad[8191]
    |0000000000000000000000|
    |----------------------|

    **We define `block_alignment` as the number of mantissa values in a single block
    after alignment. The number of exponent values in a single block after alignment
    is `block_alignment // group_size`.**

    With the definition above, the `exponent_pad` size and `mantissa_pad` size can be
    derived from `block_shape` and `block_alignment`:
    ```python
    block_exp_pad_size = block_alignment // group_size - np.prod(block_exp_shape)
    block_mantissa_pad_size = block_alignment - np.prod(block_mantissa_shape)
    ```
    """

    def __init__(
        self,
        original_shape: torch.Size,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
        block_shape: torch.Size,
        blocked_data: np.ndarray,
        block_alignment: int | None = None,
    ) -> None:
        """Initialize blocked GFP tensor with pre-blocked data.

        Args:
            original_shape: Shape of the tensor before quantization.
            group_axis: Axis along which grouping is performed.
            group_size: Number of elements in each group.
            dtype: GFP data type configuration.
            block_shape: Shape of each block.
            blocked_data: NumPy structured array containing blocked mantissa and exponent.
            block_alignment: Optional alignment for mantissa and exponent data
                within each block (must be divisible by group_size).
        """
        super().__init__(
            original_shape=original_shape,
            group_axis=group_axis,
            group_size=group_size,
            dtype=dtype,
            block_shape=block_shape,
            block_alignment=block_alignment,
        )
        self.blocked_data = blocked_data

    @classmethod
    def block_from_raw(
        cls,
        original_shape: torch.Size,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
        block_shape: torch.Size,
        mantissa_data: torch.Tensor,
        exp_data: torch.Tensor,
        block_alignment: int | None = None,
    ) -> "BlockedGFPTensor":
        """Create blocked GFP tensor from raw mantissa and exponent tensors.
        To access the mantissa and exponent data from the blocked data, we can use
            self.obj.blocked_data["mantissa"] --> shape [*self.shape, *self.block_mantissa_shape]
            self.obj.blocked_data["exponent"] --> shape [*self.shape, *self.block_exp_shape]

        Blocking is to convert the GFP data to the blocked data. We have to
        unflatten each dimension of the GFP data into (num_blocks, block_size),
        and then permute the block dimensions to the front (group axis is the
        last dimension). If group axis is not the last dimension, we need to
        transpose the data to move the group axis to the original dimension.

        Args:
            original_shape: Shape of the tensor before quantization.
            group_axis: Axis along which grouping is performed.
            group_size: Number of elements in each group.
            dtype: GFP data type configuration.
            block_shape: Shape of each block.
            mantissa_data: Mantissa tensor data.
            exp_data: Exponent tensor data.
            block_alignment: Optional alignment for mantissa and exponent data
                within each block (must be divisible by group_size).

        Returns:
            BlockedGFPTensor with data organized into blocks.
        """
        obj = cls.__new__(cls)
        BlockedGFPTensorBase.__init__(
            obj,
            original_shape=original_shape,
            group_axis=group_axis,
            group_size=group_size,
            dtype=dtype,
            block_shape=block_shape,
            block_alignment=block_alignment,
        )

        pad_sizes = [
            -obj.mantissa_shape[i] % obj.block_mantissa_shape[i]
            for i in range(obj.grouped_ndim)
        ]
        # mantissa data and exp data has group axis at the last dimension.
        if not all(pad == 0 for pad in pad_sizes):
            assert pad_sizes[-1] == 0, "Group dimension should not be padded"
            pad_arg = [x for p in pad_sizes[::-1] for x in (0, p)]
            mantissa_data = F.pad(mantissa_data, pad_arg)
            exp_data = F.pad(exp_data, pad_arg)

        # obj.shape doesn't have group axis at the last dimension.
        blocked_data = np.empty(obj.shape, dtype=obj.block_cpp_dtype)

        blocked_group_ordered_shape = []
        for sz, b_sz in zip(mantissa_data.shape[:-1], obj.block_mantissa_shape[:-1]):
            # Number of blocks in each dimension and block size.
            assert sz % b_sz == 0
            blocked_group_ordered_shape.extend([sz // b_sz, b_sz])
        # [num_blocks_0, block_size_0, num_blocks_1, block_size_1, ..., -1] so
        # that the group axis is the last dimension.
        blocked_group_ordered_shape.append(-1)

        dim_order = (
            [i * 2 for i in range(obj.ndim)]
            + [i * 2 + 1 for i in range(obj.ndim)]
            + [-1]
        )
        # move group axis to the original position for num_blocks dimensions.
        if obj.group_axis != -1:
            dim_order[obj.ndim - 1], dim_order[obj.non_neg_group_axis] = (
                dim_order[obj.non_neg_group_axis],
                dim_order[obj.ndim - 1],
            )
        gfp_np_mantissa_data = (
            mantissa_data.to(obj.dtype.mantissa_torch_dtype)
            .reshape(*blocked_group_ordered_shape)
            .permute(dim_order)
            .numpy()
        )
        gfp_np_exp_data = (
            exp_data.to(obj.dtype.exp_torch_dtype)
            .reshape(*blocked_group_ordered_shape)
            .permute(dim_order)
            .numpy()
        )
        blocked_data["mantissa"] = gfp_np_mantissa_data
        blocked_data["exponent"] = gfp_np_exp_data
        obj.blocked_data = blocked_data
        return obj

    @classmethod
    def block_from_float(
        cls,
        group_axis: int,
        group_size: int,
        dtype: GFPDataType,
        block_shape: torch.Size,
        original_data: torch.Tensor,
        block_alignment: int | None = None,
    ) -> "BlockedGFPTensor":
        """Create blocked GFP tensor directly from floating-point data.

        Args:
            group_axis: Axis along which grouping is performed.
            group_size: Number of elements in each group.
            dtype: GFP data type configuration.
            block_shape: Shape of each block.
            original_data: Floating-point tensor to quantize and block.
            block_alignment: Optional alignment for mantissa and exponent data
                within each block (must be divisible by group_size).

        Returns:
            BlockedGFPTensor with quantized and blocked data.
        """
        gfp_data = GFPTensor.quantize_from_float(
            group_axis=group_axis,
            group_size=group_size,
            dtype=dtype,
            original_data=original_data,
        )
        return gfp_data.block(block_shape, block_alignment=block_alignment)

    def __getitem__(
        self, key: slice | int | tuple[slice | int, ...]
    ) -> BlockedGFPTensor:
        """Get a slice of blocks from the blocked GFP tensor.

        Args:
            key: Slice or index for block grid dimensions.

        Returns:
            New BlockedGFPTensor containing the selected blocks.
        """
        blocked_data = self.blocked_data[key]
        original_shape = [
            size * block_size
            for size, block_size in zip(blocked_data.shape, self.block_shape)
        ]
        return BlockedGFPTensor(
            original_shape=torch.Size(original_shape),
            group_axis=self.group_axis,
            group_size=self.group_size,
            dtype=self.dtype,
            block_shape=self.block_shape,
            blocked_data=blocked_data,
        )

    def __setitem__(
        self, key: slice | int | tuple[slice | int, ...], value: BlockedGFPTensor
    ):
        """Set a slice of blocks in the blocked GFP tensor.

        Args:
            key: Slice or index for block grid dimensions.
            value: BlockedGFPTensor to assign to the selected blocks.
        """
        self.blocked_data[key] = value.blocked_data

    def copy(self) -> "BlockedGFPTensor":
        """Create a deep copy of this blocked GFP tensor.

        Returns:
            New BlockedGFPTensor with copied data.
        """
        return BlockedGFPTensor(
            original_shape=copy.copy(self.original_shape),
            group_axis=self.group_axis,
            group_size=self.group_size,
            dtype=copy.copy(self.dtype),
            block_shape=copy.copy(self.block_shape),
            blocked_data=self.blocked_data.copy(),
        )

    def copy_from(self, other: "BlockedGFPTensor"):
        """Copy data from another blocked GFP tensor into this one.

        Args:
            other: Source BlockedGFPTensor to copy from.
        """
        self.original_shape = copy.copy(other.original_shape)
        self.group_axis = other.group_axis
        self.group_size = other.group_size
        self.dtype = copy.copy(other.dtype)
        self.block_shape = copy.copy(other.block_shape)
        self.blocked_data = other.blocked_data.copy()

    def deblock(self) -> GFPTensor:
        """Convert blocked GFP tensor back to regular GFP tensor.
        To access the mantissa and exponent data from the blocked data, we can use
            self.obj.blocked_data["mantissa"] --> shape [*self.shape, *self.block_mantissa_shape]
            self.obj.blocked_data["exponent"] --> shape [*self.shape, *self.block_exp_shape]


        Deblocking is to convert the blocked data to the GFP data. We have to
        merge the mantissa and exponent data of each block on each dimension.

        Returns:
            GFPTensor with data extracted from blocks.
        """
        # Fetch all the mantissa and exponent data from the blocked data.
        # The shape is [*self.shape , *self.block_mantissa_shape, ]
        blocked_torch_mantissa = torch.from_numpy(
            self.blocked_data["mantissa"].copy()
        ).int()
        # The shape is [*self.shape , *self.block_exp_shape]
        blocked_torch_exp = torch.from_numpy(self.blocked_data["exponent"].copy()).int()

        if self.group_axis != -1:
            blocked_torch_mantissa = blocked_torch_mantissa.transpose(
                self.non_neg_group_axis, self.ndim - 1
            )
            blocked_torch_exp = blocked_torch_exp.transpose(
                self.non_neg_group_axis, self.ndim - 1
            )
        dim_order = []
        for i in range(self.ndim):
            dim_order.extend([i, i + self.ndim])
        dim_order.append(-1)

        # Block GFP data is padded to the block sizes.
        padded_gfp_data_shape = [
            int(math.ceil(m_sz / bs_sz) * bs_sz)
            for m_sz, bs_sz in zip(
                self.mantissa_shape[:-1], self.block_mantissa_shape[:-1]
            )
        ] + [-1]
        gfp_mantissa_data = blocked_torch_mantissa.permute(dim_order).reshape(
            *padded_gfp_data_shape
        )
        gfp_exp_data = blocked_torch_exp.permute(dim_order).reshape(
            *padded_gfp_data_shape
        )
        # Remove the padding from the GFP data.
        gfp_mantissa_data = gfp_mantissa_data[
            [slice(0, sz) for sz in self.mantissa_shape]
        ]
        gfp_exp_data = gfp_exp_data[[slice(0, sz) for sz in self.exp_shape]]

        return GFPTensor(
            original_shape=self.original_shape,
            group_axis=self.group_axis,
            group_size=self.group_size,
            dtype=self.dtype,
            mantissa_data=gfp_mantissa_data,
            exp_data=gfp_exp_data,
        )

    @property
    def continuous_blocked_data(self) -> np.ndarray:
        """Get continuous C++ compatible data array.

        Returns:
            NumPy structured array with continuous block data for C++ interop.
        """
        return np.ascontiguousarray(self.blocked_data)


class GFPGemm:
    """Elastix Group Floating Point (GFP) GEMM operator."""

    def __init__(
        self,
        accum_dtype: GFPDataType,
        product_dtype: GFPDataType,
    ) -> None:
        """Initialize GFP GEMM operator.

        Args:
            accum_dtype: GFP data type for accumulation results.
            product_dtype: GFP data type for intermediate products.
        """
        self.accum_dtype = accum_dtype
        self.product_dtype = product_dtype

    def __call__(
        self,
        lhs: GFPTensor,
        rhs: GFPTensor,
    ) -> GFPTensor:
        """Emulate GEMM (matrix multiplication) operation between two GFP tensors.

        Dimension notation:
            B = Batch, C = Columns (reduction), R = Rows,
            G = Group size, N = Number of groups (C / G)

        Args:
            lhs: Left-hand side GFP tensor with original shape [B0..., (B), C].
            rhs: Right-hand side GFP tensor with original shape [B1..., C, R].

        Returns:
            Result GFP tensor with shape [B2..., (B), R] where B2 is broadcast
            from B0 and B1. Output has group_axis=-1 and group_size=1.
        """
        self.verify(lhs, rhs)

        # Calculate dot product along the group dimension
        try:
            # This captures the case when batch size of LHS is explicit. The
            # remained batches, B0... and B1... must be broadcastable.
            # [B0..., B, N, G] * [B1..., R, N, G] = [B2..., B, R, N]
            m = torch.einsum(
                "...bng, ...rng -> ...brn",
                lhs.mantissa_data_signed,
                rhs.mantissa_data_signed,
            )
        except RuntimeError:
            # This captures the case when batch size of LHS is an implicit 1.
            # The remained batches, B0... and B1... must be broadcastable.
            #
            # For example:
            # [batch, num_heads, hidden_size] @
            # [batch, num_heads, hidden_size, seq_length] =
            # [batch, num_heads, seq_length]
            # In this case, the LHS is Q whose length is 1. However, this length
            # axis is reduced and become implicit, making einsum impossible to
            # match it.
            #
            # [B0..., N, G] * [B1..., R, N, G] = [B2..., R, N]
            m = torch.einsum(
                "...ng, ...rng -> ...rn",
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
        # LHS: [B0..., (B), N, 1] -> [B0..., (B), 1, N]
        # RHS: [B1..., R, N, 1] -> [B1..., 1, R, N]
        # Result: [B2..., (B), R, N]
        lhs_perm = list(range(lhs.exp_data.ndim - 2)) + [-1, -2]
        rhs_perm = list(range(rhs.exp_data.ndim - 3)) + [-1, -3, -2]
        e = lhs.exp_data.permute(lhs_perm) + rhs.exp_data.permute(rhs_perm)
        e = clamp_with_logging(
            e,
            min=self.product_dtype.bottom_exp,
            max=self.product_dtype.top_exp,
            prefix="exponent product",
        )

        # Find the largest exponent for each [B2..., (B), R] position across N
        # groups. This will be the final exponent.
        # However, to avoid numerical inaccuracies, we first shift the mantissa to align to
        # the lowest exponent, then sum along the N dimension, and finally shift back to get
        # the final mantissa (max).
        # int64 is used to reduce the chance of overflow when shifting the mantissa.
        #
        # On hardware this operation is lossless and we actually don't need to materialize
        # the e_min; instead, we can finish the accumulation with an adder-tree and do the
        # shifting before each addition.
        e_max = e.max(-1, keepdim=True)[0]  # [B2..., (B), R, 1]
        e_min = e.min(-1, keepdim=True)[0]  # [B2..., (B), R, 1]
        e_diff = e - e_min  # [B2..., (B), R, N]

        if (m.abs().clamp(1).log2() + e_diff).max() > 63:
            # we check for overflow after the shift, but it's still possible to have
            # overflow after the sum
            logging.warning("Overflow detected in accumulator (emulator-only).")

        m = (m.to(torch.int64) << e_diff).sum(-1, keepdim=True) >> (e_max - e_min)
        e = e_max

        # Calculate the final results
        s = m.sign() if not self.accum_dtype.mantissa_signed else None

        m = m.abs() if not self.accum_dtype.mantissa_signed else m
        m = clamp_with_logging(
            m,
            min=self.accum_dtype.bottom_mantissa,
            max=self.accum_dtype.top_mantissa,
            prefix="mantissa accum",
        )

        e = e - lhs.dtype.exp_bias - rhs.dtype.exp_bias + self.accum_dtype.exp_bias
        e = clamp_with_logging(
            e,
            min=self.accum_dtype.bottom_exp,
            max=self.accum_dtype.top_exp,
            prefix="exponent accum",
        )

        return GFPTensor(
            original_shape=e.squeeze(-1).shape,
            group_axis=-1,
            group_size=1,
            dtype=self.accum_dtype,
            mantissa_data=m,
            exp_data=e,
            sign_data=s,
        )

    def verify(self, lhs: GFPTensor, rhs: GFPTensor):
        """Verify GEMM operation inputs for correctness and validity.

        Args:
            lhs: Left-hand side GFP tensor.
            rhs: Right-hand side GFP tensor.

        Raises:
            ValueError: If tensor dimensions, shapes, or configurations are incompatible.
        """
        if lhs.original_ndim < 1 or rhs.original_ndim < 2:
            raise ValueError(
                f"Original axis too small, got {lhs.original_ndim} and {rhs.original_ndim}"
            )

        if lhs.original_shape[-1] != rhs.original_shape[-2]:
            raise ValueError(
                f"Columns axis of original shape mismatch: {lhs.original_shape[-1]} != {rhs.original_shape[-2]}"
            )

        if lhs.group_size != rhs.group_size:
            raise ValueError(
                f"Group size mismatch: {lhs.group_size} != {rhs.group_size}"
            )

        if lhs.group_axis not in (lhs.original_ndim - 1, -1) or rhs.group_axis not in (
            lhs.original_ndim - 2,
            -2,
        ):
            raise ValueError(
                f"Group axis must be -1 and -2, got {lhs.group_axis} and {rhs.group_axis}"
            )


class GFPElmwiseAdd:
    """Elastix Group Floating Point (GFP) element-wise addition operator."""

    def __init__(self, output_dtype: GFPDataType) -> None:
        """Initialize GFP element-wise addition operator.

        Args:
            output_dtype: GFP data type for output results.
        """
        self.output_dtype = output_dtype

    def __call__(self, lhs: GFPTensor, rhs: GFPTensor) -> GFPTensor:
        """Emulate element-wise addition between two GFP tensors.

        Args:
            lhs: Left-hand side GFP tensor.
            rhs: Right-hand side GFP tensor (must have same shape as lhs).

        Returns:
            Result GFP tensor with element-wise sum.
        """
        self.verify(lhs, rhs)

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

    def verify(self, lhs: GFPTensor, rhs: GFPTensor):
        """Verify element-wise addition inputs for correctness and validity.

        Args:
            lhs: Left-hand side GFP tensor.
            rhs: Right-hand side GFP tensor.

        Raises:
            ValueError: If shapes or configurations don't match.
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
