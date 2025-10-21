# Achronix VP815 - Test Suite

Comprehensive test programs for the Achronix VP815 FPGA card.

## Test Programs

- **`test_dma.cpp`** / **`dma_test`** - Comprehensive DMA testing with buffer size validation and round-trip verification
- **`test_mmio.cpp`** / **`mmio_test`** - Safe MMIO testing with hardware validation and MSI-X status checking
- **`test_all.cpp`** / **`test_all`** - **⭐ RECOMMENDED** - All-in-one test covering DMA, MMIO, and MSI-X with safety measures
- **`test_interrupt_callbacks.cpp`** / **`test_interrupt_callbacks`** - Advanced callback-based interrupt interface testing

## Building Tests

Navigate to this directory and build:

```bash
cd tests/achronix

# Build basic test executables (no execution)
make

# Build individual tests
make dma_test
make mmio_test
make all_test                # ⭐ RECOMMENDED
make interrupt_test

# Clean build
make clean && make
```

## Running Tests

```bash
# Run all-in-one test (⭐ RECOMMENDED - covers DMA, MMIO, and MSI-X)
./test_all

# Run individual focused tests
./dma_test                    # DMA-only testing
./mmio_test                   # MMIO-only testing
./test_interrupt_callbacks    # Advanced interrupt callback testing
```

### Test Features

- **🛡️ Safety Measures**: All tests include proper safety checks
- **📊 Comprehensive Coverage**: DMA, MMIO, and MSI-X functionality 
- **⚡ MSI-X Safety**: Automatically detects MSI-X availability before testing
- **🔍 Error Validation**: Tests both success and failure cases
- **📝 Clear Output**: Detailed test results with success/failure indicators

**Note**: Tests use absolute paths for SDK dependencies and require proper VP815 hardware setup.
