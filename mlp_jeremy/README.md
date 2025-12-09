# ACX MLP RTL

## Overview
This project contains RTL (currently Achronix specific) for a column of MLP (Matrix-L-Processor) blocks, configured to perform dot products, along with a `cocotb`-based test suite.

The main module, `mlp_bram_col`, instantiates a configurable number of MLP units in a vertical stack. Each unit consists of an `ACX_MLP72` primitive paired with a `weight_bram` for storing parameters. The design is optimized for dual 8x8 dot product operations and supports both `INT8` and `BFP8` data types.

The accompanying testbench validates the hardware implementation against a PyTorch reference model, ensuring bit-accurate results for various data scales and accumulation scenarios.

## Key Performance Metrics

| Metric | Value |
|--------|-------|
| Peak MACs/cycle | 128 (8 MLPs × 2 banks × 8 elements) |
| Peak throughput | 12.8 GMAC/s @ 100 MHz |
| Pipeline latency | 2 cycles |
| Compute efficiency | V/(V+3) where V = accumulation cycles |

Example: V=128 achieves **97.7% efficiency** (125.1 MACs/cycle).

## Setup

### Python Environment
If not installed, get UV to manage the Python environment:
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

### RTL Simulator (Riviera)
To run RTL simulations, an RTL simulator (currently Riviera) and the Achronix libraries (from ACE) are required:
- [Riviera](https://drive.google.com/drive/folders/1rMt8kyu8LbCznAFgyS4dDnR7YtzYV7iC?usp=drive_link) - found in ACE_Installs (also grab the floating license files)

```bash
# Install dependencies
sudo apt install libxcb-xinerama0 libxcb-cursor0 libxcb-xinput0 libpulse-dev libsnappy-dev libxcb-icccm4 libxcb-keysyms1 libxcb-xkb1 libxkbcommon-x11-dev

./Riviera-PRO-2025.04.139-Linux64.run
./setup_ace
./intall_ace.sh -l ace.lic -L synplify.lic

# License (add to bashrc):
export ALDEC_LICENSE_FILE=27009@workstation-01.local

# Riviera setup (optionally add to bashrc):
source ~/Aldec/Riviera-PRO-2025.04-x64/etc/setenv
```

## Run Simulation

The RTL tests are run using `cocotb` and can be executed by running the test scripts directly.

### Main MLP Tests (32 tests, NUM_MLPS=4)
```bash
cd src/acx_mlp
uv run sim/test_acx_mlp.py
```

### NV Dot Product Tests (4 tests, NUM_MLPS=8)
```bash
uv run python src/checkpoint1/run_nv_test.py
```

### BCV Pattern Tests (6 tests, NUM_MLPS=8)
```bash
uv run python src/checkpoint1/run_bcv_test.py
```

## Python Code Quality

This project uses `ruff` for linting and `mypy` for static type checking.

```bash
cd src/acx_mlp
uv run ruff check .
uv run mypy .
```

## Architecture and Documentation

- **[Architecture Manual](ARCHITECTURE.md)** - Deep technical description of RTL modules, pipeline stages, and parallelism analysis
- **[BCV Computation Guide](BCV_COMPUTATION_GUIDE.md)** - How BCV matrix multiplication maps to hardware, test coverage
- **[MLP Timing Analysis](MLP_TIMING_ANALYSIS.md)** - Pipeline timing, control signals, and multi-cycle accumulation

## Compute Engine Integration

The `compute_engine_mlp` module provides a GEMM-compatible interface for integration with the main GEMM engine:

```
src/compute_engine/
├── rtl/
│   ├── compute_engine_mlp.sv   # GEMM-compatible interface (drop-in for compute_engine_modular)
│   ├── compute_engine_gfp.sv   # Streaming GFP8 interface
│   └── gfp8_to_bfp8.sv         # Format conversion
└── tests/
    └── test_gemm_interface.py  # Validation tests
```

See [compute_engine/README.md](src/compute_engine/README.md) for details.

## Notes

### Waveform Debugging
Something about including the Achronix libraries (maybe protected code blocks?) messes up asdb dumps in Riviera - the log function can't find any signals to log. Achronix works around this by using the wave command, creating wave.do files that manually add each signal to the waveform viewer:

```tcl
# Add output interface
add wave -noupdate -group "Output" -radix hex /tb_matrix_engine/o_dout
add wave -noupdate -group "Output" /tb_matrix_engine/o_dout_valid

# Add DUT internal signals if available
add wave -noupdate -group "DUT Internal" -radix hex /tb_matrix_engine/DUT/*
```

This requires Riviera to be used in GUI mode. VCD dumping still works from Verilog, which is the recommended approach for now.

---

## Optional Tool Installation

### SpinalHDL
https://spinalhdl.github.io/SpinalDoc-RTD/master/SpinalHDL/Getting%20Started/Install%20and%20setup.html

Requires JDK, Scala2, and SBT (Scala build tool). Easiest way is to install [Coursier](https://get-coursier.io/docs/cli-installation):

```bash
# Assuming dpkg --print-architecture is amd64
curl -fL "https://github.com/coursier/launchers/raw/master/cs-x86_64-pc-linux.gz" | gzip -d > cs
chmod +x cs
./cs setup

# Check setup
source ~/.profile
scala -version
```

For VS Code users, install the 'Metals (Scala)' extension.

### Verilator (NOTE: doesn't work with Achronix protected code)
Install from source for version >= 5.036 (packages are too old):
https://veripool.org/guide/latest/install.html#git-install

```bash
sudo apt-get install git help2man perl python3 make autoconf g++ flex bison ccache
sudo apt-get install libgoogle-perftools-dev numactl perl-doc
sudo apt-get install libfl2 libfl-dev zlibc zlib1g zlib1g-dev  # Ubuntu only
```

### Formal Support (Yosys, SymbiYosys)
See https://symbiyosys.readthedocs.io/en/latest/install.html#install-doc

```bash
# Dependencies
sudo apt-get install build-essential clang bison flex \
                     libreadline-dev gawk tcl-dev libffi-dev git \
                     graphviz xdot pkg-config python3 zlib1g-dev cmake
sudo apt install python3-pip
python3 -m pip install click

# Yosys
git clone https://github.com/YosysHQ/yosys --recurse-submodules
cd yosys && make -j$(nproc) && sudo make install && cd ..

# SymbiYosys
git clone https://github.com/YosysHQ/sby
cd sby && sudo make install && cd ..

# Boolector
git clone https://github.com/boolector/boolector
cd boolector
./contrib/setup-btor2tools.sh
./contrib/setup-lingeling.sh
./configure.sh
make -C build -j$(nproc)
sudo cp build/bin/{boolector,btor*} /usr/local/bin/
sudo cp deps/btor2tools/build/bin/btorsim /usr/local/bin/
cd ..

# Yices2
sudo apt install gperf libgmp-dev
git clone https://github.com/SRI-CSL/yices2.git yices2
cd yices2 && autoconf && ./configure && make -j$(nproc) && sudo make install && cd ..
```
