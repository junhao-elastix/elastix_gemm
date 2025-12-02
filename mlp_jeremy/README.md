# ACX MLP RTL

## Overview
This project contains RTL (currently Achronix specific) for a column of MLP (Matrix-L-Processor) blocks, configured to perform dot products, along with a `cocotb`-based test suite.

The main module, `mlp_bram_col`, instantiates a configurable number of MLP units in a vertical stack. Each unit consists of an `ACX_MLP72` primitive paired with a `weight_bram` for storing parameters. The design is optimized for dual 8x8 dot product operations and supports both `INT8` and `BFP8` data types.

The accompanying testbench validates the hardware implementation against a PyTorch reference model, ensuring bit-accurate results for various data scales and accumulation scenarios.

# Setup
If not installed, get UV to manage the Python environment:
`curl -LsSf https://astral.sh/uv/install.sh | sh`
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


# Run Simulation
The RTL tests are run using `cocotb` and can be executed with `pytest` for test discovery or by running the test script directly.

To run all tests:
```bash
cd src/acx_mlp
uv run pytest -s
```

To run a specific test file:
```bash
cd src/acx_mlp
uv run sim/test_acx_mlp.py
```

# Python Code Quality
This project uses `ruff` for linting and `mypy` for static type checking.

To run the checks:
```bash
cd src/acx_mlp
uv run ruff check .
uv run mypy .
```

# Architecture and Golden Model
For a detailed explanation of the RTL architecture, see the [Architecture Manual](ARCHITECTURE.md).

A Python-based golden model is available in `golden_model.py` to provide a reference implementation for the dot product calculations. You can run its basic test with:
```bash
python test_golden_model.py
```

## SpinalHDL 
https://spinalhdl.github.io/SpinalDoc-RTD/master/SpinalHDL/Getting%20Started/Install%20and%20setup.html
Requires JDK, Scala2, and SBT (Scala build tool), easiest way is to install [cursor]https://get-coursier.io/docs/cli-installation :

(Assuming 
dpkg --print-architecture
is amd64)
```bash
curl -fL "https://github.com/coursier/launchers/raw/master/cs-x86_64-pc-linux.gz" | gzip -d > cs
chmod +x cs
./cs setup
```

Check setup w/
  $ source ~/.profile
  $ scala -version

For VS Code users, install the 'Metals (Scala)' extension

# Verilator Install (NOTE: doesn't work with Achronix protected code):
(Install from source for verion >= 5.036, packages are too old)
https://veripool.org/guide/latest/install.html#git-install

sudo apt-get install git help2man perl python3 make autoconf g++ flex bison ccache
sudo apt-get install libgoogle-perftools-dev numactl perl-doc
sudo apt-get install libfl2  # Ubuntu only (ignore if gives error)
                     graphviz xdot pkg-config python3 zlib1g-dev cmake

sudo apt install python3-pip
python3 -m pip install click

git clone https://github.com/YosysHQ/yosys --recurse-submodules
cd yosys
make -j$(nproc)
sudo make install
cd ..
### sby
git clone https://github.com/YosysHQ/sby
cd sby
sudo make install
cd ..
### Boolector
git clone https://github.com/boolector/boolector
cd boolector
./contrib/setup-btor2tools.sh
./contrib/setup-lingeling.sh
./configure.sh
make -C build -j$(nproc)
sudo cp build/bin/{boolector,btor*} /usr/local/bin/
sudo cp deps/btor2tools/build/bin/btorsim /usr/local/bin/
cd ..
### Yices2
sudo apt install gperf libgmp-dev
git clone https://github.com/SRI-CSL/yices2.git yices2
cd yices2
autoconf
./configure
make -j$(nproc)
sudo make install
cd ..

## Notes
Something about including the Achronix libraries (maybe protected code blocks?) messes up asdb dumps in Riviera - the log function cant find any signals to log.  It looks like Achronix gets aorund this by using the wave command, creating wave.do files that manually add each signal to the waveform viewer with e.g.:

```
# Add output interface
add wave -noupdate -group "Output" -radix hex /tb_matrix_engine/o_dout
add wave -noupdate -group "Output" /tb_matrix_engine/o_dout_valid
add wave -noupdate -group "Output" /tb_matrix_engine/o_dout_sop
add wave -noupdate -group "Output" /tb_matrix_engine/o_dout_eop

# Add DUT internal signals if available
add wave -noupdate -group "DUT Internal" -radix hex /tb_matrix_engine/DUT/*
```

This requires Riviera to be used in GUI mode, though?

VCD dumping still works from verilog, which is the recommended approach for now.




# Run Simulation
To run the RTL tests:
```bash
cd src/acx_mlp
uv run pytest -s # or
uv run sim/test_acx_mlp.py
```

Python checking:
```bash
cd src/acx_mlp
uv run ruff check
uv run mypy .
```

## SpinalHDL 
https://spinalhdl.github.io/SpinalDoc-RTD/master/SpinalHDL/Getting%20Started/Install%20and%20setup.html
Requires JDK, Scala2, and SBT (Scala build tool), easiest way is to install [cursor]https://get-coursier.io/docs/cli-installation :

(Assuming 
dpkg --print-architecture
is amd64)
```bash
curl -fL "https://github.com/coursier/launchers/raw/master/cs-x86_64-pc-linux.gz" | gzip -d > cs
chmod +x cs
./cs setup
```

Check setup w/
  $ source ~/.profile
  $ scala -version

For VS Code users, install the 'Metals (Scala)' extension

# Verilator Install (NOTE: doesn't work with Achronix protected code):
(Install from source for verion >= 5.036, packages are too old)
https://veripool.org/guide/latest/install.html#git-install

sudo apt-get install git help2man perl python3 make autoconf g++ flex bison ccache
sudo apt-get install libgoogle-perftools-dev numactl perl-doc
sudo apt-get install libfl2  # Ubuntu only (ignore if gives error)
sudo apt-get install libfl-dev  # Ubuntu only (ignore if gives error)
sudo apt-get install zlibc zlib1g zlib1g-dev  # Ubuntu only (ignore if gives error)

# Formal Support (Yosys, Yosys-SMTBMC and ABC)
See https://symbiyosys.readthedocs.io/en/latest/install.html#install-doc
## Dependencies
sudo apt-get install build-essential clang bison flex \
                     libreadline-dev gawk tcl-dev libffi-dev git \
                     graphviz xdot pkg-config python3 zlib1g-dev cmake

sudo apt install python3-pip
python3 -m pip install click

git clone https://github.com/YosysHQ/yosys --recurse-submodules
cd yosys
make -j$(nproc)
sudo make install
cd ..
### sby
git clone https://github.com/YosysHQ/sby
cd sby
sudo make install
cd ..
### Boolector
git clone https://github.com/boolector/boolector
cd boolector
./contrib/setup-btor2tools.sh
./contrib/setup-lingeling.sh
./configure.sh
make -C build -j$(nproc)
sudo cp build/bin/{boolector,btor*} /usr/local/bin/
sudo cp deps/btor2tools/build/bin/btorsim /usr/local/bin/
cd ..
### Yices2
sudo apt install gperf libgmp-dev
git clone https://github.com/SRI-CSL/yices2.git yices2
cd yices2
autoconf
./configure
make -j$(nproc)
sudo make install
cd ..

## Notes
Something about including the Achronix libraries (maybe protected code blocks?) messes up asdb dumps in Riviera - the log function cant find any signals to log.  It looks like Achronix gets aorund this by using the wave command, creating wave.do files that manually add each signal to the waveform viewer with e.g.:

```
# Add output interface
add wave -noupdate -group "Output" -radix hex /tb_matrix_engine/o_dout
add wave -noupdate -group "Output" /tb_matrix_engine/o_dout_valid
add wave -noupdate -group "Output" /tb_matrix_engine/o_dout_sop
add wave -noupdate -group "Output" /tb_matrix_engine/o_dout_eop

# Add DUT internal signals if available
add wave -noupdate -group "DUT Internal" -radix hex /tb_matrix_engine/DUT/*
```

This requires Riviera to be used in GUI mode, though?

VCD dumping still works from verilog, which is the recommended approach for now.