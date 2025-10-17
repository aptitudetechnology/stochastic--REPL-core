# Open-Source FPGA Toolchain for Gowin FPGAs (Project Apicula)

This guide provides instructions for installing and using the open-source FPGA toolchain based on **Project Apicula** to program Gowin FPGAs like the Tang Nano 9K (GW1NR-9). This is a free alternative to Gowin EDA.

## Supported Devices

Project Apicula supports the following Gowin FPGA families:
- GW1N-1, GW1N-4, GW1N-9
- GW1NZ-1
- GW1NS-2, GW1NS-4
- GW1NR-9 (used in Tang Nano 9K)

## Prerequisites

- Linux operating system (Ubuntu/Debian recommended)
- Python 3.6 or later
- Git
- Build tools (gcc, make, etc.)

## Installation Steps

### 1. Install System Dependencies

```bash
sudo apt update
sudo apt install -y build-essential clang bison flex libreadline-dev \
                     gawk tcl-dev libffi-dev git mercurial graphviz   \
                     xdot pkg-config python python3 libftdi-dev \
                     qt5-default python3-dev libboost-all-dev cmake libeigen3-dev
```

### 2. Install Yosys (Synthesis Tool)

```bash
git clone https://github.com/YosysHQ/yosys.git
cd yosys
make -j$(nproc)
sudo make install
cd ..
```

### 3. Install nextpnr (Place and Route Tool)

```bash
git clone https://github.com/YosysHQ/nextpnr.git
cd nextpnr
cmake -DARCH=gowin -DCMAKE_INSTALL_PREFIX=/usr/local .
make -j$(nproc)
sudo make install
cd ..
```

### 4. Install Project Apicula

```bash
git clone https://github.com/YosysHQ/apicula.git
cd apicula
pip3 install -r requirements.txt
python3 setup.py build
sudo python3 setup.py install
cd ..
```

### 5. Install openFPGALoader (Programming Tool)

```bash
git clone https://github.com/trabucayre/openFPGALoader.git
cd openFPGALoader
mkdir build
cd build
cmake ..
make -j$(nproc)
sudo make install
cd ../..
```

## Usage Instructions

### Building Your Design

1. Navigate to your Verilog project directory:
   ```bash
   cd /path/to/your/verilog/project
   ```

2. Create a synthesis script (e.g., `synth.ys`):
   ```
   read_verilog top_module.v
   read_verilog other_modules.v
   synth_gowin -top top_module
   write_json design.json
   ```

3. Run synthesis:
   ```bash
   yosys synth.ys
   ```

4. Run place and route:
   ```bash
   nextpnr-gowin --json design.json --write pnr.json --device GW1NR-9
   ```

5. Generate bitstream:
   ```bash
   gowin_pack -d GW1NR-9 -o bitstream.fs pnr.json
   ```

### Programming the FPGA

Connect your Tang Nano 9K board and program it:
```bash
openFPGALoader -b tangnano9k bitstream.fs
```

## Project-Specific Usage

For the stochastic REPL core project, assuming your top module is in `verilog/stochastic_repl_core.v`:

1. Create a synthesis script `synth.ys`:
   ```
   read_verilog verilog/sng.v
   read_verilog verilog/stochastic_multiplier.v
   read_verilog verilog/stochastic_adder.v
   read_verilog verilog/bitstream_converter.v
   read_verilog verilog/stochastic_repl_core.v
   synth_gowin -top stochastic_repl_core
   write_json design.json
   ```

2. Run the build process:
   ```bash
   yosys synth.ys
   nextpnr-gowin --json design.json --write pnr.json --device GW1NR-9
   gowin_pack -d GW1NR-9 -o bitstream.fs pnr.json
   ```

3. Program the board:
   ```bash
   openFPGALoader -b tangnano9k bitstream.fs
   ```

## Troubleshooting

- If you encounter permission issues, try running commands with `sudo` or adjust permissions.
- Ensure your Tang Nano 9K is properly connected and recognized by the system.
- Check device support with `openFPGALoader --list-boards` to confirm tangnano9k is listed.
- For synthesis issues, verify your Verilog code is compatible with Yosys.

## Additional Resources

- [Project Apicula GitHub](https://github.com/YosysHQ/apicula)
- [Yosys Documentation](https://yosyshq.net/yosys/)
- [nextpnr Documentation](https://github.com/YosysHQ/nextpnr)
- [openFPGALoader Documentation](https://github.com/trabucayre/openFPGALoader)