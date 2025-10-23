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


Perfect! You already have comprehensive documentation. Let me enhance this with **QBG-specific additions** for your hypothesis testing.

## QBG Hypothesis Testing Additions

### Project Structure for Your Research
```bash
qbg-stochastic-computing/
├── docs/
│   └── toolchain_setup.md          # Your existing doc
├── python/
│   ├── qbg_reference.py            # H₂ Python validation
│   ├── analyze_results.py          # Statistical analysis
│   └── requirements.txt
├── rtl/
│   ├── primitives/
│   │   ├── lfsr_8bit.v            # Reusable LFSR
│   │   ├── lfsr_7bit.v            # Incommensurate period
│   │   └── lfsr_9bit.v            # For 3-LFSR (H₅)
│   ├── qbg/
│   │   ├── qbg_dual_mixer.v       # YOUR HYPOTHESIS
│   │   ├── qbg_triple_mixer.v     # For H₅ testing
│   │   └── sng_baseline.v         # Single-LFSR control
│   └── test/
│       ├── stochastic_mult_test.v # Test harness
│       └── error_counter.v        # Measurement logic
├── sim/
│   ├── test_qbg.py                # Cocotb testbench
│   ├── Makefile                   # Simulation runner
│   └── wave.gtkw                  # GTKWave config
├── syn/
│   ├── synth.ys                   # Your existing synthesis
│   ├── tangnano9k.cst             # Pin constraints
│   ├── Makefile                   # Build automation
│   └── timing_analysis.tcl        # Performance validation
└── results/
    ├── python_validation/         # Week 1-2 results
    ├── simulation/                # Week 3 cocotb results
    └── hardware/                  # Week 4 FPGA measurements
```

### Enhanced Synthesis Script for QBG

```bash
# syn/synth_qbg.ys
# Synthesis for dual-LFSR QBG hypothesis testing

read_verilog ../rtl/primitives/lfsr_8bit.v
read_verilog ../rtl/primitives/lfsr_7bit.v
read_verilog ../rtl/qbg/qbg_dual_mixer.v
read_verilog ../rtl/test/stochastic_mult_test.v
read_verilog ../rtl/test/error_counter.v

# Hierarchy check
hierarchy -check -top qbg_test_top

# Optimization for minimal resource usage
synth_gowin -top qbg_test_top -json qbg_design.json

# Report statistics for H₂ validation
stat

# Generate reports for paper
tee -o synthesis_report.txt stat
```

### Automated Build Makefile

```makefile
# syn/Makefile - Automated QBG build flow

PROJECT = qbg_hypothesis
DEVICE = GW1NR-9
BOARD = tangnano9k
TOP = qbg_test_top

# Source files
RTL_SOURCES = ../rtl/primitives/lfsr_8bit.v \
              ../rtl/primitives/lfsr_7bit.v \
              ../rtl/qbg/qbg_dual_mixer.v \
              ../rtl/test/stochastic_mult_test.v

# Derived files
SYNTH_JSON = $(PROJECT)_synth.json
PNR_JSON = $(PROJECT)_pnr.json
BITSTREAM = $(PROJECT).fs

.PHONY: all synth pnr bitstream program clean stats timing

all: bitstream

# Synthesis with resource reporting
synth: $(SYNTH_JSON)

$(SYNTH_JSON): $(RTL_SOURCES) synth_qbg.ys
	@echo "=== Synthesis with Yosys ==="
	yosys synth_qbg.ys | tee synthesis_log.txt
	@echo ""
	@echo "=== Resource Usage (for H₂ validation) ==="
	@grep -A 10 "Number of cells" synthesis_log.txt

# Place and route with timing analysis
pnr: $(PNR_JSON)

$(PNR_JSON): $(SYNTH_JSON) $(BOARD).cst
	@echo "=== Place and Route with nextpnr ==="
	nextpnr-gowin --json $(SYNTH_JSON) \
	              --write $(PNR_JSON) \
	              --device $(DEVICE) \
	              --cst $(BOARD).cst \
	              --freq 27 \
	              --timing-allow-fail | tee pnr_log.txt
	@echo ""
	@echo "=== Timing Report (for H₂ validation) ==="
	@grep "Max frequency" pnr_log.txt || echo "Check pnr_log.txt"

# Generate bitstream
bitstream: $(BITSTREAM)

$(BITSTREAM): $(PNR_JSON)
	@echo "=== Generating Bitstream ==="
	gowin_pack -d $(DEVICE) -o $(BITSTREAM) $(PNR_JSON)

# Program FPGA
program: $(BITSTREAM)
	@echo "=== Programming Tang Nano 9K ==="
	openFPGALoader -b $(BOARD) $(BITSTREAM)

# Extract statistics for paper
stats: synth
	@echo "=== Extracting Statistics for Publication ==="
	@echo "LUT count:" > ../results/hardware/resource_usage.txt
	@grep "SB_LUT" synthesis_log.txt >> ../results/hardware/resource_usage.txt
	@echo "DFF count:" >> ../results/hardware/resource_usage.txt
	@grep "SB_DFF" synthesis_log.txt >> ../results/hardware/resource_usage.txt
	@echo "Max frequency:" >> ../results/hardware/resource_usage.txt
	@grep "Max frequency" pnr_log.txt >> ../results/hardware/resource_usage.txt

# Timing analysis for performance validation
timing: pnr
	@echo "=== Detailed Timing Analysis ==="
	nextpnr-gowin --json $(SYNTH_JSON) \
	              --device $(DEVICE) \
	              --report timing_report.json
	@python3 analyze_timing.py timing_report.json

clean:
	rm -f *.json *.fs *.txt *.log
	rm -rf abc.history

help:
	@echo "QBG Hypothesis Testing Build System"
	@echo ""
	@echo "Targets:"
	@echo "  synth    - Synthesize design with Yosys"
	@echo "  pnr      - Place and route with nextpnr"
	@echo "  bitstream- Generate FPGA bitstream"
	@echo "  program  - Program Tang Nano 9K"
	@echo "  stats    - Extract resource statistics for paper"
	@echo "  timing   - Detailed timing analysis"
	@echo "  clean    - Remove generated files"
	@echo ""
	@echo "For H₂ validation workflow:"
	@echo "  make stats   # Get LUT/DFF counts"
	@echo "  make timing  # Verify >27 MHz operation"
	@echo "  make program # Test on hardware"
```

### Pin Constraints for Tang Nano 9K

```tcl
# syn/tangnano9k.cst - Pin mapping for QBG testing

# System clock (27 MHz on-board oscillator)
IO_LOC "clk" 52;
IO_PORT "clk" PULL_MODE=UP;

# Reset button (S2)
IO_LOC "reset" 3;
IO_PORT "reset" PULL_MODE=UP;

# 8-bit input value (DIP switches or buttons)
IO_LOC "value[0]" 25;
IO_LOC "value[1]" 26;
IO_LOC "value[2]" 27;
IO_LOC "value[3]" 28;
IO_LOC "value[4]" 29;
IO_LOC "value[5]" 30;
IO_LOC "value[6]" 31;
IO_LOC "value[7]" 32;

# Bitstream output (to GPIO for measurement)
IO_LOC "bitstream_out" 10;
IO_PORT "bitstream_out" DRIVE=8;

# Debug outputs (optional - connect to LEDs)
IO_LOC "debug_led[0]" 16;  # Green LED
IO_LOC "debug_led[1]" 17;  # Blue LED
IO_LOC "debug_led[2]" 18;  # Red LED

# Test signals for oscilloscope/logic analyzer
IO_LOC "test_lfsr1_bit" 19;
IO_LOC "test_lfsr2_bit" 20;
IO_PORT "test_lfsr1_bit" DRIVE=8;
IO_PORT "test_lfsr2_bit" DRIVE=8;
```

### Quick Start for H₂ Testing

Add this section to your documentation:

```markdown
## Quick Start: QBG Hypothesis Testing

### Phase 1: Python Validation (Week 1-2)
```bash
cd python/
python3 qbg_reference.py --trials 1000 --length 256
# Outputs: error statistics and autocorrelation measurements
# Decision: If improvement < 5%, stop here and publish negative result
```

### Phase 2: Verilog Simulation (Week 3)
```bash
cd sim/
pip3 install cocotb cocotb-bus
make
# Verifies Verilog matches Python reference
```

### Phase 3: FPGA Synthesis (Week 4)
```bash
cd syn/
make stats     # Get resource usage for paper
make timing    # Verify timing closure
make program   # Load onto Tang Nano 9K
```

### Measuring Results on Hardware
```bash
# Connect logic analyzer to test pins
# Record 10,000 samples at 27 MHz
# Transfer data to PC for analysis
python3 ../python/analyze_hardware.py captured_data.csv
```

### Expected Results (H₂ Predictions)
- **LUT usage**: 80-120 LUTs (<2% of 8640 available) ✓
- **Max frequency**: >100 MHz (target: 27 MHz) ✓
- **Autocorrelation reduction**: >50% vs single-LFSR ✓
- **Error reduction at L=256**: 10-30% ✓
```

## Additional Toolchain Validation

Add this troubleshooting section:

```markdown
## Validating Your Toolchain for QBG Research

### 1. Test Basic Synthesis
```bash
# Create a simple test
echo "module test(input a, output b); assign b = a; endmodule" > test.v
yosys -p "read_verilog test.v; synth_gowin -top test; write_json test.json"
# Should complete without errors
```

### 2. Test nextpnr-gowin
```bash
nextpnr-gowin --json test.json --device GW1NR-9 --write test_pnr.json
# Should report successful place and route
```

### 3. Test Bitstream Generation
```bash
gowin_pack -d GW1NR-9 -o test.fs test_pnr.json
# Should create test.fs (few KB)
```

### 4. Verify FPGA Connection
```bash
openFPGALoader --detect
# Should show: Tang Nano 9K detected
```

### 5. Test Full Flow
```bash
cd syn/
make clean
make bitstream
# Should complete all stages
```

If all 5 tests pass, your toolchain is ready for QBG hypothesis testing!
```

Would you like me to provide:
1. **Python reference implementation** (`qbg_reference.py`) for H₂ testing?
2. **Cocotb testbench** (`test_qbg.py`) for Verilog verification?
3. **Minimal Verilog** for the QBG mixer module?

Which would help you start testing your hypothesis?



## Additional Resources

### Core Toolchain
- [Project Apicula GitHub](https://github.com/YosysHQ/apicula)
- [Yosys Documentation](https://yosyshq.net/yosys/)
- [Yosys Command Reference](https://yosyshq.readthedocs.io/projects/yosys/en/latest/cmd_ref.html)
- [nextpnr Documentation](https://github.com/YosysHQ/nextpnr)
- [openFPGALoader Documentation](https://github.com/trabucayre/openFPGALoader)

### Tang Nano 9K Specific
- [Tang Nano 9K Official Wiki](https://wiki.sipeed.com/hardware/en/tang/Tang-Nano-9K/Nano-9K.html)
- [Tang Nano 9K Schematic](https://dl.sipeed.com/shareURL/TANG/Nano%209K/2_Schematic)
- [Sipeed Tang Nano Examples](https://github.com/sipeed/TangNano-9K-example)
- [Tang Nano 9K Pinout Reference](https://tang-nano-9k.readthedocs.io/)
- [GW1NR-9C Datasheet](https://www.gowinsemi.com/en/support/database/) (requires registration)

### Open Source FPGA Community
- [YosysHQ Discussions](https://github.com/YosysHQ/yosys/discussions)
- [#fpga on Libera.Chat IRC](https://libera.chat/)
- [/r/FPGA Subreddit](https://www.reddit.com/r/FPGA/)
- [FPGA Discord Server](https://discord.gg/FPGA)
- [1BitSquared Discord](https://discord.gg/BZDGgXU) - Open FPGA tools discussion

### Stochastic Computing Resources
- [UMN Stochastic Computing Group](https://www.ece.umn.edu/~lixx0599/stochastic.html) - Kia Bazargan's research
- [Stochastic Computing: Techniques and Applications](https://ieeexplore.ieee.org/document/6800465) (Alaghi & Hayes survey paper)
- [SC Toolbox for MATLAB](https://github.com/SCToolbox/SCToolbox)
- [Stochastic Computing GitHub Topic](https://github.com/topics/stochastic-computing)
- [LFSR Tutorial - FPGA4Fun](http://www.fpga4fun.com/LFSR.html)

### Testing & Verification
- [cocotb Documentation](https://docs.cocotb.org/)
- [cocotb GitHub](https://github.com/cocotb/cocotb)
- [Verilator Manual](https://verilator.org/guide/latest/)
- [GTKWave Documentation](http://gtkwave.sourceforge.net/)
- [Icarus Verilog](http://iverilog.icarus.com/)

### HDL Learning Resources
- [HDLBits](https://hdlbits.01xz.net/) - Interactive Verilog exercises
- [ASIC World Verilog Tutorial](http://www.asic-world.com/verilog/veritut.html)
- [ZipCPU Blog](https://zipcpu.com/) - Excellent FPGA tutorials by Dan Gisselquist
- [Nandland Verilog Tutorials](https://www.nandland.com/)
- [FPGAwars](https://github.com/FPGAwars) - Visual FPGA design tools

### Advanced Topics
- [SymbiYosys](https://github.com/YosysHQ/SymbiYosys) - Formal verification
- [FuseSoC](https://github.com/olofk/fusesoc) - HDL package manager
- [Litex](https://github.com/enjoy-digital/litex) - Python-based SoC builder
- [Amaranth HDL](https://github.com/amaranth-lang/amaranth) - Python-based HDL (formerly nMigen)

### Hardware Interfacing
- [sigrok/PulseView](https://sigrok.org/wiki/PulseView) - Open source logic analyzer software
- [Glasgow Interface Explorer](https://github.com/GlasgowEmbedded/glasgow) - Universal hardware tool
- [Bus Pirate](http://dangerousprototypes.com/docs/Bus_Pirate) - Hardware debugging tool

### Academic Papers on Stochastic Computing
- [Alaghi & Hayes (2013) "Survey of Stochastic Computing"](https://doi.org/10.1145/2465787.2465794)
- [Gaines (1969) "Stochastic Computing Systems"](https://doi.org/10.1007/978-1-4899-5841-9_5) - Original paper
- [Brown & Card (2001) "Stochastic Neural Computation"](https://doi.org/10.1145/368434.368573)
- [Qian et al. (2011) "LFSR-based Stochastic Computing"](https://doi.org/10.1109/FCCM.2011.29)

### LFSR & Pseudorandom Generation
- [Wikipedia: Linear-feedback shift register](https://en.wikipedia.org/wiki/Linear-feedback_shift_register)
- [Xilinx XAPP052: Efficient Shift Registers](https://www.xilinx.com/support/documentation/application_notes/xapp052.pdf)
- [Maximal Length LFSR Polynomials](https://users.ece.cmu.edu/~koopman/lfsr/)
- [LFSR Calculator Tool](https://www.ece.cmu.edu/~koopman/lfsr/index.html)

### Project Management & Documentation
- [Open Science Framework (OSF)](https://osf.io/) - For pre-registration
- [AsPredicted.org](https://aspredicted.org/) - Research pre-registration
- [Jupyter Notebooks](https://jupyter.org/) - For reproducible analysis
- [Overleaf](https://www.overleaf.com/) - Collaborative LaTeX editor
- [Zotero](https://www.zotero.org/) - Reference management

### Video Tutorials
- [Phil's Lab FPGA Tutorials](https://www.youtube.com/c/PhilsLab/videos)
- [Shawn Hymel FPGA Videos](https://www.youtube.com/playlist?list=PLEBQazB0HUyT1WmMONxRZn9NmQ_9CIKhb)
- [Robert Baruch "nmigen" Series](https://www.youtube.com/playlist?list=PLEeZWGE3PwbbjxV7_XnPSR7ouLR2zjktw)
- [Tang Nano 9K Getting Started](https://www.youtube.com/watch?v=ao1znjUp7X8)

### Books
- **"Digital Design and Computer Architecture"** by Harris & Harris - Excellent HDL fundamentals
- **"FPGA Prototyping by Verilog Examples"** by Pong P. Chu - Practical Verilog
- **"Stochastic Computing: Techniques and Applications"** - Comprehensive overview (if available)
- **"The Art of Electronics"** by Horowitz & Hill - For understanding hardware interfacing

### Online Courses
- [Coursera: FPGA Design for Embedded Systems](https://www.coursera.org/specializations/fpga-design)
- [edX: Hardware Description Languages](https://www.edx.org/learn/hardware)

### Gowin FPGA Specific (Alternative to Open Tools)
- [Gowin EDA Official](https://www.gowinsemi.com/en/support/home/) - Proprietary alternative
- [Gowin IP Cores](https://www.gowinsemi.com/en/support/ip/) - Pre-built modules (if needed)

### Your Research Domain
- **Quasicrystals**: [Penrose Tiling & Quasicrystals](https://en.wikipedia.org/wiki/Quasicrystal)
- **Chronobiology**: [Circadian Rhythms Research](https://www.nigms.nih.gov/education/fact-sheets/Pages/circadian-rhythms.aspx)
- **Optimization Theory**: [No Free Lunch Theorems](https://en.wikipedia.org/wiki/No_free_lunch_theorem)

### Troubleshooting & Support
- [Project Apicula Issues](https://github.com/YosysHQ/apicula/issues) - Report bugs
- [Yosys Issues](https://github.com/YosysHQ/yosys/issues)
- [Tang Nano Forum](https://bbs.sipeed.com/) - Official Sipeed forum
- [Stack Overflow [fpga] tag](https://stackoverflow.com/questions/tagged/fpga)