# Stochastic Computing REPL Core

An experimental implementation of stochastic computing with an interactive REPL interface.

## Architecture

This project implements a stochastic computing system using:
- **Lean 4**: Formal specifications and proofs of correctness
- **Verilog**: FPGA implementation on Tang Nano 9K
- **ELM11 Firmware**: Microcontroller REPL interface

## Components

### Lean 4 Formal Specifications (`lean-stochastic/`)
- Type definitions for stochastic numbers
- Theorems proving correctness of operations
- Formal verification of stochastic arithmetic

### Verilog HDL (`verilog/`)
- `sng.v`: Stochastic Number Generator using LFSR
- `stochastic_multiplier.v`: AND gate multiplier
- `stochastic_adder.v`: MUX-based scaled adder
- `bitstream_converter.v`: Bitstream to binary conversion
- `stochastic_repl_core.v`: Top-level FPGA module
- `tb_stochastic_repl_core.v`: Testbench

### ELM11 Firmware (`elm11-firmware/`)
- `stochastic_repl.ino`: Arduino-style REPL interface
- UART communication with FPGA
- Command parsing and execution

## Building

### Lean 4
```bash
cd lean-stochastic
lake build
```

### Verilog (using Gowin EDA for Tang Nano 9K)
1. Open project in Gowin IDE
2. Add Verilog files from `verilog/` directory
3. Synthesize and program FPGA

### ELM11 Firmware
Upload `stochastic_repl.ino` using Arduino IDE (configure for ELM11 board).

## Usage

1. Program FPGA with Verilog design
2. Upload firmware to ELM11
3. Connect ELM11 to FPGA via UART
4. Use serial terminal to interact:

```
> load a 128    # Load 0.5 into register a
> load b 64     # Load 0.25 into register b
> mul           # Compute a * b
> print r       # Print result (~0.125)
```

## Mathematical Foundation

See `math.md` for theorems behind stochastic computing.

## References

- ELM11-Lua-FFT: https://github.com/caston1981/ELM11-Lua-FFT
- PyCWT with FPGA backend: https://github.com/aptitudetechnology/bioxen-server-pycwt-mod