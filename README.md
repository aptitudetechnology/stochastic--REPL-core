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

## Testing

Run the test suite to verify all components:

```bash
# Run all tests
python3 tests/test_end_to_end.py

# Run individual tests
python3 tests/test_lean.py          # Lean 4 formal verification
python3 tests/test_verilog.py       # Verilog simulation
python3 tests/test_lua_repl.py      # Lua REPL functionality
```

## FPGA Serial Communication

The ELM11 Lua firmware includes placeholders for FPGA communication. Once the Tang Nano 9K is programmed with the Verilog design:

1. Connect ELM11 UART TX/RX to FPGA UART pins
2. Update the `send_to_fpga()` and `receive_from_fpga()` functions in `elm11-firmware/stochastic_repl.lua`
3. The FPGA will handle stochastic bitstream generation and arithmetic operations

## End-to-End Testing

The `test_end_to_end.py` script verifies:
- Lean 4 theorem correctness
- Verilog module simulation
- Lua command parsing
- Stochastic computation accuracy

Expected accuracy: ±1% for 1024-bit streams, improving with longer streams.

## Mathematical Foundation

See `math.md` for theorems behind stochastic computing.

## References

- ELM11-Lua-FFT: https://github.com/caston1981/ELM11-Lua-FFT
- PyCWT with FPGA backend: https://github.com/aptitudetechnology/bioxen-server-pycwt-mod