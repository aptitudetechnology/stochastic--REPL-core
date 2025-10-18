# Stochastic Computing REPL Core ⚡

An innovative **Read-Eval-Print Loop (REPL)** for stochastic computing operations, where every computation is backed by **formal mathematical verification**. This project combines the exploratory power of interactive programming with the certainty of proven mathematics, enabling trustworthy experimentation with probabilistic hardware computing.

## What is a REPL? 🔄

A **REPL** (Read-Eval-Print Loop) is an interactive programming environment that:
- **Reads** user input (commands)
- **Evaluates** those commands (executes code)
- **Prints** the results
- **Loops** back for the next command

Traditional REPLs like Python's `python3` or Lisp's REPL enable exploratory programming. Our innovation: a REPL where "Eval" performs **stochastic computing operations** on actual FPGA hardware, with every operation mathematically verified for correctness.

## What is Stochastic Computing? 🎲

**Stochastic computing** represents numbers as probabilities in bitstreams:
- `0.5` = exactly 128 ones in a 256-bit stream
- `0.25` = exactly 64 ones in a 256-bit stream
- Operations use simple logic gates instead of complex arithmetic circuits

**Key insight**: Trade precision for hardware simplicity
- **Multiplication**: Just an AND gate! `P(A ∧ B) = P(A) × P(B)`
- **Addition**: A multiplexer (MUX) circuit
- **No complex multipliers or adders needed**

This enables ultra-low-power, area-efficient computing perfect for edge devices and IoT.

## The REPL Core Architecture 🏗️

"Core" here means the **fundamental evaluation engine** (not CPU cores). Our REPL follows the classic pattern but with stochastic operations:

```
User Command → Parse → Execute on FPGA → Convert Result → Display
     ↑                                                            ↓
   Read                                                        Print
     ↓                                                            ↑
   Eval ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← ← Loop
```

- **Read**: Parse commands like `load a 128`, `mul`, `print r`
- **Eval**: Execute stochastic operations on Tang Nano 9K FPGA hardware
- **Print**: Convert bitstream results to human-readable probabilities
- **Loop**: Return to read state for next command

## System Components with Verification Stack 🔍

Our system builds trust through **layered verification** - from mathematical theorems to working hardware:

### Lean 4 - Formal Verification (Development Time) 📐
**Proves stochastic operations are mathematically correct for ALL cases**
- Example: Proves that `P(A ∧ B) = P(A) × P(B)` for independent bitstreams
- Verifies AND gates really multiply, MUX circuits really add
- Establishes error bounds and convergence rates for different bitstream lengths
- **Critical for trust**: Users can rely on results because the math is proven sound
- Unlike tests (which check specific cases), Lean proves correctness universally

### Verilog - Hardware Implementation (Tang Nano 9K FPGA) 🔧
**Implements the verified algorithms in actual hardware**
- LFSR-based Stochastic Number Generator (SNG)
- AND gate multiplier (proven correct by Lean theorems)
- MUX-based scaled adder (proven correct by Lean theorems)
- Bitstream converters and register management

### ELM11 Firmware - REPL Interface (Runtime) 💻
**Lua-based interactive shell orchestrating FPGA operations**
- Arduino-style firmware running on ELM11 microcontroller
- UART communication with FPGA
- Command parsing: `load`, `mul`, `add`, `print`
- Manages register state and result formatting

### Python Tests - Verification Bridge 🧪
**End-to-end testing ensuring theory matches implementation**
- Verifies Verilog simulation matches Lean proofs
- Tests complete chain: theory → hardware → results
- Confirms stochastic accuracy within expected bounds

## The Verification Philosophy 🏛️

```
Lean 4 Theorems          →  "Multiplication SHOULD work this way"
       ↓
Verilog Implementation   →  "Here's the actual hardware"
       ↓
Python Tests            →  "Does it match the theory?"
       ↓
REPL Interface          →  User experiments interactively
```

When you type `mul`, you can **trust** the result because:
- ✅ Lean proved the algorithm is mathematically sound (development time)
- ✅ Verilog implemented it correctly in hardware
- ✅ Tests verified implementation matches proof
- ✅ The REPL orchestrates the verified operations (runtime)

## Why Formal Verification Matters 🤔

**Tests show it works for specific cases. Lean proves it works for ALL cases.**

- **Hardware is expensive to fix** - once fabricated, you can't patch bugs
- **Probabilistic computing needs certainty** - users must trust statistical results
- **Mathematical guarantees** about error bounds and accuracy
- **Builds confidence** in experimental probabilistic systems

Without formal verification, stochastic computing remains "experimental." With it, becomes a trustworthy foundation for probabilistic hardware.

## Example Session 🎮

```
> load a 128    # Load 0.5 into register a (128/256 = 0.5)
> load b 64     # Load 0.25 into register b (64/256 = 0.25)
> mul           # Evaluate: stochastic multiplication on FPGA (Lean-verified)
> print r       # Print result: ~0.125 (0.5 × 0.25 = 0.125)
```

The beauty: you're not just getting a number - you're getting a **mathematically proven correct** result from probabilistic hardware!

## Architecture Overview 🗺️

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│   Lean 4       │    │   Verilog        │    │   ELM11 Lua     │
│   Theorems      │    │   FPGA Design    │    │   REPL Shell    │
│                 │    │                  │    │                 │
│ • P(A∧B)=P(A)× │    │ • LFSR SNG       │    │ • Command Parse │
│   P(B)          │    │ • AND Multiplier │    │ • UART Comm     │
│ • Error Bounds  │    │ • MUX Adder      │    │ • Result Format │
│ • Convergence   │    │ • Converters     │    │                 │
└─────────────────┘    └──────────────────┘    └─────────────────┘
         ↓                        ↓                        ↓
┌─────────────────────────────────────────────────────────────┐
│                Python End-to-End Tests                      │
│  Verifies: Lean Theory ↔ Verilog Implementation ↔ Results   │
└─────────────────────────────────────────────────────────────┘
```

## Building Instructions 🛠️

### Prerequisites
- Lean 4 (for formal verification)
- Gowin EDA or Project Apicula (for FPGA synthesis)
- Arduino IDE (for ELM11 firmware)
- Python 3 (for testing)

### Lean 4 Formal Verification
```bash
cd lean-stochastic
lake build
```
This builds the mathematical theorems proving stochastic operations correct.

### Verilog Synthesis (Tang Nano 9K)
**Option A: Gowin EDA (Proprietary)**
1. Open project in Gowin IDE
2. Add Verilog files from `verilog/` directory
3. Synthesize and program FPGA

**Option B: Project Apicula (Open Source)**
```bash
# Synthesize
yosys synth.ys

# Place and route
nextpnr-gowin --json design.json --write pnr.json --device GW1NR-9

# Generate bitstream
gowin_pack -d GW1NR-9 -o bitstream.fs pnr.json

# Program FPGA
openFPGALoader -b tangnano9k bitstream.fs
```
See [`apicula.md`](apicula.md) for detailed setup.

### ELM11 Firmware
1. Configure Arduino IDE for ELM11 board
2. Upload `elm11-firmware/stochastic_repl.ino`
3. Connect ELM11 UART to FPGA UART pins

## Usage Examples 📚

### Basic Operations
```
> load a 128    # 0.5
> load b 64     # 0.25
> mul           # a * b = 0.125
> print r       # Display result
```

### Advanced Operations
```
> load x 192    # 0.75
> load y 32     # 0.125
> add           # x + y = 0.875 (scaled addition)
> print r
```

### Stochastic Exploration
```
> load chaos 128  # 0.5
> mul             # Multiply by itself repeatedly
> mul             # Watch convergence to 0.25
> print r
```

## Testing Procedures ✅

Run comprehensive tests validating the proof-to-implementation chain:

```bash
# Complete verification suite
python3 tests/test_end_to_end.py

# Individual component tests
python3 tests/test_lean.py          # Lean theorem validation
python3 tests/test_verilog.py       # Verilog simulation accuracy
python3 tests/test_lua_repl.py      # REPL command parsing
```

**Expected Accuracy**: ±1% for 1024-bit streams, improving with longer streams.

## Mathematical Foundation 📖

The system is grounded in probability theory and information theory. Key theorems proven in Lean 4:

- **Multiplication Theorem**: `P(A ∧ B) = P(A) × P(B)` for independent bitstreams
- **Addition Bounds**: Error analysis for scaled addition operations
- **Convergence Rates**: How accuracy improves with bitstream length
- **Correlation Effects**: Impact of bitstream dependencies

See [`math.md`](math.md) for complete mathematical treatment.

## Innovation Highlights 🚀

1. **REPL + Formal Verification**: Interactive exploration with mathematical certainty
2. **Hardware-Backed Probabilities**: Not simulation - real stochastic computing on FPGA
3. **Layered Trust**: From theorems to hardware to user results
4. **Ultra-Low Power Computing**: Simple gates replace complex arithmetic
5. **Educational Platform**: Learn stochastic computing through verified experimentation

## Related Projects 🔗

- [ELM11-Lua-FFT](https://github.com/caston1981/ELM11-Lua-FFT) - Lua FFT on ELM11
- [PyCWT FPGA Backend](https://github.com/aptitudetechnology/bioxen-server-pycwt-mod) - FPGA-accelerated wavelet transforms
- [Stochastic Space Invaders](games/spaceinvaders/) - Educational stochastic computing game

## Contributing 🤝

This project welcomes contributions in:
- Lean 4 theorem development
- Verilog optimizations
- Firmware enhancements
- Documentation improvements
- Educational examples

---

**Trust through Mathematics • Explore through Interaction • Compute through Probability** ⚡