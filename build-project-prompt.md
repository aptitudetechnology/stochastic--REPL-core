# GitHub Copilot Prompt: Stochastic Computing REPL Core Implementation

## Project Context

You are implementing a **Stochastic Computing REPL Core** - an experimental computer architecture that performs computations using streams of random bits rather than traditional binary logic. This system combines:

1. **Stochastic Computing (SC)**: Numerical values represented as bitstreams where the probability of "1" represents the value (e.g., 75% ones = 0.75)
2. **REPL Interface**: Interactive Read-Eval-Print Loop for command execution
3. **Formal Verification**: Using Lean 4 for mathematical proofs of correctness

## Hardware Platform

- **FPGA**: Tang Nano 9K (Gowin GW1NR-9, ~8,640 LUTs)
- **Controller**: ELM11 with REPL cores
- **Programming Language**: Lean v4 for formal specification and verification

## Reference Implementations

Study these existing projects for ELM11 and Tang Nano 9K integration patterns:

### ELM11-Lua-FFT
**Repository**: https://github.com/caston1981/ELM11-Lua-FFT

This project demonstrates:
- ELM11 Lua scripting integration
- FFT implementation on embedded hardware
- Communication protocols between controller and external hardware
- Real-time signal processing patterns

**Key learnings to apply**:
- Review the ELM11 API usage and initialization patterns
- Understand how Lua scripts interface with hardware
- Study buffer management and data flow for DSP operations
- Examine timing and synchronization approaches

### Bioxen Server with PyCWT
**Repository**: https://github.com/aptitudetechnology/bioxen-server-pycwt-mod

This project shows:
- Server architecture for embedded systems
- Python-based wavelet transform integration
- Communication protocols and data streaming
- Integration between high-level processing and embedded controllers

**Key learnings to apply**:
- Communication protocol design between host and embedded system
- Data serialization strategies for numerical data
- Error handling and robust communication patterns
- Testing and validation approaches for signal processing systems

### Integration Strategy for Stochastic REPL

When implementing the stochastic computing REPL:
1. **Adapt communication patterns** from these projects for UART-based REPL commands
2. **Follow initialization sequences** similar to those used in ELM11-Lua-FFT
3. **Use buffer management techniques** from the FFT implementation for bitstream handling
4. **Apply protocol design principles** from bioxen-server for robust command parsing
5. **Study timing patterns** to ensure adequate settling time for stochastic computations

## Core Architecture Components

### 1. Stochastic Number Generators (SNGs)
- Generate pseudo-random bitstreams using LFSRs (Linear Feedback Shift Registers)
- Multiple independent generators required to prevent correlation errors
- Must produce uniformly distributed bits

### 2. Stochastic Arithmetic Units
- **Multiplication**: Single AND gate (P(A AND B) = P(A) × P(B))
- **Scaled Addition**: Multiplexer/MUX (P(MUX(A,B,S)) = P(S)×P(A) + (1-P(S))×P(B))
- **Correlation Detection**: XNOR gates
- All operations use simple logic gates for low power consumption

### 3. Bitstream Converters
- **Input**: Binary to stochastic bitstream (SNG)
- **Output**: Bitstream to binary (simple counter)
- Precision depends on bitstream length: ±ε requires ~1/ε² bits

### 4. REPL Command Processor
- Parse user commands via UART
- Execute stochastic operations
- Convert results back to decimal
- Support variable precision settings

## Implementation Requirements

### Lean 4 Formal Specifications
When writing Lean 4 code, include:
- **Type definitions** for stochastic numbers and bitstreams
- **Theorems** proving correctness of stochastic operations
- **Proofs** of error bounds for finite-length bitstreams
- **Lemmas** establishing independence of random sources
- **Verified functions** that can extract to executable code

Example structure:
```lean
-- Define stochastic number type
def StochasticNum := List Bool

-- Prove multiplication correctness
theorem stoch_mul_correct : ∀ (a b : Real) (sa sb : StochasticNum),
  represents sa a → represents sb b → 
  represents (stoch_and sa sb) (a * b)
```

### Verilog/VHDL for Tang Nano 9K
When generating HDL code:
- **Modular design**: Separate modules for SNG, arithmetic units, converters
- **Parameterized bitstream lengths**: Support 8, 16, 32, 64, 128, 256 bits
- **Multiple LFSR polynomials**: Ensure independent random sources
- **Clock domain considerations**: Synchronous design at consistent frequency
- **Resource optimization**: Efficient use of LUTs and registers

### ELM11 Controller Integration
- **UART communication**: 115200 baud, 8N1 standard
- **Command parser**: Text-based protocol
- **State machine**: Track REPL state (idle, computing, outputting)
- **Buffer management**: Handle bitstream data flow

## Key Design Constraints

### Precision vs. Latency Tradeoff
- 1% precision: ~10,000 bits
- 0.1% precision: ~1,000,000 bits
- Implement adaptive precision based on operation requirements

### Correlation Prevention
- Use independent LFSRs with different feedback polynomials
- Rotate/shift sequences for decorrelation
- Prove independence properties formally in Lean 4

### Number Format Options
- **Unipolar [0, 1]**: Simpler implementation, limited range
- **Bipolar [-1, 1]**: More general, requires dual bitstreams or special encoding

## REPL Command Set

Implement these core commands:
```
load <reg> <value>        # Load decimal value into register (convert to bitstream)
mul <dest> <src1> <src2>  # Multiply two stochastic numbers
add <dest> <src1> <src2> <weight>  # Weighted addition using MUX
print <reg>               # Convert bitstream to decimal and display
precision <bits>          # Set bitstream length (8-256)
reset                     # Reset all registers
help                      # Display available commands
```

## Code Generation Guidelines

### For Lean 4 Files (.lean)
- Start with clear type definitions
- Include documentation strings for all theorems
- Prove properties incrementally (existence, uniqueness, correctness, bounds)
- Use tactics: `simp`, `ring`, `linarith`, `norm_num`
- Extract verified code using `#eval` or code generation

### For Verilog Files (.v)
- Use meaningful signal names (e.g., `lfsr_out`, `bitstream_a`, `stoch_result`)
- Include comments explaining stochastic computing principles
- Add testbench modules with assertions
- Parameterize with `parameter` keyword for flexibility

### For C/C++ Files (ELM11 firmware)
- Use state machine pattern for REPL loop
- Implement circular buffers for bitstream handling
- Add error checking for malformed commands
- Include timing measurements for performance analysis

## Testing Strategy

### Unit Tests
- SNG uniformity tests (chi-squared test)
- Arithmetic operation correctness (compare to exact values)
- Bitstream converter accuracy across range

### Integration Tests
- End-to-end command execution
- Multi-operation sequences (e.g., a*b + c*d)
- Edge cases: 0.0, 1.0, 0.5 values
- Precision sweep tests (8 to 256 bits)

### Formal Verification
- Prove all Lean 4 theorems
- QuickCheck-style property testing on extracted code
- FPGA simulation with formal properties

## Expected Deliverables

Generate code for:
1. **Lean 4 library**: Formal specifications and proofs (`StochasticComputing.lean`)
2. **Verilog modules**: SNG, arithmetic units, converters, top-level REPL core
3. **ELM11 firmware**: UART handler, command parser, FPGA interface
4. **Testbenches**: Simulation and verification code
5. **Documentation**: Architecture diagrams, API reference, usage examples

## Research Context

This is cutting-edge research combining:
- Formal methods (Lean 4 theorem proving)
- Computer architecture (stochastic computing)
- Embedded systems (FPGA + microcontroller)
- Approximate computing (energy-accuracy tradeoffs)

Applications include:
- Energy-efficient neural network inference
- Fault-tolerant signal processing
- Low-power embedded AI
- Probabilistic computing research

## Coding Style Preferences

- **Lean 4**: Functional style, clear proof structure, minimal tactics when possible
- **Verilog**: Behavioral for testbenches, structural for synthesis
- **C/C++**: Modern C++17 for ELM11, with RAII and strong typing
- **Comments**: Explain *why* (especially stochastic computing principles), not *what*
- **Naming**: Descriptive names that reflect stochastic computing concepts

---

**When generating code, prioritize correctness and clarity over cleverness. This is research-grade code that should be publishable and serve as a reference implementation.**