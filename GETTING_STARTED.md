# Getting Started with Stochastic Computing REPL

## Quick Start (5 minutes)

### 1. Install Dependencies

```bash
# Install Lean 4 (if not already installed)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Install open-source FPGA toolchain
# On Ubuntu/Debian:
sudo apt-get install yosys nextpnr-gowin gowin-pack openfpgaloader

# On macOS:
brew install yosys
# For other tools, see apicula.md

# Install Python dependencies for testing
pip3 install numpy matplotlib
```

### 2. Build and Test

```bash
# Clone the repository
git clone https://github.com/aptitudetechnology/stochastic--REPL-core
cd stochastic--REPL-core

# Run all tests
make test

# This will:
# - Build Lean 4 formal proofs
# - Run Verilog simulation
# - Execute Python accuracy tests
```

### 3. Synthesize for FPGA

```bash
# Build FPGA bitstream
make bitstream

# Program Tang Nano 9K
make program
```

### 4. Try the Web Visualizer

Open `visualization.html` in your browser to interactively explore stochastic computing operations.

---

## Understanding Stochastic Computing

### What is it?

Stochastic computing represents numbers as random bitstreams where the probability of a '1' equals the number's value.

**Example:**
- 0.5 → `10110101...` (roughly 50% ones)
- 0.25 → `00100001...` (roughly 25% ones)

### Why use it?

✅ **Ultra-simple hardware**: Multiply = AND gate, Add = MUX  
✅ **Fault tolerant**: Bit errors just add noise  
✅ **Low power**: Minimal logic complexity  
✅ **Progressive precision**: Can stop computation early  

❌ **Trade-offs**:  
- Long computation time (need many bits for accuracy)
- Limited to [0, 1] range (without extensions)
- Correlation issues between bitstreams

---

## Project Structure

```
stochastic-REPL-core/
├── lean-stochastic/          # Formal verification (Lean 4)
│   ├── StochasticComputing.lean
│   └── Basic.lean
├── verilog/                  # FPGA implementation
│   ├── sng.v                 # Stochastic Number Generator
│   ├── stochastic_multiplier.v
│   ├── stochastic_adder.v
│   └── stochastic_repl_core.v
├── elm11-firmware/           # Microcontroller interface
│   └── stochastic_repl.{ino,lua}
├── tests/                    # Test suite
└── Makefile                  # Build automation
```

---

## Example Usage

### Software Simulation (Python)

```python
from tests.test_stochastic_accuracy import StochasticSimulator

# Create simulator
sim = StochasticSimulator()

# Generate bitstreams for 0.5 and 0.75
a = sim.generate_bitstream(0.5, length=1024)
b = sim.generate_bitstream(0.75, length=1024)

# Multiply (0.5 × 0.75 = 0.375)
result = sim.multiply(a, b)
print(f"0.5 × 0.75 ≈ {result:.4f}")  # ~0.375

# Add (average: (0.5 + 0.75)/2 = 0.625)
result = sim.scaled_add(a, b)
print(f"(0.5 + 0.75)/2 ≈ {result:.4f}")  # ~0.625
```

### FPGA REPL (when hardware is connected)

```
> load a 128    # Load 0.5 (128/256) into register a
> load b 192    # Load 0.75 (192/256) into register b
> mul           # Multiply: a × b
> print r       # Print result (~96, which is 0.375 × 256)
```

### Lean 4 Formal Proof

```lean
-- From lean-stochastic/StochasticComputing.lean
theorem stochastic_multiply_correct :
  ∀ (a b : StochasticNumber),
    E[multiply a b] = E[a] * E[b]
```

---

## Common Tasks

### Add a New Operation

1. **Define in Lean** (`lean-stochastic/StochasticComputing.lean`):
```lean
def square (x : StochasticNumber) : StochasticNumber :=
  multiply x x

theorem square_correct : E[square x] = E[x]^2 := sorry
```

2. **Implement in Verilog** (`verilog/stochastic_square.v`):
```verilog
module stochastic_square(
    input wire clk,
    input wire x,
    output reg result
);
    always @(posedge clk) begin
        result <= x & x;  // Same as multiply(x, x)
    end
endmodule
```

3. **Add to REPL** (`elm11-firmware/stochastic_repl.lua`):
```lua
elseif cmd == "square" then
    -- Send square command to FPGA
    send_to_fpga("SQR")
```

4. **Test**:
```python
# In tests/test_operations.py
def test_square():
    sim = StochasticSimulator()
    x = sim.generate_bitstream(0.6, 1024)
    result = sim.multiply(x, x)
    assert abs(result - 0.36) < 0.02
```

### Increase Accuracy

Accuracy improves with longer bitstreams:

| Stream Length | Typical Error |
|---------------|---------------|
| 128 bits      | ±2%           |
| 256 bits      | ±1%           |
| 1024 bits     | ±0.5%         |
| 4096 bits     | ±0.25%        |

Edit `verilog/stochastic_repl_core.v`:
```verilog
parameter STREAM_LENGTH = 1024;  // Increase this
```

### Debug Correlation Issues

Stochastic computing is sensitive to correlated bitstreams:

```bash
# Run correlation test
python3 tests/test_stochastic_accuracy.py

# Look for "CORRELATION EFFECTS TEST" output
```

**Solution**: Ensure independent LFSRs with different seeds in `sng.v`.

---

## Troubleshooting

### "lake: command not found"
Install Lean 4's package manager:
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
```

### "nextpnr-gowin: No such file"
See `apicula.md` for detailed installation instructions for your platform.

### FPGA programming fails
```bash
# Check if Tang Nano 9K is detected
lsusb | grep -i gowin

# Try manual programming
openFPGALoader -b tangnano9k build/stochastic_repl.fs
```

### High error in results
- Increase `STREAM_LENGTH` in Verilog
- Check for bitstream correlation
- Verify SNG LFSR seeds are different

---

## Next Steps

1. **Read the theory**: See `math.md` for mathematical foundations
2. **Explore examples**: Run `python3 tests/test_stochastic_accuracy.py`
3. **Try visualization**: Open `visualization.html`
4. **Add operations**: Implement division, square root, etc.
5. **Optimize hardware**: Reduce FPGA resource usage

---

## Resources

- [Stochastic Computing: A Survey](https://dl.acm.org/doi/10.1145/2465787.2465794)
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Tang Nano 9K Documentation](https://wiki.sipeed.com/hardware/en/tang/Tang-Nano-9K/Nano-9K.html)
- [Project Apicula](https://github.com/YosysHQ/apicula)

---

## Contributing

We welcome contributions! Areas of interest:
- Additional operations (division, exp, log, trig functions)
- Better correlation handling
- Power consumption analysis
- Application examples
- Documentation improvements

See `CONTRIBUTING.md` for guidelines (TODO).