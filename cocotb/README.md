# Cocotb Testbench Plan for QBG Hypothesis Testing

## Overview
This document outlines the cocotb testbench implementation for validating the QBG (Quasiperiodic Bitstream Generator) hypothesis. The testbenches will verify that the Verilog implementation matches the expected stochastic computing behavior and test the core hypothesis: *Does quasiperiodic mixing reduce correlation in stochastic bitstreams?*

## Directory Structure
```
cocotb/
├── Makefile                    # Build and run scripts
├── requirements.txt           # Python dependencies
├── test_lfsr_primitives.py    # Test LFSR modules
├── test_qbg_dual_mixer.py     # Test dual-LFSR QBG hypothesis
├── test_qbg_triple_mixer.py   # Test triple-LFSR extension
├── test_sng_baseline.py       # Test control condition
├── test_stochastic_mult.py    # Test stochastic multiplication
├── test_qbg_top.py           # Test top-level module
├── utils/
│   ├── statistical_tests.py   # Correlation and randomness tests
│   ├── bitstream_analysis.py  # Bitstream quality metrics
│   └── reference_models.py    # Python reference implementations
└── results/                   # Test output and analysis
```

## Test Strategy

### 1. LFSR Primitive Tests (`test_lfsr_primitives.py`)

**Objectives:**
- Verify maximal-length sequences (periods: 255, 127, 511)
- Test reset behavior and non-zero seeds
- Validate polynomial implementations
- Check data_valid signals

**Test Cases:**
```python
def test_lfsr_8bit_maximal_period(dut):
    """Verify 8-bit LFSR produces period-255 sequence"""
    # Reset and run for 256 cycles
    # Assert no repeats in first 255 values
    # Assert period resets at 256th cycle

def test_lfsr_7bit_maximal_period(dut):
    """Verify 7-bit LFSR produces period-127 sequence"""
    # Similar to 8-bit test

def test_lfsr_9bit_maximal_period(dut):
    """Verify 9-bit LFSR produces period-511 sequence"""
    # Similar to 8-bit test

def test_lfsr_reset_behavior(dut):
    """Test reset returns to non-zero seed"""
    # Run some cycles, reset, verify returns to seed

def test_lfsr_enable_control(dut):
    """Test enable signal controls LFSR advancement"""
    # Enable high: advances, Enable low: holds
```

### 2. QBG Dual Mixer Tests (`test_qbg_dual_mixer.py`)

**Objectives:**
- Test all 4 mixing modes (00, 01, 10, 11)
- Verify quasiperiodic behavior reduces correlation
- Compare against baseline single-LFSR
- Validate golden ratio weighting

**Test Cases:**
```python
def test_qbg_single_mode(dut):
    """Mode 00: Single LFSR (baseline)"""
    # Should behave identically to sng_baseline

def test_qbg_dual_simple_average(dut):
    """Mode 01: Simple averaging of two LFSRs"""
    # Verify (lfsr1 + lfsr2) / 2 behavior
    # Check incommensurate periods don't correlate

def test_qbg_dual_golden_ratio(dut):
    """Mode 10: Golden ratio weighted mixing"""
    # Verify 0.618*lfsr1 + 0.382*lfsr2 approximation
    # Test correlation reduction

def test_qbg_dual_xor(dut):
    """Mode 11: XOR mixing"""
    # Verify lfsr1 ^ lfsr2 behavior
    # Alternative decorrelation method

def test_qbg_correlation_reduction(dut):
    """CORE HYPOTHESIS TEST: Does QBG reduce correlation?"""
    # Generate long bitstreams (10,000+ bits)
    # Compute autocorrelation vs baseline
    # Assert reduced correlation in QBG modes
```

### 3. Statistical Analysis Tests (`utils/statistical_tests.py`)

**Core Metrics:**
```python
def autocorrelation_test(bitstream, max_lag=100):
    """Compute autocorrelation function"""
    # Return correlation coefficients for lags 1-100

def correlation_coefficient(seq1, seq2):
    """Pearson correlation between two sequences"""
    # Measure linear dependence

def run_length_distribution(bitstream):
    """Analyze run lengths (streak analysis)"""
    # Should follow geometric distribution for random data

def chi_square_uniformity_test(bitstream, num_bins=16):
    """Test uniformity of bit distribution"""
    # Chi-square test for randomness

def spectral_test(bitstream):
    """FFT-based spectral analysis"""
    # Check for periodic components
```

### 4. Stochastic Multiplication Tests (`test_stochastic_mult.py`)

**Objectives:**
- Validate stochastic multiplication accuracy
- Compare QBG vs baseline performance
- Test different input probabilities

**Test Cases:**
```python
def test_stochastic_mult_accuracy(dut):
    """Test A × B computation accuracy"""
    # Test various probability pairs (0.1, 0.2, 0.5, 0.8, etc.)
    # Measure error vs theoretical A×B
    # Compare QBG vs baseline accuracy

def test_stochastic_mult_precision(dut):
    """Test precision vs bitstream length"""
    # Vary bitstream length (64, 256, 1024, 4096)
    # Measure convergence to true product
    # Plot precision vs length curves

def test_stochastic_mult_correlation_impact(dut):
    """Test how correlation affects multiplication"""
    # Same inputs, different mixing modes
    # Measure variance in results
    # Lower correlation should give more consistent results
```

### 5. Hardware Integration Tests (`test_qbg_top.py`)

**Objectives:**
- Test top-level module on Tang Nano 9K
- Verify pin mappings and timing
- Test debug LED functionality

**Test Cases:**
```python
def test_top_level_bitstream_generation(dut):
    """Test bitstream output on physical pins"""
    # Vary value_in (0-255)
    # Verify bitstream_led follows expected probability

def test_top_level_debug_leds(dut):
    """Test RGB LED debug outputs"""
    # Verify LED patterns match LFSR activity

def test_top_level_reset_behavior(dut):
    """Test reset button functionality"""
    # Active-low reset, proper synchronization
```

## Implementation Plan

### Phase 1: LFSR Verification (Week 1)
1. Implement LFSR testbenches
2. Verify maximal-length sequences
3. Generate reference sequences for comparison

### Phase 2: QBG Core Testing (Week 2)
1. Test all mixing modes
2. Implement statistical analysis
3. Run correlation reduction tests

### Phase 3: Application Validation (Week 3)
1. Stochastic multiplication tests
2. Accuracy and precision analysis
3. Performance comparison charts

### Phase 4: Hardware Integration (Week 4)
1. Top-level module tests
2. Timing and synchronization verification
3. Debug functionality validation

## Test Infrastructure

### Makefile Structure
```makefile
# Simulation targets
sim-lfsr: test_lfsr_primitives.py
	cocotb-run --module test_lfsr_primitives --top lfsr_8bit

sim-qbg: test_qbg_dual_mixer.py
	cocotb-run --module test_qbg_dual_mixer --top qbg_dual_mixer

sim-mult: test_stochastic_mult.py
	cocotb-run --module test_stochastic_mult --top stochastic_mult_test

# Analysis targets
analyze-correlation: results/
	python utils/statistical_tests.py --correlation

analyze-precision: results/
	python utils/statistical_tests.py --precision

# Hardware targets
synth: rtl/*.v
	yosys -p "synth_gowin -top qbg_test_top -json qbg.json" rtl/*.v

pnr: qbg.json
	nextpnr-gowin --json qbg.json --write qbg_pnr.json \
		--device GW1NR-LV9QN88PC6/I5 --cst tangnano9k.cst

pack: qbg_pnr.json
	gowin_pack -d GW1N-9C qbg_pnr.json -o qbg.fs
```

### Python Dependencies
```
cocotb>=1.8.0
numpy>=1.21.0
scipy>=1.7.0
matplotlib>=3.5.0
pandas>=1.3.0
pytest>=7.0.0
```

# Running the Tests

## Prerequisites

1. **Install Python dependencies:**
   ```bash
   pip install -r requirements.txt
   ```

2. **Install cocotb:**
   ```bash
   pip install cocotb
   ```

3. **Install Icarus Verilog (simulation backend):**
   ```bash
   # Ubuntu/Debian
   sudo apt-get install iverilog

   # Or using conda
   conda install -c conda-forge iverilog
   ```

## Test Execution

### Option 1: Run all tests with Makefile
```bash
# Run all tests
make test-all

# Run specific test suites
make test-lfsr      # Test LFSR primitives
make test-qbg       # Test QBG hypothesis (CORE TEST)
make test-mult      # Test stochastic multiplication
make test-top       # Test top-level integration

# Run with different simulators
make SIM=verilator test-all
make SIM=vcs test-all  # Commercial simulator
```

### Option 2: Run individual tests with Python script
```bash
# Run all tests
python run_tests.py

# Run specific test (requires manual Verilog file specification)
python -m pytest test_lfsr_primitives.py -v
```

### Option 3: Manual cocotb execution
```bash
# Example: Test LFSR primitives
cocotb-run \
  --module test_lfsr_primitives \
  --top lfsr_8bit \
  --sim icarus \
  --include ../verilog/rtl/primitives \
  ../verilog/rtl/primitives/lfsr_8bit.v \
  test_lfsr_primitives.py
```

## Test Results and Analysis

### Output Files
- `results/*.npz`: Raw test data and analysis results
- `results/*.png`: Generated plots and visualizations
- `results/test_report.md`: Comprehensive test report

### Key Metrics to Monitor
- **Cross-correlation reduction**: > 50% for hypothesis support
- **Autocorrelation improvement**: > 30% reduction
- **Spectral flatness**: > 70% for good randomness
- **Multiplication accuracy**: QBG should outperform baseline

### Interpreting Results
The core hypothesis test (`test_qbg_dual_mixer.py`) will output:
```
Correlation Analysis Results:
  Cross-correlation reduction: 0.734
  Autocorrelation improvement: 0.456
  Spectral flatness: 0.823
  Hypothesis supported: True
```

## Debugging

### Common Issues

1. **Import errors**: Ensure `PYTHONPATH` includes the `utils/` directory
   ```bash
   export PYTHONPATH=$PWD/utils:$PYTHONPATH
   ```

2. **Verilog compilation errors**: Check file paths in test files match your Verilog structure

3. **Simulation hangs**: Use `make GUI=1` to enable waveform viewer for debugging

### Viewing Waveforms
```bash
# Run test with waveform output
make GUI=1 test-qbg

# Or manually
cocotb-run --module test_qbg_dual_mixer --top qbg_dual_mixer --sim icarus --gui 1 [files...]
```

## Performance Optimization

### Simulation Speed
- Use `verilator` for faster simulation: `make SIM=verilator`
- Reduce sample counts in tests for quicker iteration
- Use `pytest -x` to stop on first failure

### Memory Usage
- Large bitstream collections may require significant RAM
- Consider reducing `num_samples` for memory-constrained systems

## Integration with Hardware Testing

After successful simulation:
1. Run `make report` to generate synthesis-ready metrics
2. Use Tang Nano 9K toolchain for FPGA implementation
3. Compare simulation results with hardware measurements
4. Validate correlation reduction in actual stochastic circuits

## Troubleshooting

### Dependencies
```bash
# Check cocotb installation
python -c "import cocotb; print(cocotb.__version__)"

# Check Verilog simulator
iverilog -V

# Check Python packages
pip list | grep -E "(numpy|scipy|matplotlib)"
```

### Test Failures
- Check Verilog file paths match your directory structure
- Ensure LFSR periods match test expectations (255, 127, 511)
- Verify clock and reset timing in testbenches
- Check that Verilog modules have correct port names

### Performance Issues
- Use `SIM=verilator` for better performance
- Reduce test sample sizes for faster iteration
- Run tests in parallel if system supports it
````