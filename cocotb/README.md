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

## Success Criteria

### Functional Verification
- ✅ All LFSR modules produce maximal-length sequences
- ✅ QBG mixing modes produce valid bitstreams
- ✅ Stochastic multiplication converges to correct values
- ✅ Hardware module synthesizes without errors

### Hypothesis Validation
- ✅ QBG modes show reduced autocorrelation vs baseline
- ✅ QBG modes maintain or improve multiplication accuracy
- ✅ Triple-LFSR shows further correlation reduction
- ✅ Results reproducible across multiple test runs

### Performance Metrics
- ✅ <1% error in stochastic multiplication (for P(A)×P(B) > 0.1)
- ✅ >50% reduction in autocorrelation peak vs baseline
- ✅ <5% variation in accuracy across mixing modes
- ✅ Successful synthesis on Tang Nano 9K

## Risk Mitigation

1. **Reference Implementation**: Python models for all Verilog modules
2. **Statistical Rigor**: Large sample sizes (10,000+ bits per test)
3. **Cross-validation**: Multiple test methods for each hypothesis
4. **Hardware Verification**: Oscilloscope validation of physical outputs

## Deliverables

1. **Complete test suite** with 100% coverage
2. **Statistical analysis reports** with charts and metrics
3. **Hypothesis validation results** (accept/reject with evidence)
4. **Hardware verification** on Tang Nano 9K
5. **Documentation** for replication and extension

---

*This plan provides a systematic approach to validating the QBG hypothesis through comprehensive simulation and hardware testing.*</content>
<parameter name="filePath">/home/chris/stochastic--REPL-core/cocotb/README.md