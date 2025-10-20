# Testable Hypothesis: Quasiperiodic Bitstream Generation

## Research Question

Can dual-LFSR quasiperiodic mixing, inspired by the mathematical principles of discrete time quasicrystals, reduce correlation artifacts and improve accuracy in stochastic computing operations?

---

## Hypothesis Statement

**Primary Hypothesis (H1):**
> Stochastic multiplication and addition operations using bitstreams generated from two LFSRs with incommensurate periods, mixed quasiperiodically, will exhibit **10-30% lower error** compared to operations using bitstreams from a single LFSR, when measured over 1000 trials with 256-bit streams.

**Null Hypothesis (H0):**
> There is no statistically significant difference in error rates between single-LFSR and dual-LFSR quasiperiodic bitstream generation for stochastic computing operations.

**Secondary Hypothesis (H2):**
> The autocorrelation function of quasiperiodically-mixed dual-LFSR bitstreams will show **at least 20% lower peak autocorrelation** (excluding zero lag) compared to single-LFSR bitstreams.

---

## Variables

### Independent Variables
1. **Bitstream generation method**
   - Control: Single LFSR (standard approach)
   - Experimental: Dual LFSR with quasiperiodic mixing

2. **Mixing parameters** (for experimental condition)
   - τ₁/τ₂ ratio: {1.5, 1.618 (golden ratio), 1.732 (√3), 2.0}
   - Epsilon (mixing strength): {0.1, 0.3, 0.5}

3. **LFSR configurations**
   - Single: 8-bit LFSR (period 255)
   - Dual: 8-bit (period 255) + 7-bit (period 127)

### Dependent Variables
1. **Absolute error** in stochastic operations
   - For multiplication: |P(A)×P(B) - measured_result|
   - For addition: |0.5×(P(A)+P(B)) - measured_result|

2. **Autocorrelation peak** (max value excluding lag=0)

3. **Standard deviation** of errors across trials

### Controlled Variables
- Bitstream length: 256 bits
- Number of trials: 1000 per condition
- Test values: P(A) ∈ {0.25, 0.5, 0.75}, P(B) ∈ {0.25, 0.5, 0.75}
- Hardware: Same FPGA/simulation environment
- Temperature: Room temperature (20-25°C)

---

## Experimental Design

### Phase 1: Python Simulation (Week 1)

**Setup:**
```python
# Control group
def single_lfsr_bitstream(length=256, seed=42):
    """Standard 8-bit LFSR (x^8 + x^6 + x^5 + x^4 + 1)"""
    pass

# Experimental group
def dual_lfsr_quasiperiodic(length=256, tau1=1.0, tau2=1.618, epsilon=0.3):
    """Two LFSRs mixed with quasiperiodic weighting"""
    pass
```

**Test Cases:**
```
Multiplication tests: 9 combinations of P(A) × P(B)
  (0.25, 0.25) → expected 0.0625
  (0.25, 0.50) → expected 0.125
  (0.25, 0.75) → expected 0.1875
  (0.50, 0.25) → expected 0.125
  (0.50, 0.50) → expected 0.25
  (0.50, 0.75) → expected 0.375
  (0.75, 0.25) → expected 0.1875
  (0.75, 0.50) → expected 0.375
  (0.75, 0.75) → expected 0.5625

Addition tests: Same 9 combinations
  Formula: 0.5 × (P(A) + P(B))
```

**Metrics per test:**
- Run 1000 trials
- Calculate mean absolute error
- Calculate standard deviation
- Measure autocorrelation

### Phase 2: Statistical Analysis

**Required for H1 acceptance:**
1. Mean error reduction ≥ 10% (p < 0.05, two-tailed t-test)
2. Improvement consistent across at least 75% of test cases
3. Effect size (Cohen's d) ≥ 0.3 (small to medium effect)

**Required for H2 acceptance:**
1. Autocorrelation peak reduction ≥ 20% (p < 0.05)
2. Reduction consistent across all mixing parameters tested

### Phase 3: Hardware Validation (Week 2-3)

**Tang Nano 9K FPGA Implementation:**
```verilog
// Implement both methods in Verilog
// Compare power consumption
// Measure actual timing
// Validate against simulation
```

**Success Criteria:**
- Hardware results within 5% of simulation predictions
- Power consumption increase < 20% vs single LFSR
- Timing closure at 27 MHz clock

### Phase 4: CMOS Validation (Week 4)

**4000-series discrete implementation:**
```
CD4094 × 2 (dual LFSRs)
CD4053     (mixing/MUX)
CD4081     (AND gates for multiplication)
```

**Success Criteria:**
- Matches FPGA results within 10%
- Power consumption < 1 µW measured
- Validates formal verification chain

---

## Measurement Protocol

### Error Measurement
```python
def measure_error(method, P_A, P_B, operation='multiply', trials=1000):
    errors = []
    for trial in range(trials):
        # Generate bitstreams
        stream_A = method.generate(P_A, length=256)
        stream_B = method.generate(P_B, length=256)
        
        # Perform operation
        if operation == 'multiply':
            result_stream = bitwise_and(stream_A, stream_B)
            expected = P_A * P_B
        elif operation == 'add':
            result_stream = mux_add(stream_A, stream_B)
            expected = 0.5 * (P_A + P_B)
        
        # Measure result
        measured = count_ones(result_stream) / 256
        errors.append(abs(measured - expected))
    
    return {
        'mean_error': np.mean(errors),
        'std_error': np.std(errors),
        'max_error': np.max(errors),
        'min_error': np.min(errors)
    }
```

### Autocorrelation Measurement
```python
def measure_autocorrelation(bitstream):
    """
    Compute normalized autocorrelation
    Return peak value excluding lag=0
    """
    autocorr = np.correlate(bitstream, bitstream, mode='full')
    autocorr = autocorr / autocorr[len(bitstream)-1]  # Normalize
    
    # Remove zero lag (always 1.0)
    middle = len(autocorr) // 2
    autocorr = np.delete(autocorr, middle)
    
    return np.max(np.abs(autocorr))
```

---

## Expected Results

### Optimistic Scenario (H1 supported)
```
Single LFSR:
  Mean error (multiply): 0.0391 (1/√256 theoretical)
  Mean error (add):      0.0391
  Autocorr peak:         0.15

Dual LFSR (golden ratio, ε=0.3):
  Mean error (multiply): 0.0293 (25% reduction) ✓
  Mean error (add):      0.0301 (23% reduction) ✓
  Autocorr peak:         0.11 (27% reduction) ✓
  
Statistical significance: p < 0.001
Effect size: d = 0.45 (medium)
```

### Realistic Scenario (H1 partially supported)
```
Single LFSR:
  Mean error: 0.0391
  Autocorr peak: 0.15

Dual LFSR:
  Mean error: 0.0352 (10% reduction) ✓
  Autocorr peak: 0.12 (20% reduction) ✓
  
Statistical significance: p < 0.05
Effect size: d = 0.25 (small)
Conclusion: Modest but measurable improvement
```

### Null Scenario (H0 cannot be rejected)
```
Single LFSR:
  Mean error: 0.0391

Dual LFSR:
  Mean error: 0.0385 (1.5% reduction - not significant)
  
Statistical significance: p = 0.23 (ns)
Effect size: d = 0.08 (negligible)
Conclusion: No meaningful improvement
```

---

## Success Criteria

### Minimum Viable Results (MVR)
To proceed with hardware implementation and publication:

1. ✅ **Mean error reduction ≥ 10%** across majority of test cases
2. ✅ **Statistical significance p < 0.05** on paired t-test
3. ✅ **Autocorrelation reduction ≥ 15%** (relaxed from 20%)
4. ✅ **Reproducible** across 3 independent simulation runs
5. ✅ **Computational overhead < 2x** vs single LFSR

### Stretch Goals
If achieved, significantly strengthens publication:

1. 🎯 Mean error reduction ≥ 25%
2. 🎯 Golden ratio (φ = 1.618) demonstrably optimal
3. 🎯 Hardware validation matches simulation within 5%
4. 🎯 Power consumption increase < 10%
5. 🎯 Formal Lean 4 proof of error bounds

---

## Falsification Criteria

**Abandon hypothesis if:**

1. ❌ Mean error reduction < 5% across all parameter combinations
2. ❌ No statistical significance (p > 0.1) in any test
3. ❌ High variance makes results unreproducible
4. ❌ Computational overhead > 3x vs single LFSR
5. ❌ Hardware implementation shows opposite effect (worse accuracy)

**Note:** Negative results are still publishable! Title becomes: "Limits of Quasiperiodic Mixing for Stochastic Computing: An Empirical Study"

---

## Timeline & Resources

### Week 1: Simulation
- **Time:** 20-30 hours
- **Resources:** Python, NumPy, SciPy, Matplotlib
- **Cost:** $0
- **Deliverable:** Complete statistical analysis

### Week 2-3: FPGA Implementation
- **Time:** 30-40 hours
- **Resources:** Tang Nano 9K ($15), Gowin EDA (free), oscilloscope (optional)
- **Cost:** $15-50
- **Deliverable:** Working Verilog implementation

### Week 4: CMOS Validation
- **Time:** 20 hours
- **Resources:** 4000-series ICs ($13), breadboard ($10), multimeter ($20)
- **Cost:** $43
- **Deliverable:** Physical hardware validation

### Week 5: Analysis & Write-up
- **Time:** 15-20 hours
- **Resources:** LaTeX, citation manager
- **Cost:** $0
- **Deliverable:** Research paper draft

**Total Investment:** ~100 hours, ~$70

---

## Publications Strategy

### If Positive Results (≥10% improvement)
**Target venues:**
- IEEE TVLSI (Transactions on Very Large Scale Integration)
- ACM JETC (Journal on Emerging Technologies in Computing)
- FPGA 2026 conference
- Title: *"Quasiperiodic Bitstream Generation for Enhanced Stochastic Computing: A Formally Verified Approach"*

### If Modest Results (5-10% improvement)
**Target venues:**
- ISVLSI (International Symposium on VLSI Design)
- Workshop papers at DAC, DATE, FPL
- Title: *"Dual-LFSR Decorrelation in Stochastic Computing: Theoretical Foundations and Empirical Evaluation"*

### If Negative Results (<5% improvement)
**Target venues:**
- ReScience journal (reproduction studies)
- Workshop on Negative Results in Hardware
- Title: *"Empirical Limits of Quasiperiodic Mixing for LFSR-Based Stochastic Computing"*

**Key message:** Well-executed negative results are valuable to the community!

---

## Intellectual Honesty Checklist

Before claiming results, verify:

- [ ] Statistical tests appropriate and correctly applied
- [ ] P-hacking avoided (no selective reporting)
- [ ] Effect sizes reported, not just p-values
- [ ] Confidence intervals included
- [ ] Negative results disclosed if found
- [ ] Limitations section honest and complete
- [ ] No overstating "DTQC" connection (mathematical inspiration only)
- [ ] Hardware validation confirms simulation
- [ ] Independent reproduction attempted
- [ ] Data and code publicly available

---

## Lean 4 Formal Verification Component

Regardless of empirical results, formalize in Lean:

```lean
-- Theorem: Dual LFSR autocorrelation bound
theorem dual_lfsr_autocorrelation_bound
  (lfsr1 lfsr2 : LFSR)
  (h_incommensurate : Irrational (lfsr1.period / lfsr2.period))
  (mixing : ℝ → ℝ → ℝ) :
  ∃ (bound : ℝ), bound < single_lfsr_autocorr ∧
    quasiperiodic_autocorr lfsr1 lfsr2 mixing ≤ bound
```

This provides theoretical foundation even if empirical gains are modest.

---

## Risk Mitigation

### Technical Risks
| Risk | Probability | Impact | Mitigation |
|------|-------------|---------|------------|
| No improvement found | 30% | High | Publish negative results, still valuable |
| FPGA synthesis fails | 15% | Medium | Extensive simulation first, backup designs |
| Timing closure issues | 20% | Low | Reduce clock frequency if needed |
| Hardware-simulation mismatch | 25% | Medium | Careful validation at each step |

### Publication Risks
| Risk | Probability | Impact | Mitigation |
|------|-------------|---------|------------|
| Overselling DTQC connection | 40% | High | Clear language: "inspired by", not "implements" |
| Results not reproducible | 20% | High | Public code/data, detailed methodology |
| Scooped by others | 10% | Medium | Fast execution, preprint on arXiv |
| Reviewer skepticism | 50% | Medium | Strong statistics, honest limitations section |

---

## Go/No-Go Decision Points

### After Week 1 (Simulation):
**GO if:** Error reduction ≥ 8% with p < 0.1  
**NO-GO if:** Error reduction < 3% or p > 0.2  
**PIVOT if:** 3-8% improvement → investigate parameter optimization

### After Week 2 (FPGA):
**GO if:** Hardware matches simulation ± 10%  
**NO-GO if:** Hardware shows opposite effect  
**PIVOT if:** Large mismatch → debug and re-simulate

### After Week 3 (Full validation):
**PUBLISH if:** All success criteria met  
**PREPRINT if:** Interesting but incomplete results  
**ARCHIVE if:** Fundamentally flawed approach discovered

---

## Conclusion

This hypothesis is:
- ✅ **Testable** with clear metrics and statistical criteria
- ✅ **Falsifiable** with explicit go/no-go thresholds  
- ✅ **Achievable** with modest time and budget
- ✅ **Valuable** whether results are positive or negative
- ✅ **Honest** about mathematical inspiration vs. physical implementation
- ✅ **Rigorous** with formal verification and hardware validation

**Recommendation:** Proceed with Week 1 simulation. Decision point after statistical analysis.

**Worst case:** Learn that quasiperiodic mixing doesn't help much → still publishable, advances knowledge  
**Best case:** 25% error reduction → significant contribution to stochastic computing literature

Either way, it's good science.