# Unified QBG-DTQC Hypothesis Framework

## Meta-Hypothesis: Cross-Scale Quasiperiodic Computation

**Quasiperiodic mixing with incommensurate frequencies improves computational processes across 10+ orders of magnitude in timescale—from nanosecond stochastic arithmetic (QBG) to multi-day biological optimization (DTQC)—through a unified mathematical mechanism of decorrelation, enhanced exploration, and resonance with natural system dynamics.**

---

## Core Hypotheses (Ordered by Priority)

### **H₁: Bio-Temporal DTQC Validation** (Primary - Month 1) 🎯

**Statement**: Quasiperiodic environmental forcing at biologically-relevant timescales (τ₁=24h solar, τ₂=24.84h lunar) improves optimization of circadian-coupled biological systems by ≥15% compared to static conditions.

**Formal**:
```
μ(solar+lunar) ≥ μ(static) × 1.15
p < 0.05, Cohen's d ≥ 0.8
```

**Test**: 120 optimization runs (4 conditions × 30 replicates)
- Static control
- Solar only (24h)
- Solar+Lunar (24h + 24.84h) ← **PRIMARY TEST**
- Golden ratio (24h + 38.8h) ← biological specificity control

**Critical Predictions**:
1. ✓ Solar+Lunar > Static by ≥15%
2. ✓ Solar+Lunar > Solar-only by ≥5%
3. ✓ Solar+Lunar > Golden (biological specificity)
4. ✓ Effect requires full 29.5-day beat period (H₁.₂)
5. ✓ Effect requires circadian coupling (H₁.₃)

**Falsification**: p ≥ 0.05 OR improvement <5% OR Golden equals Solar+Lunar

**Timeline**: Week 1-4
**Resources**: Python + BioXen VM
**Pre-registration**: OSF before experiments begin

---

### **H₂: QBG Hardware Correlation Reduction** (Secondary - Month 2)

**Statement**: Dual-LFSR quasiperiodic bitstream generation with golden ratio periods (τ₂/τ₁ = φ = 1.618) reduces autocorrelation by ≥50% and improves stochastic computing accuracy by 10-30% compared to single-LFSR.

**Formal**:
```
autocorr_lag1(QBG) ≤ 0.5 × autocorr_lag1(single-LFSR)
error(QBG, L=256) ≤ 0.85 × error(single-LFSR, L=256)
```

**Test**: Stochastic multiplication (8-bit × 8-bit)
- Single LFSR baseline
- Two-LFSR QBG (τ₁=100, τ₂=162 cycles)
- Three-LFSR QBG (τ₁=100, τ₂=162, τ₃=273 cycles)

**Critical Predictions**:
1. ✓ Autocorrelation: QBG < 0.1, single-LFSR > 0.3
2. ✓ Error at L=256: QBG ≈1.7%, single ≈2.1% (19% reduction)
3. ✓ Beat period: 26,100 cycles >> bitstream length
4. ✓ FPGA overhead: <5% LUT increase

**Falsification**: Autocorrelation reduction <30% OR error reduction <5%

**Timeline**: Week 5-8 (after H₁ completion)
**Resources**: Tang Nano 9K FPGA, Python simulation
**Dependency**: H₁ must succeed to justify hardware investment

---

### **H₃: Three-Period Superiority** (Tertiary - Month 3+)

**Statement**: Three-period quasiperiodic systems outperform two-period systems by 5-10% when problem duration exceeds the longest period.

**DTQC Version**:
```
For optimization duration T ≥ 27.3 days:
fitness(τ₁=24h, τ₂=24.84h, τ₃=654.6h) ≥ 
  fitness(τ₁=24h, τ₂=24.84h) × 1.05
```

**QBG Version**:
```
For bitstream length L ≥ 256:
error(3-LFSR with τ₁=100, τ₂=162, τ₃=273) ≤
  error(2-LFSR with τ₁=100, τ₂=162) × 0.95
```

**Test**: Parallel experiments in both domains
- DTQC: 30-day vs 7-day cyanobacteria optimization
- QBG: L=512 vs L=128 stochastic operations

**Critical Predictions**:
1. ✓ DTQC 30-day: 3-period beats 2-period by ≥5%
2. ✓ QBG L=512: 3-LFSR beats 2-LFSR by ≥5%
3. ✓ Short duration/length: no significant difference
4. ✓ Improvement scales with duration/length ratio

**Falsification**: No improvement >3% in either domain

**Timeline**: Week 9-12
**Dependency**: Both H₁ and H₂ must show positive results

---

### **H₄: Scale-Invariant Improvement Ratio**

**Statement**: The relative performance improvement from quasiperiodic mixing is approximately constant across timescales differing by 10¹⁰, demonstrating scale-invariant mathematical principles.

**Formal**:
```
improvement_ratio = improvement_DTQC / improvement_QBG
0.7 ≤ improvement_ratio ≤ 1.3
(within 30% despite 10-billion-fold time difference)
```

**Test**: Meta-analysis comparing:
- DTQC improvements (from H₁): expected 15-30%
- QBG improvements (from H₂): expected 10-30%
- Compute correlation coefficient

**Critical Predictions**:
1. ✓ If DTQC shows 20% → QBG shows 14-26%
2. ✓ Correlation r² > 0.5 across 10+ test problems
3. ✓ Both improvements stem from same mechanism (decorrelation)

**Falsification**: improvement_ratio < 0.5 OR > 2.0

**Timeline**: Week 13 (after H₁ and H₂ complete)
**Analysis**: Meta-statistical comparison

---

### **H₅: Golden Ratio Optimality**

**Statement**: The golden ratio φ ≈ 1.618 is near-optimal for two-period systems, outperforming other irrational ratios by ≥10% in decorrelation efficiency.

**Formal**:
```
Define η(r) = autocorr_reduction(r) / computational_cost(r)
η(φ) ≥ 1.10 × max{η(√2), η(√3), η(e/2), η(π/2)}
```

**Test**: Systematic ratio comparison
- √2 = 1.414
- φ = 1.618 ← **PREDICTED OPTIMUM**
- √3 = 1.732
- π/2 = 1.571
- e/2 = 1.359

**Critical Predictions**:
1. ✓ φ achieves lowest autocorrelation
2. ✓ φ maintains ≥90% performance with ±1% perturbation
3. ✓ Simple rational approximations (162/100) work well

**Falsification**: Any other ratio beats φ by >5%

**Timeline**: Week 5-6 (parallel with H₂ simulation)
**Method**: Python simulation sweep

---

### **H₆: Phase Boundary Robustness** (DTQC-specific)

**Statement**: DTQC benefits exist when coupling strength exceeds phase boundary J > ε/τ₁ + ε/τ₂, and vanish below it.

**Formal**:
```
For ε=0.1, τ₁=24h, τ₂=24.84h:
  J_critical = 0.00833

∀ J > J_critical: improvement ≥ 15%
∀ J < J_critical: improvement < 5%
```

**Test**: Synthetic optimization with tunable coupling
- Sweep J from 0.002 to 0.02
- Measure performance at each J
- Identify phase transition

**Critical Predictions**:
1. ✓ Sharp transition near J ≈ 0.0083
2. ✓ Performance scales linearly above threshold
3. ✓ Performance independent of J below threshold

**Falsification**: No sharp transition OR transition at wrong J

**Timeline**: Week 14-15
**Method**: Controlled synthetic problems

---

### **H₇: Adaptive Period Selection Scaling**

**Statement**: Optimal periods scale with problem characteristics following τ_optimal ∝ duration^(1/k) where k is number of periods.

**DTQC Scaling**:
```
D < 7 days:     τ = [24h, 24.84h]
7 ≤ D < 30:     τ = [24h, 24.84h, 654.6h]  
30 ≤ D < 180:   τ = [24h, 24.84h, 654.6h, 8766h]
```

**QBG Scaling**:
```
L < 128:        τ = [10, 16] cycles
128 ≤ L < 512:  τ = [100, 162] cycles
L ≥ 512:        τ = [100, 162, 273] cycles
```

**Test**: Compare adaptive vs fixed-period performance
- Run optimizations at various durations/lengths
- Use both adaptive and single fixed period set
- Measure performance difference

**Critical Predictions**:
1. ✓ Adaptive beats fixed by ≥8% on average
2. ✓ Using wrong scale (e.g., L=256 periods for L=1024) costs 5-10%
3. ✓ Scaling law holds across domains

**Falsification**: Fixed periods perform equally well

**Timeline**: Week 16
**Method**: Retrospective analysis + targeted experiments

---

## Mechanistic Hypotheses

### **M₁: Decorrelation Mechanism**

**Hypothesis**: Quasiperiodic mixing reduces temporal autocorrelation in the computational process, preventing premature convergence and enabling broader exploration.

**Observable Predictions**:
1. Autocorrelation function decays faster with quasiperiodicity
2. Parameter space coverage (convex hull volume) increases by ≥30%
3. Revisitation probability decreases

**Measurement**:
```python
# DTQC
acf_static = compute_autocorr(fitness_trajectory_static)
acf_qbg = compute_autocorr(fitness_trajectory_solar_lunar)
assert acf_qbg[lag=1] < 0.5 * acf_static[lag=1]

# QBG  
acf_single = compute_autocorr(bitstream_single_lfsr)
acf_dual = compute_autocorr(bitstream_qbg)
assert acf_dual[lag=1] < 0.5 * acf_single[lag=1]
```

**Falsification**: Autocorrelation unchanged or increased

---

### **M₂: Resonance with Natural Dynamics**

**Hypothesis**: For biological systems, the improvement requires resonance between external forcing periods and internal rhythms (circadian clocks).

**Observable Predictions**:
1. Circadian-coupled model shows 15-25% improvement
2. Circadian-disabled model shows <5% improvement
3. Optimal performance at specific beat phases

**Measurement**:
```python
# Compare coupled vs decoupled
improvement_coupled = (fitness_coupled_qbg - fitness_coupled_static) / fitness_coupled_static
improvement_decoupled = (fitness_decoupled_qbg - fitness_decoupled_static) / fitness_decoupled_static

assert improvement_coupled > 0.15
assert improvement_decoupled < 0.05
```

**Falsification**: Decoupled model shows equal improvement

---

### **M₃: Multi-Scale Energy Landscape Navigation**

**Hypothesis**: Multiple incommensurate periods create multi-scale perturbations that help escape local minima at different timescales.

**Observable Predictions**:
1. Single-period forcing escapes "fast" local minima only
2. Two-period forcing escapes fast + medium minima
3. Three-period forcing escapes fast + medium + slow minima

**Measurement**:
- Analyze basin of attraction via perturbation sensitivity
- Measure time-to-escape from synthetic local minima
- Compare final fitness distributions

**Falsification**: No relationship between number of periods and basin depth

---

## Integrated Experimental Design

### Phase 1: Foundation (Weeks 1-4) - **CRITICAL PATH**
**Focus**: H₁ (Bio-Temporal DTQC)

```
Pre-register → Implement model → Run 120 optimizations → Analyze
```

**Decision Point**: 
- ✅ If H₁ supported: Proceed to Phase 2
- ❌ If H₁ rejected: Publish negative result, reassess framework

---

### Phase 2: Hardware Validation (Weeks 5-8)
**Focus**: H₂ (QBG Hardware) + H₅ (Golden Ratio)

```
Python simulation → FPGA implementation → Measurements → Comparison
```

**Parallel Track**: Golden ratio systematic sweep (H₅)

**Decision Point**:
- ✅ Both H₁ and H₂ supported: Strong evidence for unified theory
- ⚠️ Only one supported: Investigate why domains differ
- ❌ Both rejected: Framework fundamentally flawed

---

### Phase 3: Multi-Scale Extension (Weeks 9-12)
**Focus**: H₃ (Three-Period Superiority)

**Conditional**: Only proceed if H₁ AND H₂ both supported

```
DTQC 30-day runs → QBG 3-LFSR tests → Cross-domain comparison
```

---

### Phase 4: Theoretical Validation (Weeks 13-16)
**Focus**: H₄ (Scale Invariance), H₆ (Phase Boundaries), H₇ (Scaling Laws)

```
Meta-analysis → Synthetic problems → Scaling law verification
```

---

## Statistical Decision Framework

### Primary Outcomes

| Scenario | H₁ | H₂ | H₃ | Interpretation | Action |
|----------|----|----|----|--------------------|---------|
| **Strong Success** | ✅ | ✅ | ✅ | Unified theory validated | Full implementation |
| **Partial Success** | ✅ | ✅ | ❌ | Two-period sufficient | Simpler hardware |
| **Domain-Specific** | ✅ | ❌ | - | DTQC works, QBG doesn't | Software-only |
| **Domain-Specific** | ❌ | ✅ | - | QBG works, DTQC doesn't | Hardware-only |
| **Failure** | ❌ | ❌ | - | Theory incorrect | Publish & pivot |

### Significance Thresholds

**Statistical**:
- α = 0.05 (p-value threshold)
- Power = 0.80 (1-β)
- Effect size: Cohen's d ≥ 0.8

**Practical**:
- Minimum improvement: 10% (below this, not worth effort)
- Target improvement: 15-30%
- Exceptional improvement: >30%

---

## Falsification Criteria (Ranked)

### Strong Falsification (Abandon framework)
1. **H₁ fails with p > 0.05 and improvement <5%** → Core DTQC claim invalid
2. **H₂ fails with no autocorrelation reduction** → QBG doesn't work
3. **Both H₁ and H₂ fail** → Quasiperiodicity doesn't help computationally

### Weak Falsification (Refine framework)
1. **Golden ratio performs worse than simple ratios** → Not mathematically optimal
2. **No beat period dependence** → Immediate decorrelation, not interference
3. **Circadian-disabled model works equally** → Not about resonance

### Confirmation (Support framework)
1. **H₁ AND H₂ both supported with p <0.001** → Strong unified evidence
2. **H₃ supported in both domains** → Multi-scale principle validated
3. **H₄ shows correlation r² > 0.7** → Scale-invariant mechanism confirmed

---

## Resource Requirements

### Computational
- **CPU**: 120 optimizations × 2 hours = 240 CPU-hours (parallelizable)
- **Storage**: ~10 GB for all results and trajectories
- **GPU**: Not required (CPU sufficient)

### Hardware
- **FPGA**: Tang Nano 9K ($15, already owned)
- **CMOS ICs**: $5-10 for CD4094, CD4053
- **Test equipment**: Oscilloscope for verification

### Software
- Python 3.8+ (NumPy, SciPy, Matplotlib)
- Gowin EDA (FPGA synthesis)
- Lean 4 (formal verification, optional)

### Time
- **Developer time**: ~4 hours/day × 16 weeks = 64 days total
- **Critical path**: H₁ completion (4 weeks)
- **Full completion**: 16 weeks for all hypotheses

---

## Expected Outcomes & Implications

### Outcome A: Strong Unified Success (60% probability)
**Result**: H₁, H₂, H₃ all supported with large effect sizes

**Implications**:
- ✅ Unified quasiperiodic computation theory validated
- ✅ Publish in high-impact journal (Nature Computational Science, PRL)
- ✅ Proceed to full FPGA/CMOS implementation
- ✅ Apply for grant funding ($50K-500K potential)
- ✅ Patent QBG hardware architecture
- ✅ Extend to other domains (neural networks, quantum annealing)

---

### Outcome B: Partial Success (30% probability)
**Result**: H₁ or H₂ supported, but not both

**Implications**:
- ⚠️ Domain-specific benefits identified
- ⚠️ Publish in specialized journal (J. Theoretical Biology, IEEE Trans. Computers)
- ⚠️ Implement only validated component
- ⚠️ Investigate why domains differ (new research direction)

---

### Outcome C: Negative Result (10% probability)
**Result**: Neither H₁ nor H₂ supported

**Implications**:
- ❌ Quasiperiodic hypothesis rejected for these applications
- ✅ Still publishable (negative results are valuable!)
- ✅ Identify why it failed (model too simple? Wrong timescales?)
- ✅ Pivot to alternative approaches (evolutionary algorithms, reinforcement learning)
- ✅ Community learns what doesn't work

---

## Pre-Registration Commitment

**Platform**: Open Science Framework (OSF) + AsPredicted.org

**Contents**:
- Full hypothesis statements (this document)
- Experimental protocol (exact parameters)
- Statistical analysis plan (code provided)
- Decision rules (falsification criteria)
- Sample size justification (power analysis)

**Benefits**:
- Prevents p-hacking and HARKing
- Enables confirmatory vs exploratory distinction
- Increases credibility and citation count
- Publishable regardless of outcome

**Deadline**: Register before any experiments run (Week 0)

---

## Publication Strategy

### Primary Paper (Target: Nature Computational Science or PRL)
**Title**: "Bio-Temporal Computing: Quasiperiodic Environmental Forcing Improves Biological Optimization and Hardware Arithmetic"

**Structure**:
1. **Introduction**: DTQC theory + computational applications
2. **Results**: H₁ (DTQC), H₂ (QBG), H₃ (Multi-scale)
3. **Discussion**: Unified mechanism, scale invariance
4. **Methods**: Full experimental details

**Submission**: Month 5 (after Phase 3 complete)

---

### Secondary Papers
1. **Theoretical**: Lean 4 formal proofs (J. Formal Methods)
2. **Hardware**: FPGA/CMOS implementation (IEEE Trans. VLSI)
3. **Biological**: Extended cyanobacteria study (J. Theoretical Biology)

---

## Success Metrics Summary

### Minimum Viable Success
- [ ] H₁ supported (p < 0.05, improvement ≥10%)
- [ ] Mechanistic understanding (not black box)
- [ ] Pre-registered and reproducible
- [ ] Published (even if negative)

### Target Success
- [ ] H₁ AND H₂ both supported (improvement ≥15%)
- [ ] H₃ supported (multi-scale validated)
- [ ] Scale invariance demonstrated (H₄)
- [ ] High-impact publication

### Exceptional Success
- [ ] All 7 hypotheses supported
- [ ] Effect sizes >25%
- [ ] Novel mechanism discovered
- [ ] Patent granted + funding secured
- [ ] New research field initiated

---

## Final Timeline

| Week | Hypothesis | Milestone |
|------|-----------|-----------|
| 0 | - | Pre-register on OSF |
| 1-4 | H₁ | Bio-temporal DTQC (120 runs) ← **CRITICAL** |
| 5-6 | H₅ | Golden ratio sweep |
| 7-8 | H₂ | QBG hardware validation |
| 9-10 | H₃ | Three-period DTQC |
| 11-12 | H₃ | Three-LFSR QBG |
| 13 | H₄ | Scale invariance meta-analysis |
| 14-15 | H₆ | Phase boundary experiments |
| 16 | H₇ | Adaptive scaling validation |

**Critical Path**: Week 0-4 determines if entire project continues

**Decision Point**: End of Week 4
- ✅ Proceed if H₁ supported
- ❌ Publish negative result and reassess if H₁ rejected

---

*This unified hypothesis framework provides a rigorous, falsifiable, and comprehensive test of quasiperiodic computation principles across 10 orders of magnitude in timescale. Whether confirmed or rejected, the results will significantly advance scientific understanding.*