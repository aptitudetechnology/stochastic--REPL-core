# Revised Unified QBG-DTQC Hypothesis Framework

## Meta-Hypothesis: Analogous Cross-Scale Quasiperiodic Effects

**Quasiperiodic mixing with incommensurate frequencies may improve computational processes across vastly different timescales—from nanosecond stochastic arithmetic (QBG) to multi-day biological optimization (DTQC)—through mathematically analogous (though potentially mechanistically distinct) decorrelation mechanisms.**

**Key Revision**: This framework tests whether similar mathematical structures produce similar computational benefits across scales, NOT whether they represent the same physical mechanism. The domains may share mathematical properties while differing fundamentally in their underlying processes.

---

## Core Hypotheses (Ordered by Priority)

### **H₁: Bio-Temporal DTQC Validation** (Primary - Month 1) 🎯

**Statement**: Quasiperiodic environmental forcing at biologically-relevant timescales (τ₁=24h solar, τ₂=24.84h lunar) improves optimization of circadian-coupled biological systems by ≥15% compared to static conditions, and this improvement specifically requires the 29.5-day beat period.

**Formal**:
```
μ(solar+lunar) ≥ μ(static) × 1.15
p < 0.05, Cohen's d ≥ 0.8
n = 40 per condition (increased from 30)
```

**Test**: 280 optimization runs (7 conditions × 40 replicates)

**Conditions** (REVISED - added critical controls):
1. **Static control** (no forcing)
2. **Solar only** (24h single period)
3. **Lunar only** (24.84h single period) ← NEW
4. **Solar+Lunar aligned** (24h + 24.84h, correct beat) ← PRIMARY TEST
5. **Solar+Lunar misaligned** (24h + 25.84h, disrupted beat) ← NEW
6. **Golden ratio** (24h + 38.8h) ← biological specificity control
7. **Random dual period** (24h + 27.3h) ← NEW

**Critical Predictions**:
1. ✓ Solar+Lunar_aligned > Static by ≥15%
2. ✓ Solar+Lunar_aligned > Solar-only by ≥8%
3. ✓ Solar+Lunar_aligned > Lunar-only by ≥8%
4. ✓ Solar+Lunar_aligned > Solar+Lunar_misaligned by ≥5% (beat period matters)
5. ✓ Solar+Lunar_aligned > Golden ratio by ≥5% (biological specificity)
6. ✓ Solar+Lunar_aligned > Random dual by ≥5% (not just any two periods)
7. ✓ Single periods (Solar, Lunar) show 5-10% improvement vs Static (resonance exists)
8. ✓ Effect requires circadian coupling (H₁.₂)

**Falsification Criteria**:
- **Strong rejection**: p ≥ 0.05 OR improvement <5% for Solar+Lunar_aligned
- **Mechanism rejection**: No difference between aligned vs misaligned (beat period doesn't matter)
- **Non-specific**: Golden ratio or Random dual equal to Solar+Lunar (not biologically specific)

**Timeline**: Week 1-5 (extended from 4 weeks due to more conditions)
**Resources**: Python + BioXen VM
**Pre-registration**: OSF before experiments begin

---

### **H₂: QBG Hardware Correlation Reduction** (Secondary - Month 2)

**Statement**: Dual-LFSR quasiperiodic bitstream generation with golden ratio periods (τ₂/τ₁ = φ = 1.618) reduces autocorrelation by ≥50% and improves stochastic computing accuracy by 10-30% compared to single-LFSR, as measured in both simulation AND actual FPGA hardware.

**Formal**:
```
autocorr_lag1(QBG) ≤ 0.5 × autocorr_lag1(single-LFSR)
error(QBG, L=256) ≤ 0.85 × error(single-LFSR, L=256)
Both conditions must hold in simulation AND hardware
```

**Test**: Stochastic multiplication (8-bit × 8-bit)

**Phases**:
1. **Simulation** (Week 6): Establish baseline with ideal conditions
2. **FPGA Implementation** (Week 7-8): Validate under real-world conditions

**Conditions**:
1. Single LFSR baseline
2. Two-LFSR QBG (τ₁=100, τ₂=162 cycles)
3. Three-LFSR QBG (τ₁=100, τ₂=162, τ₃=273 cycles)

**Critical Predictions**:
1. ✓ **Simulation**: Autocorrelation QBG < 0.1, single-LFSR > 0.3
2. ✓ **Simulation**: Error at L=256: QBG ≈1.7%, single ≈2.1% (19% reduction)
3. ✓ **Hardware**: Autocorrelation reduction ≥40% (allowing 10% degradation vs simulation)
4. ✓ **Hardware**: Error reduction ≥15% (allowing some degradation)
5. ✓ **Hardware**: FPGA overhead <5% LUT increase
6. ✓ **Hardware**: No significant power consumption increase (<10%)

**Falsification Criteria**:
- **Strong rejection**: Autocorrelation reduction <30% in simulation
- **Hardware failure**: Hardware results show <20% of simulation benefit
- **Cost failure**: FPGA overhead >10% OR power increase >20%

**Timeline**: Week 6-9 (extended for hardware)
**Resources**: Tang Nano 9K FPGA, oscilloscope, Python simulation
**Dependency**: H₁ results inform whether to proceed with hardware implementation

---

### **H₃: Three-Period Superiority** (Exploratory - Month 3+)

**Status**: EXPLORATORY (not confirmatory)

**Statement**: Three-period quasiperiodic systems MAY outperform two-period systems by 5-10% when problem duration exceeds the longest period, but this is speculative and will only be pursued if H₁ and H₂ show large effect sizes (>20%).

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

**Decision Rule**: 
- ✅ Proceed if H₁ shows >20% AND H₂ shows >20% improvement
- ❌ Skip if either shows <20% (not worth added complexity)

**Test**: Parallel experiments in both domains
- DTQC: 30-day vs 7-day cyanobacteria optimization (n=20 per condition)
- QBG: L=512 vs L=128 stochastic operations (n=100 trials)

**Exploratory Predictions**:
1. ? DTQC 30-day: 3-period MAY beat 2-period by ≥5%
2. ? QBG L=512: 3-LFSR MAY beat 2-LFSR by ≥5%
3. ? Short duration/length: expect no significant difference
4. ? Improvement MAY scale with duration/length ratio

**Analysis Approach**: Report effect sizes with confidence intervals, do NOT claim confirmation even if p<0.05 (exploratory = hypothesis generating)

**Timeline**: Week 10-12 (CONDITIONAL on H₁ and H₂ results)

---

### **H₄: Mathematical Analogy Test** (REVISED)

**Statement**: If quasiperiodic mixing benefits both domains through analogous mathematical mechanisms (decorrelation), then the relative improvement ratios should correlate across different problem types within each domain, even if absolute magnitudes differ between domains.

**Formal** (REVISED - tighter criteria):
```
Within-domain correlation test:
- Test 5+ different problems in DTQC domain
- Test 5+ different problems in QBG domain
- Compute improvement ratio for each problem
- Within-domain correlation: r² > 0.6

Cross-domain similarity test:
ONLY if both domains show consistent improvements:
improvement_ratio = median(improvement_DTQC) / median(improvement_QBG)
0.8 ≤ improvement_ratio ≤ 1.25 (±20%, tightened from ±30%)
```

**Interpretation Framework**:
- **Strong analogy** (r²>0.6 within domains, ratio ∈ [0.8,1.25]): Mathematical principles generalize
- **Weak analogy** (r²>0.6 within domains, ratio outside [0.8,1.25]): Similar math, different magnitudes
- **Domain-specific** (low r² within domains): Each domain has unique mechanisms
- **No effect** (no improvements): Quasiperiodicity doesn't help computation

**Test Problems**:

DTQC (5 problems):
1. Cyanobacteria growth optimization (primary)
2. Synthetic circadian oscillator
3. Yeast cell cycle model
4. Plant photoperiod response
5. Mammalian sleep-wake cycle

QBG (5 operations):
1. Multiplication (8-bit × 8-bit)
2. Squaring (8-bit²)
3. Division (8-bit ÷ 8-bit)
4. Square root approximation
5. Sigmoid function approximation

**Critical Predictions**:
1. ✓ Within DTQC: If cyanobacteria improves 20%, yeast should improve 15-25%
2. ✓ Within QBG: If multiplication improves 18%, squaring should improve 13-23%
3. ? Cross-domain: Improvements MAY be similar magnitude (but not required)

**Falsification Criteria**:
- **Weak analogy**: r² < 0.4 within either domain
- **No analogy**: Both domains show r² < 0.3

**Timeline**: Week 13 (after H₁ and H₂ complete)
**Analysis**: Correlation analysis + meta-regression

---

### **H₅: Golden Ratio Near-Optimality**

**Statement**: For two-period systems with finite sequence lengths, the golden ratio φ ≈ 1.618 should show near-optimal decorrelation efficiency due to its properties as the most poorly approximable irrational number. However, this optimality may be sequence-length dependent.

**Theoretical Basis**: 
- φ has continued fraction [1;1,1,1,...] (slowest rational convergence)
- This maximizes "irrationality" for avoiding resonances
- For finite L, optimality may shift to nearby ratios

**Formal**:
```
Define η(r) = autocorr_reduction(r) / computational_cost(r)
η(φ) ≥ 0.95 × max{η(√2), η(√3), η(√5), η(e/2), η(π/2)}
(Near-optimal = within 5% of best)

Test sequence-length dependence:
- L=64: optimal_ratio = ?
- L=128: optimal_ratio = ?
- L=256: optimal_ratio = ?
- L=512: optimal_ratio = ?
```

**Test**: Systematic ratio comparison
- √2 = 1.414
- (√5+1)/2 = 1.618 (φ)
- φ = 1.618034... ← **PREDICTED NEAR-OPTIMUM**
- 162/100 = 1.620 (rational approximation)
- √3 = 1.732
- π/2 = 1.571
- e/2 = 1.359
- √5 = 2.236

**Critical Predictions**:
1. ✓ φ achieves ≥95% of best observed decorrelation
2. ✓ Simple rational approximations (162/100) perform within 2% of φ
3. ✓ φ maintains ≥90% performance with ±2% perturbation (robustness)
4. ? Optimal ratio MAY shift with sequence length

**Falsification Criteria**:
- **Strong rejection**: φ performs <90% of best ratio
- **Weak rejection**: φ performs 90-94% of best (near-optimal not achieved)
- **Length-dependence**: Different L values have different optimal ratios

**Timeline**: Week 6-7 (parallel with H₂ simulation)
**Method**: Python simulation sweep (5000 trials per ratio)

---

### **H₆: Phase Boundary Robustness** (DTQC-specific)

**Statement**: DTQC benefits require coupling strength exceeding a phase boundary J > ε/τ₁ + ε/τ₂. Below this threshold, forcing periods are too weakly coupled to the system dynamics to produce benefits.

**Theoretical Derivation**:
```
For environmental forcing ε·sin(2πt/τᵢ) coupled to system via parameter J:
- Forcing amplitude: ε
- Response timescale: 1/J
- For forcing to influence system on timescale τᵢ:
  J·τᵢ > ε (dimensionless)
  
For two-period system:
J > ε/τ₁ + ε/τ₂ (both periods must couple)

For ε=0.1, τ₁=24h, τ₂=24.84h:
J_critical = 0.1/24 + 0.1/24.84 = 0.00833 h⁻¹
```

**Formal**:
```
∀ J > 1.2×J_critical: improvement ≥ 15%
∀ J < 0.8×J_critical: improvement < 5%
Transition width: ±20% around J_critical
```

**Test**: Synthetic optimization with tunable coupling
- Sweep J from 0.002 to 0.02 (10 values)
- n=20 replicates per J value
- Measure fitness improvement

**Critical Predictions**:
1. ✓ Sharp transition near J ≈ 0.0083
2. ✓ Sigmoid-like response curve (not linear)
3. ✓ Performance plateaus above 2×J_critical
4. ✓ Below J_critical, performance ≈ static control

**Falsification Criteria**:
- **No boundary**: Linear response across all J values
- **Wrong J**: Transition occurs at J > 2×predicted OR J < 0.5×predicted
- **No threshold**: Gradual improvement with no clear transition

**Timeline**: Week 14-15
**Method**: Controlled synthetic problems with adjustable coupling

---

### **H₇: Adaptive Period Selection Scaling** (Exploratory)

**Status**: EXPLORATORY - post-hoc pattern analysis, not a priori prediction

**Statement**: Optimal periods MAY scale with problem characteristics following power law relationships, but this will be investigated retrospectively after H₁-H₆ complete.

**Proposed Scaling Laws** (to be tested, not assumed):

DTQC:
```
D < 7 days:     τ = [24h, 24.84h]
7 ≤ D < 30:     τ = [24h, 24.84h, 654.6h]  
30 ≤ D < 180:   τ = [24h, 24.84h, 654.6h, 8766h]
```

QBG:
```
L < 128:        τ = [10, 16] cycles
128 ≤ L < 512:  τ = [100, 162] cycles
L ≥ 512:        τ = [100, 162, 273] cycles
```

**Analysis Approach**: 
- Compile results from H₁-H₆
- Search for scaling relationships
- Generate hypotheses for future dedicated study
- DO NOT claim confirmation (this is hypothesis-generating)

**Timeline**: Week 16
**Method**: Retrospective data analysis

---

## Mechanistic Hypotheses

### **M₁: Decorrelation Mechanism** (Both Domains)

**Hypothesis**: Quasiperiodic mixing reduces temporal autocorrelation in the computational process, preventing premature convergence (DTQC) or systematic bias accumulation (QBG).

**Observable Predictions**:
1. Autocorrelation function decays faster with quasiperiodicity
2. DTQC: Parameter space coverage (convex hull volume) increases by ≥30%
3. QBG: Bitstream randomness (entropy rate) increases by ≥20%
4. Both: Revisitation probability decreases

**Measurement**:
```python
# DTQC
acf_static = autocorr(fitness_trajectory_static)
acf_qp = autocorr(fitness_trajectory_solar_lunar)
assert acf_qp[lag=1] < 0.5 * acf_static[lag=1]

# QBG  
acf_single = autocorr(bitstream_single_lfsr)
acf_dual = autocorr(bitstream_qbg)
assert acf_dual[lag=1] < 0.5 * acf_single[lag=1]
```

**Falsification**: Autocorrelation unchanged (ratio > 0.8) or increased

---

### **M₂: Resonance with Natural Dynamics** (DTQC-specific)

**Hypothesis**: For DTQC, the improvement requires resonance between external forcing periods and internal circadian rhythms. This is domain-specific and does NOT apply to QBG.

**Observable Predictions**:
1. Circadian-coupled model shows 15-25% improvement
2. Circadian-disabled model shows <5% improvement
3. Optimal performance at specific beat phases
4. Solar-only and Lunar-only individually show 5-10% improvement (single-period resonance)

**Measurement**:
```python
# Compare coupled vs decoupled
improvement_coupled = (fitness_coupled_qp - fitness_coupled_static) / fitness_coupled_static
improvement_decoupled = (fitness_decoupled_qp - fitness_decoupled_static) / fitness_decoupled_static

assert improvement_coupled > 0.15
assert improvement_decoupled < 0.05
```

**Falsification**: Decoupled model shows equal improvement (>15%)

**Domain Note**: This mechanism is SPECIFIC to biological systems with circadian clocks. QBG operates purely on mathematical decorrelation (M₁).

---

### **M₃: Multi-Scale Energy Landscape Navigation** (Exploratory)

**Hypothesis**: Multiple incommensurate periods MAY create multi-scale perturbations that help escape local minima at different timescales. This is speculative.

**Observable Predictions** (if H₃ pursued):
1. Single-period forcing escapes "fast" local minima only
2. Two-period forcing escapes fast + medium minima
3. Three-period forcing escapes fast + medium + slow minima

**Measurement**:
- Analyze basin of attraction via perturbation sensitivity
- Measure time-to-escape from synthetic local minima
- Compare final fitness distributions
- Spectral analysis of fitness trajectories

**Falsification**: No relationship between number of periods and escape from local minima

**Status**: Will only be tested if H₃ is pursued (conditional on H₁ and H₂ results)

---

## Integrated Experimental Design

### Phase 1: Foundation (Weeks 1-5) - **CRITICAL PATH**
**Focus**: H₁ (Bio-Temporal DTQC) with expanded controls

```
Week 0: Pre-register on OSF
Week 1: Implement model + debug
Week 2-4: Run 280 optimizations (7 conditions × 40 replicates)
Week 5: Statistical analysis + interpretation
```

**Decision Point** (End of Week 5): 
- ✅ **Proceed to Phase 2** if H₁ supported (p<0.05, improvement ≥10%)
- ⚠️ **Conditional proceed** if H₁ shows trend (0.05 < p < 0.10, improvement ≥8%) → increase n to 50
- ❌ **Publish negative result** if H₁ rejected (p≥0.10 OR improvement <5%)

---

### Phase 2: Hardware Validation (Weeks 6-9)
**Focus**: H₂ (QBG Hardware) + H₅ (Golden Ratio)

```
Week 6: Python simulation baseline + golden ratio sweep (H₅)
Week 7: FPGA implementation + synthesis
Week 8: Hardware measurements (autocorrelation, error, power)
Week 9: Simulation vs hardware comparison + analysis
```

**Parallel Track**: Golden ratio systematic sweep (H₅) runs during Week 6

**Decision Point** (End of Week 9):
- ✅ **Both H₁ and H₂ supported**: Strong evidence for mathematical analogy
- ⚠️ **Only H₁ supported**: DTQC-specific benefit (biological resonance)
- ⚠️ **Only H₂ supported**: QBG-specific benefit (hardware decorrelation)
- ❌ **Both rejected**: Framework incorrect, publish negative results

---

### Phase 3: Multi-Scale Extension (Weeks 10-12) - CONDITIONAL

**Focus**: H₃ (Three-Period Superiority) - EXPLORATORY

**Entry Criteria**: 
- H₁ shows improvement >20% (not just >15%)
- H₂ shows improvement >20% (not just >15%)
- Both have p < 0.01 (strong significance)

**Skip Criteria**:
- Either H₁ or H₂ shows improvement <20%
- Either has 0.01 < p < 0.05 (marginal significance)
- Time/resource constraints

```
Week 10: DTQC 30-day setup (if pursuing)
Week 11: QBG 3-LFSR implementation
Week 12: Cross-domain comparison
```

---

### Phase 4: Theoretical Validation (Weeks 13-16)

**Focus**: H₄ (Mathematical Analogy), H₆ (Phase Boundaries), H₇ (Scaling Laws)

```
Week 13: H₄ meta-analysis across multiple problems
Week 14-15: H₆ phase boundary experiments
Week 16: H₇ retrospective scaling analysis + documentation
```

---

## Statistical Decision Framework (Revised)

### Primary Outcomes

| Scenario | H₁ | H₂ | Interpretation | Action |
|----------|----|----|----------------|---------|
| **Strong Success** | ✅ (>20%) | ✅ (>20%) | Mathematical analogy validated | Pursue H₃, H₄ |
| **Moderate Success** | ✅ (15-20%) | ✅ (15-20%) | Both work, modest effects | Skip H₃, do H₄ |
| **DTQC-specific** | ✅ (>15%) | ❌ (<10%) | Biological resonance, not general | Focus on DTQC |
| **QBG-specific** | ❌ (<10%) | ✅ (>15%) | Hardware decorrelation, not biological | Focus on QBG |
| **Null Result** | ❌ (<5%) | ❌ (<5%) | Quasiperiodicity doesn't help | Publish negative |
| **Trend** | ~ (p=0.06) | ~ (p=0.08) | Increase sample size | Extend to n=50 |
| **Opposite** | ❌ (negative) | ✅ (>15%) | DTQC harmful, investigate | Check for bugs |

### Significance Thresholds (Revised)

**Statistical**:
- α = 0.05 (two-tailed)
- Power = 0.80 (1-β)
- Effect size: Cohen's d ≥ 0.8
- **Sample size**: n=40 per condition (increased from 30)

**Practical Significance**:
- Minimum meaningful improvement: 10%
- Target improvement: 15-25%
- Exceptional improvement: >25% (check for implementation errors!)

**Multiple Comparisons**:
- H₁ has 7 conditions → use Tukey HSD or Holm-Bonferroni
- Report both corrected and uncorrected p-values
- Primary comparison: Solar+Lunar_aligned vs Static (most important)

---

## Power Analysis (Added)

### H₁ Power Calculation

For detecting d=0.8 with α=0.05, power=0.80:
- Two-group t-test: n≈26 per group
- Seven-group ANOVA with post-hoc: n≈35 per group
- **Chosen**: n=40 per group (provides power=0.85)

Total runs: 7 conditions × 40 replicates = **280 runs**

### H₂ Power Calculation

For detecting 20% error reduction:
- Baseline error: ~2.1%
- QBG error: ~1.68% (20% reduction)
- Standard deviation: ~0.3%
- Effect size: d = (2.1-1.68)/0.3 = 1.4 (large)
- Required n: ~15 per condition
- **Chosen**: n=100 trials (provides power > 0.99)

---

## Falsification Criteria (Revised & Ranked)

### Strong Falsification (Abandon domain)

1. **H₁ fails**: p > 0.10 AND improvement <5% → DTQC doesn't work
2. **H₂ fails**: Autocorrelation reduction <20% in hardware → QBG doesn't work
3. **Both H₁ and H₂ fail** → Quasiperiodicity doesn't help computation

### Mechanism Falsification (Revise theory)

1. **No beat period dependence** (H₁): Solar+Lunar_aligned = Solar+Lunar_misaligned → Not about interference
2. **No circadian dependence** (M₂): Decoupled model = Coupled model → Not about resonance
3. **Golden ratio not near-optimal** (H₅): φ < 90% of best → Not mathematically special

### Weak Falsification (Refine details)

1. **Domain-specific**: Only H₁ OR H₂ works → Mechanisms differ by domain
2. **Three-period doesn't help** (H₃): No improvement → Two periods sufficient
3. **No phase boundary** (H₆): Linear response → Simple coupling model wrong

### Confirmation (Support framework)

1. **Both H₁ and H₂ supported** with p < 0.01, d > 1.0 → Strong evidence
2. **Beat period matters** (H₁): Aligned > Misaligned → Mechanism validated
3. **H₅ supported**: φ is near-optimal → Mathematical principles confirmed
4. **H₄ shows within-domain correlation** r² > 0.6 → Generalizable effects

---

## Resource Requirements (Revised)

### Computational
- **CPU**: 280 runs (H₁) × 2 hours = 560 CPU-hours (parallelizable to 14 hours on 40-core)
- **Additional**: 200 hours for H₂-H₇ = **760 CPU-hours total**
- **Storage**: ~15 GB for all results and trajectories
- **GPU**: Not required

### Hardware
- **FPGA**: Tang Nano 9K ($15, owned)
- **CMOS ICs**: $5-10 for CD4094, CD4053 (optional)
- **Test equipment**: Oscilloscope for verification (borrow or $50 USB scope)

### Software (All Free)
- Python 3.8+ (NumPy, SciPy, Matplotlib, Pandas)
- Gowin EDA (FPGA synthesis)
- Statistical software: R or Python statsmodels
- Lean 4 (formal verification, optional)

### Time (Realistic Estimate)
- **Week 1-5**: H₁ implementation (40h) + runs (14h) + analysis (20h) = **74 hours**
- **Week 6-9**: H₂ simulation (30h) + FPGA (30h) + analysis (20h) = **80 hours**
- **Week 10-12**: H₃ conditional (60h if pursued, 0h if skipped)
- **Week 13-16**: H₄-H₇ analysis (40h) + documentation (20h) = **60 hours**

**Total**: 274 hours (if H₃ skipped) or 334 hours (if H₃ pursued)
**Equivalent**: 8.5 weeks full-time OR 17 weeks half-time (4h/day)

---

## Pre-Registration Requirements (Complete)

### OSF Pre-Registration Must Include:

#### 1. Hypotheses (✅ Provided above)

#### 2. Experimental Protocol
```
## H₁ Computational Protocol
- Model: BioXen cyanobacteria ODE system
- Solver: scipy.integrate.solve_ivp, RK45 method
- Timestep: 0.1 hour
- Duration: 29.5 days (one full beat period)
- Parameters optimized: 8 circadian-coupled growth parameters
- Initial conditions: Random uniform [0.8, 1.2] × default
- Fitness: Final biomass density
- Random seed: 42 (for reproducibility)
```

#### 3. Data Exclusion Criteria
```
Exclude runs if:
- Solver fails to converge (>10% NaN values in trajectory)
- Runtime exceeds 10× median (likely infinite loop/bug)
- Biomass goes negative (unphysical)
- Biomass exceeds 10× initial (numerical instability)

Analysis: 
- Primary: Include all valid runs
- Sensitivity: Re-analyze excluding outliers >3 IQR
```

#### 4. Stopping Rules
```
- Fixed sample size: n=40 per condition (no interim analyses)
- No peeking at results until all 280 runs complete
- If equipment fails, restart entire batch for that condition
- Time limit: 5 weeks maximum for Phase 1
```

#### 5. Statistical Analysis Plan
```
Primary analysis:
- One-way ANOVA across 7 conditions
- If ANOVA significant (p<0.05), post-hoc Tukey HSD
- Effect size: Cohen's d for pairwise comparisons
- Report: Mean ± SEM, p-values (corrected and uncorrected)

Secondary analysis:
- Autocorrelation function (lag 0-100 hours)
- Parameter space coverage (convex hull volume)
- Beat phase analysis (29.5-day cycle)
```

#### 6. Violations Protocol
```
If anything deviates from pre-registration:
- Document deviation in supplementary materials
- Explain reason (e.g., "bug discovered in Week 3")
- Mark any analyses after deviation as "exploratory"
- Do not claim confirmation for post-hoc analyses
```

---

## Publication Strategy (Revised - PLOS ONE Focus)

Given your statement about PLOS ONE, here's a realistic strategy:

### Primary Target: PLOS ONE

**Why PLOS ONE**:
- ✅ Open access (broad visibility)
- ✅ Values methodological rigor and reproducibility
- ✅ Publishes negative results (outcome-neutral)
- ✅ Reasonable acceptance rate (~40-50%)
- ✅ Fast turnaround (3-4 months typical)
- ✅ No strict "novelty" requirement (scientifically sound > paradigm-shifting)
- ✅ Accepts computational/simulation studies
- ✅ Pre-registration increases acceptance likelihood

**Article Type**: Research Article

**Estimated Timeline**:
- Submission: Month 5 (after Phase 2 complete)
- Initial review: 6-8 weeks
- Revision: 2-4 weeks
- Final decision: Month 7-8
- Publication: Month 8-9

### Title Options (Based on Outcomes)

**If Both H₁ and H₂ Supported**:
"Quasiperiodic Temporal Forcing Improves Computational Performance Across Biological Optimization and Hardware Arithmetic: Evidence for Mathematical Analogy"

**If Only H₁ Supported**:
"Bio-Temporal Optimization: Quasiperiodic Environmental Cycles Improve Circadian-Coupled Biological Systems"

**If Only H₂ Supported**:
"Quasiperiodic Bitstream Generation Reduces Autocorrelation in Stochastic Computing Hardware"

**If Neither Supported (Negative Results)**:
"No Evidence for Computational Benefits of Quasiperiodic Temporal Forcing: A Pre-Registered Null Result"

### Structure (PLOS ONE Format)

```
Abstract (300 words)
├── Background
├── Methods Summary
├── Results Summary
└── Conclusions

Introduction (4-5 pages)
├── Computational challenges (biological optimization & stochastic computing)
├── Quasiperiodic dynamics in nature
├── Theoretical motivation (decorrelation hypothesis)
└── Specific hypotheses (H₁-H₇)

Materials and Methods (6-8 pages)
├── DTQC Model (H₁)
│   ├── Biological system description
│   ├── Environmental forcing protocol
│   └── Statistical analysis plan
├── QBG Implementation (H₂)
│   ├── LFSR architecture
│   ├── Simulation protocol
│   └── FPGA implementation details
├── Computational details
└── Pre-registration statement

Results (8-10 pages)
├── H₁: Bio-Temporal DTQC
│   ├── Main effect (7-condition comparison)
│   ├── Beat period dependence
│   └── Circadian coupling requirement
├── H₂: QBG Hardware
│   ├── Simulation results
│   ├── Hardware validation
│   └── Autocorrelation analysis
├── H₅: Golden Ratio Optimality
├── H₄: Cross-Domain Analysis (if applicable)
└── H₃, H₆, H₇: If pursued

Discussion (5-6 pages)
├── Summary of findings
├── Mechanistic interpretation
│   ├── Decorrelation (M₁)
│   ├── Biological resonance (M₂)
│   └── Domain specificity
├── Comparison to existing work
├── Limitations
│   ├── Simulation vs real biology
│   ├── Single hardware platform
│   └── Theoretical gaps
├── Implications
│   ├── For biological computing
│   ├── For hardware design
│   └── For general computational theory
└── Future directions

Acknowledgments
Data Availability (OSF repository link)
Funding Statement
References (40-60)
```

### Supplementary Materials

**Supplement 1**: Full Pre-Registration Document (OSF timestamped)
**Supplement 2**: Complete Parameter Tables
**Supplement 3**: Extended Statistical Analyses
**Supplement 4**: Source Code (Python, FPGA Verilog)
**Supplement 5**: Raw Data (CSV format)
**Supplement 6**: Reproducibility Guide

### Backup Targets (If PLOS ONE Rejects)

1. **Scientific Reports** (Nature family, similar open access model)
2. **PeerJ** (Open access, lower fees, fast publication)
3. **Frontiers in Computational Neuroscience** (if biological angle strong)
4. **IEEE Access** (if hardware angle strong)

### Expected Review Comments & Responses

**Common Concern #1**: "Why should we believe simulation results translate to real biology?"

**Pre-prepared Response**:
"We acknowledge this limitation explicitly. Our DTQC results represent a proof-of-concept using established circadian models. The H₁ validation specifically tests whether the predicted beat period (29.5 days) matters, which provides mechanistic evidence beyond simple parameter fitting. We propose wet-lab validation as future work (see Discussion, lines XXX)."

**Common Concern #2**: "The connection between domains seems forced."

**Pre-prepared Response**:
"We have revised our framing to emphasize mathematical analogy rather than mechanistic unity. H₄ explicitly tests whether improvements correlate within domains and across domains separately. If cross-domain correlation is weak, this itself is a scientifically valuable finding showing domain-specific mechanisms."

**Common Concern #3**: "Why didn't you test X?"

**Pre-prepared Response**:
"Our pre-registration (OSF link) established the hypothesis space before experiments began. Testing X would constitute post-hoc hypothesis generation, which we avoided to maintain confirmatory rigor. However, X is an excellent suggestion for future exploratory work [cite reviewer suggestion if appropriate]."

---

## Expected Outcomes & Implications (Revised)

### Scenario A: Strong Unified Success (40% probability, revised from 60%)
**Result**: H₁ supported with >20% improvement, H₂ supported with >20% improvement

**Evidence**:
- p < 0.01 for both hypotheses
- Large effect sizes (d > 1.0)
- Beat period dependence confirmed (aligned > misaligned)
- Hardware validation matches simulation within 20%

**Implications**:
- ✅ Mathematical analogy across scales validated (even if mechanisms differ)
- ✅ Publish in PLOS ONE with high confidence
- ✅ Proceed to optional H₃ (three-period extension)
- ✅ Consider grant applications for:
  - Wet-lab validation (cyanobacteria cultures with controlled lighting)
  - Multi-platform hardware testing (different FPGA families)
  - Theoretical formalization (Lean 4 proofs)
- ✅ Potential follow-up projects:
  - Neural network training with quasiperiodic learning rates
  - Quantum annealing with quasiperiodic schedules
  - Evolutionary algorithms with quasiperiodic mutation rates

**Grant Potential**: $10K-50K for exploratory follow-up (NSF, Templeton)

---

### Scenario B: Partial Success - DTQC Only (25% probability)
**Result**: H₁ supported (>15%), H₂ fails (<10%)

**Evidence**:
- Biological systems show clear benefit
- Beat period matters (aligned > misaligned)
- Circadian coupling required
- Hardware shows no benefit or marginal benefit

**Interpretation**: 
- Biological resonance is real
- Mathematical decorrelation alone insufficient for hardware
- Domain-specific mechanisms

**Implications**:
- ✅ Publish in PLOS ONE with biological focus
- ✅ Pivot to biological computing applications
- ✅ Investigate why hardware failed:
  - Autocorrelation not the bottleneck?
  - Sequence length too short?
  - Wrong timescale matching?
- ⚠️ Hardware angle was incorrect, but negative result is publishable
- ✅ Future work: Wet-lab validation of circadian predictions

**Publication Angle**: "Bio-Temporal Computing: Natural Circadian Cycles Enhance Biological Optimization"

---

### Scenario C: Partial Success - QBG Only (15% probability)
**Result**: H₁ fails (<10%), H₂ supported (>15%)

**Evidence**:
- Hardware shows clear autocorrelation reduction
- Stochastic computing accuracy improves
- Biological systems show no benefit or marginal benefit

**Interpretation**:
- Hardware decorrelation is real
- Biological model was wrong or forcing too weak
- Domain-specific mechanisms

**Implications**:
- ✅ Publish in PLOS ONE with hardware focus
- ✅ Pivot to hardware computing applications
- ✅ Investigate why DTQC failed:
  - Beat period too long for optimization horizon?
  - Coupling strength inadequate?
  - Wrong biological system?
- ✅ Future work: 
  - Multi-platform FPGA validation
  - ASIC implementation for production use
  - Patent quasiperiodic LFSR architecture

**Publication Angle**: "Quasiperiodic Bitstream Generation Improves Stochastic Computing Through Decorrelation"

---

### Scenario D: Null Result - Neither Works (15% probability)
**Result**: H₁ fails (<5%), H₂ fails (<5%)

**Evidence**:
- No significant improvements in either domain
- Effect sizes near zero
- p > 0.10 for all comparisons

**Interpretation**:
- Quasiperiodic hypothesis is incorrect for these applications
- Autocorrelation reduction doesn't translate to performance
- Theory needs fundamental revision

**Implications**:
- ✅ Still publishable! Pre-registered negative results are valuable
- ✅ Submit to PLOS ONE with "null result" emphasis
- ✅ High value to community (prevents others from pursuing dead end)
- ✅ Investigate why framework failed:
  - Was autocorrelation actually reduced?
  - Did we test wrong timescales?
  - Are there confounding factors?
- ✅ Pivot to alternative approaches:
  - Adaptive scheduling algorithms
  - Reinforcement learning for parameter tuning
  - Different hardware architectures

**Publication Angle**: "No Computational Benefit from Quasiperiodic Temporal Forcing: A Pre-Registered Negative Result"

**Citation Value**: Negative results with strong methods often get cited MORE than marginal positive results (prevents file-drawer problem)

---

### Scenario E: Ambiguous Results (5% probability)
**Result**: Trends but not significance (0.05 < p < 0.10 for both)

**Evidence**:
- Both show 8-12% improvements
- p-values around 0.06-0.08
- Effect sizes d ≈ 0.5-0.7 (medium)

**Interpretation**:
- Possible real effects but underpowered
- Need larger sample size
- May be smaller effect than hypothesized

**Implications**:
- ⚠️ Difficult to publish (neither confirmation nor clear null)
- ⚠️ Options:
  1. Increase n to 50-60 per condition (2 more weeks)
  2. Publish as "preliminary evidence" with clear caveats
  3. Report as negative (p>0.05) with discussion of trends
- ⚠️ Most honest approach: Increase sample size, report final result

**Action**: Extend Phase 1 by 2 weeks if this occurs

---

## Risk Mitigation Strategies

### Risk 1: Implementation Bugs
**Probability**: Medium (30%)
**Impact**: High (could invalidate results)

**Mitigation**:
- ✅ Unit tests for all core functions
- ✅ Compare to published models (reproduce known results first)
- ✅ Visualize trajectories during runs (sanity check)
- ✅ Independent code review (ask colleague or post on forum)
- ✅ Check extreme cases (static forcing should match literature)

---

### Risk 2: Hardware Unavailable
**Probability**: Low (10%)
**Impact**: Medium (delays Phase 2)

**Mitigation**:
- ✅ Already own Tang Nano 9K FPGA
- ✅ Can complete H₁ without hardware
- ✅ Simulation provides preliminary H₂ results
- ✅ Backup: Borrow oscilloscope or use cheaper USB logic analyzer

---

### Risk 3: Results Too Good To Be True
**Probability**: Low (15%)
**Impact**: High (likely indicates bug)

**Mitigation**:
- ✅ If improvement >40%, assume bug until proven otherwise
- ✅ Check for:
  - Data leakage (using test data in training)
  - Comparison errors (comparing wrong conditions)
  - Unit errors (mixing hours/days)
  - Random seed issues (deterministic vs stochastic)
- ✅ Rerun suspicious conditions 3 times independently
- ✅ Visualize actual trajectories, not just summary statistics

---

### Risk 4: Computer Crashes Mid-Experiment
**Probability**: Medium (20%)
**Impact**: Medium (lose partial results)

**Mitigation**:
- ✅ Save results after each run (not batch at end)
- ✅ Use checkpoint system (can resume from last completed run)
- ✅ Backup data to cloud storage daily
- ✅ Keep detailed log of which runs completed

---

### Risk 5: Time Overruns
**Probability**: High (50%)
**Impact**: Low to Medium

**Mitigation**:
- ✅ Timeline includes 20% buffer (16 weeks for 13 weeks of work)
- ✅ H₃ is optional (can skip if time constrained)
- ✅ H₆ and H₇ can be deferred to future work
- ✅ Minimum viable product: H₁ + H₂ + H₅ only (10 weeks)

---

## Success Metrics Summary (Revised)

### Minimum Viable Success ✅
**Definition**: Worth the time investment, publishable

- [ ] H₁ OR H₂ supported (p < 0.05, improvement ≥10%)
- [ ] Pre-registered methodology (no HARKing)
- [ ] Reproducible (code + data on OSF)
- [ ] Clear interpretation (positive or negative)
- [ ] Published (PLOS ONE or equivalent)

**Value**: Even if neither works, pre-registered negative result is publishable and valuable

---

### Target Success 🎯
**Definition**: Strong evidence, high impact

- [ ] Both H₁ AND H₂ supported (improvement ≥15%, p < 0.01)
- [ ] Mechanistic understanding (M₁ decorrelation confirmed)
- [ ] Beat period dependence demonstrated (aligned > misaligned)
- [ ] Hardware validated (not just simulation)
- [ ] Published with good citation potential

**Value**: Establishes mathematical analogy across domains, opens new research directions

---

### Exceptional Success 🌟
**Definition**: Paradigm-shifting, high visibility

- [ ] All primary hypotheses supported (H₁, H₂, H₅)
- [ ] Effect sizes >25% in both domains
- [ ] Three-period superiority demonstrated (H₃)
- [ ] Scale invariance confirmed (H₄ with r² > 0.7)
- [ ] Novel mechanism discovered (beyond simple decorrelation)
- [ ] Published with high visibility (>100 citations within 3 years)
- [ ] Enables practical applications (grant funding, patents)

**Value**: Opens new field of "quasiperiodic computation", potential for significant impact

---

## Final Gantt Chart Timeline

```
Week 0:  [Pre-Registration - OSF]
         └─ Hypothesis document, protocol, analysis plan

Week 1:  [H₁ Implementation]
         ├─ BioXen model setup
         ├─ Forcing function implementation  
         └─ Unit tests + validation

Week 2:  [H₁ Execution - Batch 1]
         ├─ Static control (40 runs)
         ├─ Solar only (40 runs)
         └─ Lunar only (40 runs)

Week 3:  [H₁ Execution - Batch 2]
         ├─ Solar+Lunar aligned (40 runs) ← PRIMARY
         ├─ Solar+Lunar misaligned (40 runs)
         └─ Checkpoint backups

Week 4:  [H₁ Execution - Batch 3]
         ├─ Golden ratio (40 runs)
         └─ Random dual (40 runs)

Week 5:  [H₁ Analysis]
         ├─ Statistical tests (ANOVA, post-hoc)
         ├─ Effect size calculations
         ├─ Autocorrelation analysis
         └─ DECISION POINT: Proceed to Phase 2?

Week 6:  [H₅ + H₂ Simulation]
         ├─ Golden ratio systematic sweep
         ├─ QBG LFSR simulation baseline
         └─ Autocorrelation measurements

Week 7:  [H₂ FPGA Implementation]
         ├─ Verilog coding (2-LFSR, 3-LFSR)
         ├─ Synthesis + place & route
         └─ Simulation validation

Week 8:  [H₂ Hardware Testing]
         ├─ FPGA measurements (autocorrelation)
         ├─ Stochastic multiplication tests
         ├─ Power consumption measurement
         └─ Compare to simulation

Week 9:  [H₂ Analysis + Phase 2 Report]
         ├─ Hardware vs simulation comparison
         ├─ Statistical analysis
         └─ DECISION POINT: Pursue H₃?

Week 10: [H₃ DTQC - CONDITIONAL]
         ├─ 30-day optimization setup
         └─ 3-period forcing implementation

Week 11: [H₃ QBG - CONDITIONAL]
         ├─ 3-LFSR implementation
         └─ Long bitstream tests (L=512)

Week 12: [H₃ Analysis - CONDITIONAL]
         ├─ Cross-domain comparison
         └─ Multi-period benefits assessment

Week 13: [H₄ Meta-Analysis]
         ├─ Compile results from H₁-H₃
         ├─ Within-domain correlations
         ├─ Cross-domain correlations
         └─ Mathematical analogy test

Week 14: [H₆ Phase Boundaries]
         ├─ Synthetic problems with tunable J
         ├─ Sweep coupling strength
         └─ Identify phase transition

Week 15: [H₆ Continued + H₇ Setup]
         ├─ Phase boundary analysis
         └─ Scaling law data compilation

Week 16: [H₇ + Final Documentation]
         ├─ Retrospective scaling analysis
         ├─ Complete documentation
         ├─ Prepare manuscript draft
         └─ Package OSF repository

Week 17: [Manuscript Writing - Buffer]
Week 18: [Final Revisions - Buffer]
```

**Critical Path**: Week 0-5 (H₁ validation)
**Conditional Path**: Week 10-12 (H₃, only if H₁+H₂ strong)
**Buffer**: Week 17-18 (handles overruns)

---

## Data Management Plan

### Storage Structure
```
project_root/
├── data/
│   ├── raw/
│   │   ├── h1_dtqc/
│   │   │   ├── static_control/
│   │   │   ├── solar_only/
│   │   │   ├── lunar_only/
│   │   │   ├── solar_lunar_aligned/
│   │   │   ├── solar_lunar_misaligned/
│   │   │   ├── golden_ratio/
│   │   │   └── random_dual/
│   │   └── h2_qbg/
│   │       ├── simulation/
│   │       └── hardware/
│   ├── processed/
│   └── analysis/
├── code/
│   ├── models/
│   │   ├── dtqc_biomodel.py
│   │   └── qbg_lfsr.py
│   ├── forcing/
│   │   └── quasiperiodic_generator.py
│   ├── analysis/
│   │   ├── statistics.py
│   │   └── visualization.py
│   └── fpga/
│       └── lfsr_quasiperiodic.v
├── docs/
│   ├── preregistration.md
│   ├── protocol.md
│   └── changelog.md
└── results/
    ├── figures/
    ├── tables/
    └── manuscript/
```

### Backup Strategy
- **Real-time**: Auto-save after each run
- **Daily**: Git commit + push to GitHub (private repo)
- **Weekly**: Full backup to external drive
- **Monthly**: Archive to cloud storage (Google Drive/Dropbox)

### Data Sharing
- **Code**: GitHub (make public at publication)
- **Data**: OSF repository (DOI assigned)
- **Manuscript**: PeerJ Preprints or bioRxiv (if pursuing publication)
- **License**: MIT for code, CC-BY for data

---

## Ethical Considerations

### Research Integrity
- ✅ Pre-registration prevents p-hacking and HARKing
- ✅ Report all pre-registered analyses (even if non-significant)
- ✅ Clearly distinguish confirmatory vs exploratory results
- ✅ If protocol violated (e.g., bug found), document in supplementary materials

### Computational Ethics
- ⚠️ This research uses significant computational resources (760 CPU-hours)
- ✅ Justify usage: Advancing scientific understanding of quasiperiodic computation
- ✅ Optimize code to minimize waste (vectorization, efficient algorithms)
- ✅ If using shared cluster, follow usage policies

### Reproducibility
- ✅ Provide complete source code
- ✅ Document exact versions (Python 3.10.4, NumPy 1.23.0, etc.)
- ✅ Include random seeds for deterministic reproduction
- ✅ Write README with step-by-step instructions

### Authorship
- If this were for publication, solo authorship is appropriate (you designed, executed, analyzed)
- If collaborators contribute significantly (>10% effort), include as co-authors
- If using substantial code from others, cite appropriately

---

## Personal Learning Outcomes

Regardless of whether the hypotheses are supported, you will gain:

### Technical Skills
- ✅ Rigorous experimental design (pre-registration, power analysis)
- ✅ Advanced statistical analysis (ANOVA, effect sizes, correlations)
- ✅ FPGA development (Verilog, synthesis, hardware testing)
- ✅ Scientific Python (NumPy, SciPy, Matplotlib)
- ✅ Data visualization (publication-quality figures)

### Scientific Skills
- ✅ Hypothesis formulation and falsification
- ✅ Cross-domain thinking (biology + hardware)
- ✅ Mechanistic reasoning (decorrelation, resonance)
- ✅ Literature review and synthesis
- ✅ Scientific writing (if pursuing publication)

### Conceptual Insights
- ✅ Understanding of quasiperiodic dynamics
- ✅ Biological circadian systems
- ✅ Stochastic computing principles
- ✅ Hardware-software co-design
- ✅ Mathematical analogies across scales

### Meta-Skills
- ✅ Project management (16-week timeline)
- ✅ Risk mitigation strategies
- ✅ Dealing with negative results gracefully
- ✅ Balancing exploration vs exploitation in research
- ✅ Knowing when to pivot vs persist

---

## Conclusion

This revised framework addresses the critical weaknesses identified:

1. ✅ **"Unified theory" → "Mathematical analogy"** (more honest framing)
2. ✅ **Expanded H₁ controls** (7 conditions to isolate mechanism)
3. ✅ **Increased sample size** (n=40 per condition, proper power)
4. ✅ **Hardware validation** (FPGA measurements, not just simulation)
5. ✅ **Tightened H₄** (±20% band, within-domain correlations)
6. ✅ **Realistic publication target** (PLOS ONE, not Nature)
7. ✅ **Exploratory markers** (H₃, H₇ clearly labeled)
8. ✅ **Complete pre-registration** (data exclusion, stopping rules)

**The core insight remains**: If quasiperiodic temporal forcing improves computation, it should work across domains through analogous mathematical principles (even if the physical mechanisms differ).

**The key improvement**: We now test this claim rigorously with proper controls, adequate power, and realistic expectations.

**The valuable outcome**: Whether confirmed or rejected, this framework will produce scientifically rigorous results that advance understanding—and that's what good science is about.

---

*This revised framework provides a more realistic, rigorous, and honest approach to testing quasiperiodic computation principles. It acknowledges limitations, includes critical controls, and prepares for all possible outcomes (including negative results). Whether you publish or not, executing this plan will develop valuable scientific skills and produce genuine insights.*