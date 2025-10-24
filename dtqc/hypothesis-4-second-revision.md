# Revised Unified QBG-DTQC Hypothesis Framework
## Timeline-Agnostic Research Protocol

## Meta-Hypothesis: Analogous Cross-Scale Quasiperiodic Effects

**Quasiperiodic mixing with incommensurate frequencies may improve computational processes across vastly different timescales—from nanosecond stochastic arithmetic (QBG) to multi-day biological optimization (DTQC)—through mathematically analogous (though potentially mechanistically distinct) decorrelation mechanisms.**

**Key Principle**: This framework tests whether similar mathematical structures produce similar computational benefits across scales, NOT whether they represent the same physical mechanism. The domains may share mathematical properties while differing fundamentally in their underlying processes.

---

## Core Hypotheses (Ordered by Priority)

### **H₁: Bio-Temporal DTQC Validation** (Primary - Phase 1) 🎯

**Statement**: Quasiperiodic environmental forcing at biologically-relevant timescales (τ₁=24h solar, τ₂=24.84h lunar) improves optimization of circadian-coupled biological systems by ≥15% compared to static conditions, and this improvement specifically requires the 29.5-day beat period.

**Formal**:
```
μ(solar+lunar) ≥ μ(static) × 1.15
p < 0.05, Cohen's d ≥ 0.8
n = 40 per condition
```

**Experimental Design**: 280 optimization runs (7 conditions × 40 replicates)

**Conditions**:
1. **Static control** (no forcing) - baseline
2. **Solar only** (24h single period) - tests single-period resonance
3. **Lunar only** (24.84h single period) - tests lunar-specific effects
4. **Solar+Lunar aligned** (24h + 24.84h, correct beat) - PRIMARY TEST
5. **Solar+Lunar misaligned** (24h + 25.84h, disrupted beat) - tests beat period specificity
6. **Golden ratio** (24h + 38.8h) - tests biological specificity
7. **Random dual period** (24h + 27.3h) - tests against arbitrary dual forcing

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

**Statistical Analysis**:
- One-way ANOVA across 7 conditions
- Post-hoc: Tukey HSD for pairwise comparisons
- Effect sizes: Cohen's d with 95% CI
- Multiple comparison correction: Holm-Bonferroni
- Report both corrected and uncorrected p-values

**Resources**: 
- Python + BioXen cyanobacteria ODE model
- Pre-registration on OSF before data collection begins
- Computational: 280 runs (parallelizable)

**Completion Criteria**: All 280 runs finished, statistical analysis complete, results interpretable

---

### **H₂: QBG Hardware Correlation Reduction** (Secondary - Phase 2)

**Statement**: Dual-LFSR quasiperiodic bitstream generation with golden ratio periods (τ₂/τ₁ = φ = 1.618) reduces autocorrelation by ≥50% and improves stochastic computing accuracy by 10-30% compared to single-LFSR, as measured in both simulation AND actual FPGA hardware.

**Formal**:
```
autocorr_lag1(QBG) ≤ 0.5 × autocorr_lag1(single-LFSR)
error(QBG, L=256) ≤ 0.85 × error(single-LFSR, L=256)
Both conditions must hold in simulation AND hardware
```

**Test Application**: Stochastic multiplication (8-bit × 8-bit)

**Phases**:

#### Phase 2a: Simulation Baseline
**Conditions**:
1. Single LFSR baseline
2. Two-LFSR QBG (τ₁=100, τ₂=162 cycles)
3. Three-LFSR QBG (τ₁=100, τ₂=162, τ₃=273 cycles)

**Measurements** (n=100 trials per condition):
- Autocorrelation function (lag 0-50)
- Error rate vs sequence length (L=64, 128, 256, 512)
- Bitstream entropy rate

#### Phase 2b: FPGA Hardware Validation
**Platform**: Tang Nano 9K FPGA
**Implementation**: Verilog synthesis of 2-LFSR and 3-LFSR architectures

**Hardware Measurements** (n=50 per condition):
- Autocorrelation via captured bitstreams (≥10,000 bits)
- Error rates for stochastic multiplication
- Resource utilization (LUT count)
- Power consumption (if measurable)

**Critical Predictions**:
1. ✓ **Simulation**: Autocorrelation QBG < 0.1, single-LFSR > 0.3
2. ✓ **Simulation**: Error at L=256: QBG ≈1.7%, single ≈2.1% (19% reduction)
3. ✓ **Hardware**: Autocorrelation reduction ≥40% (allowing 10% degradation vs simulation)
4. ✓ **Hardware**: Error reduction ≥15% (allowing some degradation)
5. ✓ **Hardware**: FPGA overhead <20% LUTs relative to stochastic core
6. ✓ **Hardware**: No significant power consumption increase (<10%)

**Falsification Criteria**:
- **Strong rejection**: Autocorrelation reduction <30% in simulation
- **Hardware failure**: Hardware results show <20% of simulation benefit
- **Cost failure**: FPGA overhead >25% OR power increase >20%

**Completion Criteria**: 
- Phase 2a: All simulations complete, autocorrelation and error metrics computed
- Phase 2b: Hardware implemented, measurements taken, simulation-vs-hardware comparison documented

---

### **H₃: Three-Period Superiority** (Exploratory - Phase 4)

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

**Entry Criteria** (ALL must be satisfied):
- ✅ H₁ shows improvement >20% with p < 0.01
- ✅ H₂ shows improvement >20% with p < 0.01
- ✅ Sufficient resources remain for additional testing

**Skip Criteria** (ANY triggers skip):
- ❌ Either H₁ or H₂ shows improvement <20%
- ❌ Either H₁ or H₂ has p > 0.01 (marginal significance)
- ❌ Resource constraints prevent additional experiments

**Test Design**:
- DTQC: 30-day vs 7-day cyanobacteria optimization (n=20 per condition)
- QBG: L=512 vs L=128 stochastic operations (n=100 trials)

**Exploratory Predictions** (hypothesis-generating, not confirmatory):
1. ? DTQC 30-day: 3-period MAY beat 2-period by ≥5%
2. ? QBG L=512: 3-LFSR MAY beat 2-LFSR by ≥5%
3. ? Short duration/length: expect no significant difference
4. ? Improvement MAY scale with duration/length ratio

**Analysis Approach**: 
- Report effect sizes with confidence intervals
- Do NOT claim confirmation even if p<0.05
- Treat as exploratory hypothesis generation
- Suggest follow-up studies if patterns emerge

**Completion Criteria**: 
- If pursued: All experiments complete, effect sizes reported with appropriate caveats
- If skipped: Document reasoning in results section

---

### **H₄: Mathematical Analogy Test** (Phase 3)

**Statement**: If quasiperiodic mixing benefits both domains through analogous mathematical mechanisms (decorrelation), then the relative improvement ratios should correlate across different problem types within each domain, even if absolute magnitudes differ between domains.

**Formal** (REVISED for scaling-adjusted analysis):
```
Within-domain correlation test:
- Test 5+ different problems in DTQC domain
- Test 5+ different problems in QBG domain
- Compute normalized improvement: imp_norm = imp / (duration/τ_beat)
- Within-domain correlation: r² > 0.6

Cross-domain similarity test:
ONLY if both domains show consistent improvements:
improvement_ratio = median(improvement_DTQC) / median(improvement_QBG)
0.8 ≤ improvement_ratio ≤ 1.25 (±20%)
```

**Interpretation Framework**:
- **Strong analogy** (r²>0.6 within domains, ratio ∈ [0.8,1.25]): Mathematical principles generalize
- **Weak analogy** (r²>0.6 within domains, ratio outside [0.8,1.25]): Similar math, different magnitudes
- **Domain-specific** (low r² within domains): Each domain has unique mechanisms
- **No effect** (no improvements): Quasiperiodicity doesn't help computation

**Test Problems**:

**DTQC (5 biological systems)**:
1. Cyanobacteria growth optimization (primary, from H₁)
2. Synthetic circadian oscillator
3. Yeast cell cycle model
4. Plant photoperiod response
5. Mammalian sleep-wake cycle

**QBG (5 stochastic operations)**:
1. Multiplication (8-bit × 8-bit) (primary, from H₂)
2. Squaring (8-bit²)
3. Division (8-bit ÷ 8-bit)
4. Square root approximation
5. Sigmoid function approximation

**Sample Size**: n=20 replicates per problem/operation (minimum)

**Critical Predictions**:
1. ✓ Within DTQC: If cyanobacteria improves 20%, yeast should improve 15-25%
2. ✓ Within QBG: If multiplication improves 18%, squaring should improve 13-23%
3. ? Cross-domain: Improvements MAY be similar magnitude (but not required for analogy)

**Falsification Criteria**:
- **Weak analogy**: r² < 0.4 within either domain
- **No analogy**: Both domains show r² < 0.3

**Completion Criteria**: 
- All 10 problems/operations tested
- Correlation analysis complete
- Scaling relationships characterized

---

### **H₅: Golden Ratio Near-Optimality** (Phase 2 - Parallel with H₂)

**Statement**: For two-period systems with finite sequence lengths, the golden ratio φ ≈ 1.618 should show near-optimal decorrelation efficiency due to its properties as the most poorly approximable irrational number. However, this optimality may be sequence-length dependent.

**Theoretical Basis**: 
- φ has continued fraction [1;1,1,1,...] (slowest rational convergence)
- This maximizes "irrationality" for avoiding resonances
- For finite L, optimality may shift to nearby rational approximations

**Formal**:
```
Define η(r) = autocorr_reduction(r) / computational_cost(r)
η(φ) ≥ 0.95 × max{η(√2), η(√3), η(√5), η(e/2), η(π/2), η(F_n)}
(Near-optimal = within 5% of best)

where F_n are Fibonacci ratios: 13/8, 21/13, 34/21, etc.
```

**Test**: Systematic ratio comparison (n=5000 trials per ratio)

**Ratios to Test**:
- √2 = 1.414
- 13/8 = 1.625 (Fibonacci approximation)
- 21/13 = 1.615 (closer Fibonacci)
- **φ = 1.618034...** ← PREDICTED NEAR-OPTIMUM
- 34/21 = 1.619 (even closer Fibonacci)
- 162/100 = 1.620 (practical rational)
- √3 = 1.732
- π/2 = 1.571
- e/2 = 1.359
- √5 = 2.236

**Sequence Lengths to Test**: L = 64, 128, 256, 512

**Critical Predictions**:
1. ✓ φ achieves ≥95% of best observed decorrelation
2. ✓ Simple rational approximations (162/100) perform within 2% of φ
3. ✓ φ maintains ≥90% performance with ±2% perturbation (robustness)
4. ? Optimal ratio MAY shift with sequence length (e.g., Fibonacci approximations better at short L)

**Falsification Criteria**:
- **Strong rejection**: φ performs <90% of best ratio
- **Weak rejection**: φ performs 90-94% of best (near-optimal not achieved)
- **Length-dependence**: Different L values have clearly different optimal ratios (φ not universal)

**Completion Criteria**: All ratios tested at all sequence lengths, near-optimality claim evaluated

---

### **H₆: Phase Boundary Robustness** (Phase 4 - DTQC-specific)

**Statement**: DTQC benefits require coupling strength exceeding a phase boundary where forcing periods couple strongly enough to system dynamics. Below this threshold, forcing is too weak to produce computational benefits.

**Theoretical Derivation** (CORRECTED for dimensional consistency):
```
For environmental forcing ε·sin(2πt/τᵢ) coupled to system via parameter J:
- Forcing amplitude: ε (dimensionless, relative to baseline)
- Coupling rate: J (units: 1/time)
- Response timescale: 1/J
- Beat period: τ_beat = τ₁τ₂/|τ₂-τ₁|

For forcing to influence system on beat timescale:
J·τ_beat > ε/ε₀ (dimensionless coupling strength)

where ε₀ is the natural fluctuation scale of the system

For ε=0.1, ε₀=0.05, τ_beat=29.5 days:
J_critical = (ε/ε₀) / τ_beat = 2 / (29.5 days) = 0.0678 day⁻¹
```

**Formal**:
```
∀ J > 1.2×J_critical: improvement ≥ 15%
∀ J < 0.8×J_critical: improvement < 5%
Transition width: ±20% around J_critical
```

**Test**: Synthetic optimization problem with tunable coupling
- Sweep J from 0.02 to 0.15 day⁻¹ (10 values spanning predicted J_critical)
- n=20 replicates per J value
- Measure fitness improvement vs static control

**Critical Predictions**:
1. ✓ Sharp transition near predicted J_critical
2. ✓ Sigmoid-like response curve (not linear)
3. ✓ Performance plateaus above 2×J_critical
4. ✓ Below J_critical, performance ≈ static control

**Falsification Criteria**:
- **No boundary**: Linear response across all J values
- **Wrong prediction**: Transition occurs at J > 2×predicted OR J < 0.5×predicted
- **No threshold**: Gradual improvement with no clear transition

**Entry Criteria**:
- H₁ must be supported (otherwise no benefit to explain)
- Interest in mechanistic understanding remains high

**Completion Criteria**: 
- J sweep complete
- Phase transition characterized (or absence documented)
- Comparison to theoretical prediction

---

### **H₇: Adaptive Period Selection Scaling** (Phase 4 - Exploratory)

**Status**: EXPLORATORY - post-hoc pattern analysis, not a priori prediction

**Statement**: Optimal periods MAY scale with problem characteristics following power law relationships, but this will be investigated retrospectively after H₁-H₆ complete.

**Proposed Scaling Laws** (to be tested, not assumed):

**DTQC**:
```
D < 7 days:     τ = [24h, 24.84h]
7 ≤ D < 30:     τ = [24h, 24.84h, 654.6h]  
30 ≤ D < 180:   τ = [24h, 24.84h, 654.6h, 8766h]

Hypothesized relationship: 
optimal_τ_max ∝ D^α where 0.5 < α < 1.5
```

**QBG**:
```
L < 128:        τ = [10, 16] cycles
128 ≤ L < 512:  τ = [100, 162] cycles
L ≥ 512:        τ = [100, 162, 273] cycles

Hypothesized relationship:
optimal_τ_max ∝ L^β where 0.5 < β < 1.5
```

**Analysis Approach**: 
- Compile all improvement data from H₁-H₆
- Search for scaling relationships via log-log regression
- Generate hypotheses for future dedicated study
- DO NOT claim confirmation (this is hypothesis-generating)
- Report as "patterns observed" not "laws established"

**Completion Criteria**: 
- Retrospective analysis complete
- Scaling relationships characterized (if any)
- Future research directions identified

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

**Test During**: H₁ and H₂ primary experiments

---

### **M₂: Resonance with Natural Dynamics** (DTQC-specific)

**Hypothesis**: For DTQC, the improvement requires resonance between external forcing periods and internal circadian rhythms. This is domain-specific and does NOT apply to QBG.

**Observable Predictions**:
1. Circadian-coupled model shows 15-25% improvement
2. Circadian-disabled model shows <5% improvement
3. Optimal performance at specific beat phases
4. Solar-only and Lunar-only individually show 5-10% improvement (single-period resonance exists)

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

**Test During**: H₁ experiments (include circadian-disabled condition as control)

---

### **M₃: Multi-Scale Energy Landscape Navigation** (Exploratory)

**Hypothesis**: Multiple incommensurate periods MAY create multi-scale perturbations that help escape local minima at different timescales. This is speculative.

**Observable Predictions** (if H₃ pursued):
1. Single-period forcing escapes "fast" local minima only
2. Two-period forcing escapes fast + medium minima
3. Three-period forcing escapes fast + medium + slow minima

**Measurement**:
- Basin of attraction analysis via perturbation sensitivity
- Time-to-escape from synthetic local minima
- Final fitness distributions (multimodality)
- Spectral analysis of fitness trajectories

**Falsification**: No relationship between number of periods and escape from local minima

**Status**: Will only be tested if H₃ is pursued (conditional on H₁ and H₂ showing >20% improvements)

---

## Integrated Experimental Design

### Phase 0: Foundation & Validation
**MUST COMPLETE BEFORE ANY EXPERIMENTS**

```
Pre-Registration:
□ Register on OSF with full protocol
□ Timestamped commitment to hypotheses, sample sizes, analyses
□ Document any protocol changes if they occur

Model Implementation:
□ Implement BioXen cyanobacteria ODE model
□ Implement quasiperiodic forcing functions
□ Write unit tests for all core components
□ Validate against literature (reproduce published results)

Critical Validation Checks:
□ Test 1: Circadian coupling strength
  - Compare coupled vs decoupled optimization
  - Requirement: >5% fitness difference
  - If fails: Model unsuitable for H₁, abort or revise
  
□ Test 2: Timescale response sweep
  - Test forcing periods: 12h, 24h, 48h, 7d, 14d, 30d
  - Requirement: Measurable response at 24h AND 30d
  - If fails: Beat period may not couple, revise hypothesis
  
□ Test 3: Landscape structure analysis
  - Estimate ruggedness via Hessian eigenvalues
  - Requirement: Not purely convex (local minima exist)
  - If fails: Quasiperiodic forcing unnecessary
  
□ Test 4: Beat period sensitivity pilot
  - Compare 7-day vs 30-day optimization (n=5 each)
  - Requirement: >3% difference suggests beat matters
  - If fails: Increase pilot to n=10 or reconsider hypothesis

Decision Point:
✅ All tests pass → Proceed to Phase 1
❌ Any critical test fails → Debug model or revise hypothesis
⚠️ Marginal results → Increase pilot size before committing
```

**Completion Criteria**: 
- All validation checks pass
- Model behavior understood and documented
- GO/NO-GO decision made and recorded

---

### Phase 1: Primary Hypothesis Testing (H₁ - DTQC)
**CAN START ONCE PHASE 0 COMPLETE**

```
Experiments: 280 runs total (7 conditions × 40 replicates)

Execution:
□ Static control (40 runs)
□ Solar only - 24h (40 runs)
□ Lunar only - 24.84h (40 runs)
□ Solar+Lunar aligned (40 runs) ← PRIMARY TEST
□ Solar+Lunar misaligned - 25.84h (40 runs)
□ Golden ratio - 24h + 38.8h (40 runs)
□ Random dual - 24h + 27.3h (40 runs)

Notes:
- Conditions can be run in any order
- Fully parallelizable if resources allow
- Save results after EACH run (not batched)
- NO PEEKING at results until all 280 complete

Data Management:
□ Checkpoint system implemented (can pause/resume)
□ Progress log updated after each session
□ Backups created regularly
□ Raw data preserved (never overwrite)

Analysis (ONLY after all 280 runs complete):
□ ANOVA across 7 conditions
□ Post-hoc comparisons (Tukey HSD)
□ Effect size calculations (Cohen's d with 95% CI)
□ Autocorrelation analysis (M₁ test)
□ Parameter space coverage (convex hull volume)
□ Circadian coupling validation (M₂ test)
□ Beat phase analysis (29.5-day periodicity)

Secondary Analyses:
□ Trajectory visualizations
□ Convergence rate comparisons
□ Sensitivity to initial conditions
□ Time-series spectral analysis
```

**Decision Point** (End of Phase 1):

| Outcome | Condition | Next Steps |
|---------|-----------|------------|
| **Strong Success** | p<0.01, improvement >20% | Proceed to Phase 2, consider Phase 4 |
| **Moderate Success** | p<0.05, improvement 15-20% | Proceed to Phase 2, skip Phase 4 |
| **Trend** | 0.05<p<0.10, improvement 10-15% | Increase to n=50, rerun |
| **Weak Signal** | p<0.05 but improvement <10% | Proceed to Phase 2, temper expectations |
| **Mechanism Failure** | p<0.05 but no beat dependence | Investigate alternative mechanisms |
| **Null Result** | p>0.10 or improvement <5% | Publish negative result, Phase 2 optional |
| **Negative Effect** | Performance degradation | Check for bugs, investigate pathology |

**Completion Criteria**: 
- All 280 runs complete
- Statistical analysis finished
- Decision documented for Phase 2

---

### Phase 2: Hardware Validation (H₂ - QBG)
**CAN START AFTER PHASE 0 (PARALLEL WITH PHASE 1 IF DESIRED)**

#### Phase 2a: Simulation Baseline

```
Implementation:
□ Single LFSR baseline (typically 16-bit)
□ Dual-LFSR QBG (τ₁=100, τ₂=162 cycles)
□ Triple-LFSR QBG (τ₁=100, τ₂=162, τ₃=273 cycles)
□ Stochastic multiplication circuit (8-bit × 8-bit)

Tests (n=100 trials per condition):
□ Autocorrelation measurement (lag 0-50)
□ Error rate vs sequence length (L=64, 128, 256, 512)
□ Bitstream entropy rate
□ Spectral analysis of bitstreams

Parallel Track: Golden Ratio Sweep (H₅)
□ Test ratios: √2, 13/8, 21/13, φ, 34/21, 162/100, √3, π/2, e/2, √5
□ Measure autocorrelation and error for each (n=5000 per ratio)
□ Test at multiple sequence lengths (L=64, 128, 256, 512)
□ Compare φ performance to alternatives

Requirements for Phase 2a Success:
□ QBG autocorrelation < 0.5 × single-LFSR
□ QBG error < 0.85 × single-LFSR (at L=256)
□ φ achieves ≥95% of best observed ratio
```

**Completion Criteria (Phase 2a)**: 
- All simulations complete
- Baseline performance established
- Golden ratio near-optimality evaluated

#### Phase 2b: FPGA Hardware Validation

```
Hardware Implementation:
□ Write Verilog for 2-LFSR QBG
□ Write Verilog for 3-LFSR QBG (if Phase 2a promising)
□ Create testbench (simulation verification)
□ Synthesize for Tang Nano 9K
□ Generate programming bitstream
□ Test basic functionality

Resource Measurement:
□ LUT utilization (expect ~45 LUTs for 2-LFSR, ~70 for 3-LFSR)
□ Register count
□ Maximum clock frequency
□ Power consumption (if measurable)

Hardware Testing (n=50 measurements per condition):
□ Capture bitstreams via UART/USB (≥10,000 bits per capture)
□ Compute autocorrelation in Python
□ Measure error rates for stochastic multiplication
□ Compare to simulation baseline
□ Characterize hardware-specific effects

Requirements for Phase 2b Success:
□ Hardware autocorrelation reduction ≥40% (vs sim 50%, allows 10% degradation)
□ Hardware error reduction ≥15% (vs sim 20%, allows degradation)
□ LUT overhead <20% relative to stochastic core
□ Power increase <10%
□ Implementation stable (no glitches, timing violations)
```

**Decision Point** (End of Phase 2):

| H₁ Result | H₂ Result | Interpretation | Next Steps |
|-----------|-----------|----------------|------------|
| ✅ Strong | ✅ Strong | Mathematical analogy validated | Phase 3 (H₄), consider Phase 4 |
| ✅ Moderate | ✅ Moderate | Both work, modest effects | Phase 3 (H₄), skip Phase 4 |
| ✅ Strong | ❌ Fail | DTQC-specific (biological resonance) | Focus publication on DTQC |
| ❌ Fail | ✅ Strong | QBG-specific (hardware decorrelation) | Focus publication on QBG |
| ❌ Fail | ❌ Fail | Quasiperiodicity doesn't help | Publish joint negative result |
| ⚠️ Trend | ⚠️ Trend | Possible effects, underpowered | Increase sample sizes |

**Completion Criteria (Phase 2b)**: 
- Hardware implemented and tested
- Simulation vs hardware comparison complete
- Performance gaps understood and documented

---

### Phase 3: Cross-Domain Analysis (H₄)
**REQUIRES PHASE 1 AND PHASE 2A COMPLETE**

```
DTQC Problem Set (n=20 per problem):
□ Cyanobacteria growth (already done from H₁)
□ Synthetic circadian oscillator
□ Yeast cell cycle model
□ Plant photoperiod response
□ Mammalian sleep-wake cycle

QBG Operation Set (n=100 per operation):
□ Multiplication 8×8 (already done from H₂)
□ Squaring (8²)
□ Division (8÷8)
□ Square root approximation
□ Sigmoid function approximation