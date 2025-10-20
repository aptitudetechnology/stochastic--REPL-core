# QBG Bio-Temporal Computing: Formal Hypothesis

## Research Question
Does quasiperiodic environmental forcing at biologically-relevant timescales (solar 24h + lunar 24.84h) improve computational optimization of circadian-coupled biological processes compared to static or single-period forcing?

---

## Null and Alternative Hypotheses

### H₀ (Null Hypothesis)
Quasiperiodic forcing with solar/lunar periods (τ₁=24h, τ₂=24.84h) provides **no significant improvement** in optimization performance compared to static conditions when optimizing circadian-coupled biological systems.

Mathematically:
```
μ(solar+lunar) - μ(static) ≤ 0
```
Where μ represents mean fitness (total carbon fixation over 30 days)

### H₁ (Alternative Hypothesis)
Quasiperiodic forcing with solar/lunar periods **significantly improves** optimization performance by ≥15% compared to static conditions.

Mathematically:
```
μ(solar+lunar) - μ(static) ≥ 0.15 × μ(static)
```

**Significance level**: α = 0.05 (two-tailed t-test)
**Effect size target**: Cohen's d ≥ 0.8 (large effect)

---

## Subsidiary Hypotheses

### H₁.₁: Biological Timescale Specificity
**Hypothesis**: The improvement is specific to biologically-relevant timescales (24h/24.84h), not a generic effect of quasiperiodicity.

**Test**: Compare solar+lunar (24h/24.84h) vs golden ratio (24h/38.8h)

**Prediction**: 
```
μ(solar+lunar) > μ(golden ratio)
```

**Interpretation**:
- If TRUE: Biological timescale matching is critical (supports biomimetic approach)
- If FALSE: Pure quasiperiodicity matters more than biological realism (mathematical effect)

---

### H₁.₂: Beat Period Dependence
**Hypothesis**: The 29.5-day beat period created by solar/lunar interference is necessary for full optimization benefit.

**Test**: Compare optimization runs of different lengths:
- 7 days (< beat period)
- 15 days (½ beat period)  
- 30 days (1 full beat period)
- 60 days (2 beat periods)

**Prediction**:
```
Improvement correlates with run length up to ~30 days, then saturates
```

**Interpretation**:
- If TRUE: Beat period exploration is critical mechanism
- If FALSE: Immediate decorrelation effect dominates

---

### H₁.₃: Circadian Coupling Requirement
**Hypothesis**: The improvement requires organisms/processes with endogenous circadian rhythms that can resonate with external forcing.

**Test**: Compare two models:
- **Model A**: Circadian-coupled photosynthesis (as described)
- **Model B**: Same photosynthesis but with circadian clock disabled

**Prediction**:
```
Improvement(Model A) > Improvement(Model B)
```

**Interpretation**:
- If TRUE: Resonance between external forcing and internal rhythms is key
- If FALSE: External modulation helps regardless of internal dynamics

---

### H₁.₄: Multi-Timescale Necessity
**Hypothesis**: Dual-period forcing is superior to single-period forcing.

**Test**: Compare three conditions:
- Static (no forcing)
- Solar only (24h)
- Solar+Lunar (24h + 24.84h)

**Prediction**:
```
μ(solar+lunar) > μ(solar only) > μ(static)
```

**Interpretation**:
- If TRUE: Multi-timescale exploration provides additional benefit
- If FALSE: Single circadian forcing is sufficient

---

## Mechanistic Hypotheses

### M₁: Energy Landscape Navigation
**Hypothesis**: Quasiperiodic forcing helps optimization escape local minima by providing multi-timescale perturbations.

**Observable predictions**:
1. Static optimization converges quickly but to suboptimal solutions
2. Solar+lunar optimization takes longer but finds better global optima
3. Final parameter distributions differ significantly between conditions

**Measurement**: 
- Compare convergence curves (fitness vs iteration)
- Analyze basin of attraction (perturbation sensitivity)
- Measure parameter variance across runs

---

### M₂: Biologically-Relevant Parameter Space
**Hypothesis**: Evolution has optimized biological systems for solar/lunar timescales, so those timescales naturally explore the "right" parameter regions.

**Observable predictions**:
1. Optimal parameters under solar+lunar forcing match known biological values
2. Parameters found under golden ratio forcing are biologically unrealistic
3. Organisms show performance peaks at specific beat phases

**Measurement**:
- Compare optimized parameters to published experimental values
- Check if parameters fall within physiological bounds
- Correlate performance with beat phase (29.5-day modulation)

---

### M₃: Temporal Decorrelation
**Hypothesis**: Quasiperiodic forcing reduces temporal autocorrelation in the optimization landscape, preventing premature convergence.

**Observable predictions**:
1. Autocorrelation of fitness trajectory decreases with quasiperiodicity
2. Exploration radius (parameter space volume) increases
3. Revisitation probability of same parameter regions decreases

**Measurement**:
- Compute autocorrelation function of fitness time series
- Measure parameter space coverage (convex hull volume)
- Calculate return probability (how often optimization revisits same region)

---

## Experimental Design

### Independent Variables
1. **Forcing type** (categorical, 4 levels):
   - Static (constant light/temp)
   - Solar (24h only)
   - Solar+Lunar (24h + 24.84h)
   - Golden (24h + 38.8h φ ratio)

2. **Run duration** (continuous):
   - 7, 15, 30, 60 days

3. **Model type** (categorical, 2 levels):
   - Circadian-coupled
   - Circadian-disabled

### Dependent Variables
1. **Primary**: Total carbon fixation over simulation period (fitness)
2. **Secondary**: 
   - Convergence rate (iterations to 90% of final fitness)
   - Parameter values (photosystem, carbon, energy levels)
   - Trajectory autocorrelation
   - Parameter space exploration volume

### Control Variables
- Random seed (test 10 seeds per condition)
- Initial parameter bounds (same for all conditions)
- Timestep size (dt = 0.1 hours)
- Model parameters (Q10, kinetic constants, etc.)

### Sample Size
**Power analysis**:
- Expected effect size: d = 0.8 (large)
- Significance level: α = 0.05
- Power: 1-β = 0.80
- **Required n per group**: 26

**Practical**: Run 30 replicates per condition (provides buffer)

**Total simulations**: 4 conditions × 30 replicates = **120 optimization runs**

---

## Statistical Analysis Plan

### Primary Analysis
```python
from scipy import stats

# Compare solar+lunar vs static (main hypothesis)
t_stat, p_value = stats.ttest_ind(fitness_solar_lunar, 
                                   fitness_static,
                                   alternative='greater')

# Effect size
cohen_d = (np.mean(fitness_solar_lunar) - np.mean(fitness_static)) / \
          np.sqrt((np.std(fitness_solar_lunar)**2 + np.std(fitness_static)**2) / 2)

# Percent improvement
improvement = (np.mean(fitness_solar_lunar) - np.mean(fitness_static)) / \
              np.mean(fitness_static) * 100
```

**Decision rule**:
- **Reject H₀ if**: p < 0.05 AND improvement ≥ 15% AND Cohen's d ≥ 0.8
- **Support H₁ if**: All three criteria met
- **Inconclusive if**: p < 0.05 but improvement < 15%
- **Fail to reject H₀ if**: p ≥ 0.05

### Secondary Analyses
```python
# ANOVA across all four conditions
f_stat, p_anova = stats.f_oneway(fitness_static, fitness_solar,
                                  fitness_solar_lunar, fitness_golden)

# Post-hoc pairwise comparisons (Bonferroni corrected)
from statsmodels.stats.multicomp import pairwise_tukeyhsd
tukey = pairwise_tukeyhsd(all_fitness, all_conditions)

# Regression: Does run length affect improvement?
from scipy.stats import linregress
slope, intercept, r_value, p_value, std_err = \
    linregress(run_lengths, improvements)
```

### Visualization
```python
# Box plots with significance bars
import matplotlib.pyplot as plt
import seaborn as sns

fig, ax = plt.subplots(figsize=(10, 6))
sns.boxplot(data=results_df, x='condition', y='fitness', ax=ax)
sns.swarmplot(data=results_df, x='condition', y='fitness', 
              color='black', alpha=0.3, ax=ax)

# Add significance stars
def add_sig_bar(ax, x1, x2, y, p_value):
    stars = '***' if p < 0.001 else '**' if p < 0.01 else '*' if p < 0.05 else 'ns'
    ax.plot([x1, x2], [y, y], 'k-', linewidth=2)
    ax.text((x1+x2)/2, y+0.02, stars, ha='center', fontsize=12)

add_sig_bar(ax, 0, 2, max_fitness*1.1, p_value)
```

---

## Falsification Criteria

### Strong Falsification (Reject H₁ outright)
Any of:
1. **p ≥ 0.05**: No statistically significant difference
2. **Improvement < 5%**: Effect too small to matter
3. **Cohen's d < 0.3**: Negligible effect size
4. **Golden ratio performs equally well**: Not biologically specific

### Weak Falsification (Needs refinement)
Any of:
1. **5% ≤ improvement < 15%**: Marginal effect, not worth hardware investment
2. **High variance**: Inconsistent across seeds (σ/μ > 0.3)
3. **No beat period correlation**: 7-day and 30-day runs identical
4. **Circadian-disabled model shows same effect**: Not rhythm-dependent

### Confirmation (Support H₁)
All of:
1. **p < 0.05**: Statistically significant
2. **Improvement ≥ 15%**: Practically significant
3. **Cohen's d ≥ 0.8**: Large effect
4. **Solar+lunar > golden**: Biologically specific
5. **Mechanism identified**: Clear explanation why it works

---

## Expected Outcomes & Interpretations

### Outcome 1: Strong Confirmation
**Result**: 20-30% improvement, p < 0.001, biologically-specific

**Interpretation**: 
- Bio-temporal computing is a real phenomenon
- Hardware implementation justified
- Potential applications: field-deployed biosensors, synthetic biology optimization

**Next steps**: 
- Proceed to FPGA implementation (Month 2)
- Test on additional organisms
- Explore other biological timescales (seasonal, ultradian)

---

### Outcome 2: Weak Confirmation  
**Result**: 10-12% improvement, p < 0.05, but high variance

**Interpretation**:
- Effect exists but is context-dependent
- Needs refinement before hardware
- May require longer optimization runs or better models

**Next steps**:
- Identify sources of variance
- Test on more complex/realistic models
- Extend simulation duration to 60+ days

---

### Outcome 3: Negative Result
**Result**: <5% improvement, p > 0.05

**Interpretation**:
- Quasiperiodic forcing doesn't help this problem
- Possible reasons:
  - Timescales mismatch (need faster/slower periods)
  - Model too simplified (missing critical dynamics)
  - Optimization landscape too simple (no local minima)

**Next steps**:
- Publish negative result (equally valuable!)
- Try different biological system (e.g., circatidal organisms)
- Investigate alternative DTQC formulations

---

### Outcome 4: Surprising Result
**Result**: Golden ratio performs best, solar+lunar second

**Interpretation**:
- Mathematical quasiperiodicity matters more than biological realism
- Suggests generic decorrelation effect, not resonance
- Rethink biomimetic approach

**Next steps**:
- Focus on pure mathematical quasicrystal theory
- Test broader range of incommensurate ratios
- Decouple from biological interpretation

---

## Theoretical Framework

### Underlying Theory
This hypothesis synthesizes three theoretical frameworks:

1. **Discrete Time Quasicrystal (DTQC) Theory**
   - Quasiperiodic driving creates multi-timescale exploration
   - Incommensurate frequencies prevent periodic traps
   - Enables escape from local minima

2. **Chronobiology**
   - Circadian clocks are universal in biology
   - Evolution optimized for 24h solar cycles
   - Tidal organisms also evolved for 24.84h lunar cycles
   - Beat interference (29.5 days) drives monthly rhythms

3. **Optimization Theory**
   - Energy landscape navigation
   - Basin hopping via perturbations
   - Multi-scale search (exploitation vs exploration)

### Predicted Mechanism
```
Quasiperiodic Forcing (24h + 24.84h)
         ↓
Modulates Energy Landscape
         ↓
Creates Time-Varying Barriers
         ↓
Enables Escape from Local Minima
         ↓
Explores Biologically-Relevant Parameter Space
         ↓
Converges to Better Global Optima
```

**Critical assumption**: The biological system has evolved to respond optimally to these specific timescales, so computational optimization "piggybacks" on evolutionary optimization.

---

## Broader Implications

### If H₁ is Supported
1. **Computational**: New optimization algorithm for biological problems
2. **Theoretical**: Validates DTQC principles in practical setting
3. **Engineering**: Ultra-low-power bio-temporal computing architecture
4. **Scientific**: Connects chronobiology to computational theory

### If H₀ is Supported
1. **Computational**: Standard methods remain state-of-art
2. **Theoretical**: DTQC benefits may be context-specific
3. **Scientific**: Need better understanding of when quasiperiodicity helps

---

## Pre-Registration
To ensure scientific rigor, this hypothesis should be **pre-registered** before running experiments:

**Registry**: Open Science Framework (OSF) or AsPredicted.org

**Pre-registration includes**:
- Full hypothesis statements
- Experimental design
- Sample size justification
- Statistical analysis plan
- Decision rules for interpreting results

**Benefits**:
- Prevents p-hacking
- Increases credibility
- Enables confirmatory vs exploratory distinction
- Publishable regardless of outcome

---

## Timeline

| Week | Activity | Deliverable |
|------|----------|-------------|
| 0 | Pre-registration | OSF registration complete |
| 1 | Biological model implementation | Model validated against literature |
| 2 | DTQC forcing implementation | 120 optimization runs complete |
| 3 | Statistical analysis | Results with p-values, effect sizes |
| 4 | Interpretation & documentation | Accept/reject H₁ with justification |

---

## Success Criteria Summary

**Minimum viable success**:
- Clear accept/reject decision on H₁ (not "maybe")
- Statistically rigorous analysis (pre-registered)
- Mechanistic explanation (not just black box)
- Reproducible code (others can verify)

**Exceptional success**:
- Strong effect (>20% improvement)
- Novel mechanism discovered
- Multiple subsidiary hypotheses confirmed
- Clear path to practical applications

---

*This hypothesis is designed to be **falsifiable, testable, and conclusive** within 30 days of computational experiments. Whether H₁ is supported or rejected, the result advances scientific understanding.*