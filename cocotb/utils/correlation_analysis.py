#!/usr/bin/env python3
"""
Correlation Analysis for QBG Hypothesis Testing
Specialized tools for analyzing quasiperiodic bitstream mixing.
"""

import numpy as np
from scipy import signal, stats
from .bitstream_analysis import compute_correlation, spectral_analysis, compute_spectral_flatness
import warnings
warnings.filterwarnings('ignore')


def analyze_correlation_reduction(stream_a, stream_b, mixed_output):
    """
    Analyze how well QBG mixing reduces correlation
    Core hypothesis validation function
    """
    results = {}

    # Cross-correlation between original streams
    orig_corr = compute_correlation(stream_a, stream_b)
    results['original_cross_corr'] = orig_corr

    # Cross-correlations with mixed output
    corr_a_mixed = compute_correlation(stream_a, mixed_output)
    corr_b_mixed = compute_correlation(stream_b, mixed_output)
    results['mixed_corr_a'] = corr_a_mixed
    results['mixed_corr_b'] = corr_b_mixed

    # Correlation reduction metrics
    reduction_a = 1 - abs(corr_a_mixed) / abs(orig_corr) if abs(orig_corr) > 0 else 1
    reduction_b = 1 - abs(corr_b_mixed) / abs(orig_corr) if abs(orig_corr) > 0 else 1
    results['cross_corr_reduction'] = (reduction_a + reduction_b) / 2

    # Autocorrelation analysis
    autocorr_mixed = np.correlate(mixed_output - 0.5, mixed_output - 0.5, mode='full')
    autocorr_mixed = autocorr_mixed[autocorr_mixed.size // 2:]
    autocorr_mixed = autocorr_mixed / np.max(np.abs(autocorr_mixed))

    # Compare with original streams' autocorrelations
    autocorr_a = np.correlate(stream_a - 0.5, stream_a - 0.5, mode='full')
    autocorr_a = autocorr_a[autocorr_a.size // 2:]
    autocorr_a = autocorr_a / np.max(np.abs(autocorr_a))

    autocorr_b = np.correlate(stream_b - 0.5, stream_b - 0.5, mode='full')
    autocorr_b = autocorr_b[autocorr_b.size // 2:]
    autocorr_b = autocorr_b / np.max(np.abs(autocorr_b))

    # Autocorrelation improvement (lower is better)
    max_autocorr_orig = max(np.max(np.abs(autocorr_a[1:100])), np.max(np.abs(autocorr_b[1:100])))
    max_autocorr_mixed = np.max(np.abs(autocorr_mixed[1:100]))

    if max_autocorr_orig > 0:
        results['autocorr_improvement'] = 1 - max_autocorr_mixed / max_autocorr_orig
    else:
        results['autocorr_improvement'] = 1.0

    # Spectral analysis
    _, psd_mixed = spectral_analysis(mixed_output)
    results['spectral_flatness'] = compute_spectral_flatness(psd_mixed)

    # Quasiperiodic signature analysis
    results.update(analyze_quasiperiodic_signature(stream_a, stream_b, mixed_output))

    # Hypothesis validation
    results['hypothesis_supported'] = (
        results['cross_corr_reduction'] > 0.5 and  # Significant correlation reduction
        results['autocorr_improvement'] > 0.3 and   # Autocorrelation improvement
        results['spectral_flatness'] > 0.7          # Good spectral properties
    )

    return results


def analyze_quasiperiodic_signature(stream_a, stream_b, mixed_output):
    """
    Analyze quasiperiodic mixing signatures
    Looks for evidence of incommensurate period mixing
    """
    results = {}

    # Period analysis
    period_a = find_dominant_period(stream_a)
    period_b = find_dominant_period(stream_b)
    period_mixed = find_dominant_period(mixed_output)

    results['period_a'] = period_a
    results['period_b'] = period_b
    results['period_mixed'] = period_mixed

    # Quasiperiodic ratio (should be irrational or large)
    if period_a > 0 and period_b > 0:
        ratio_ab = period_b / period_a
        results['period_ratio'] = ratio_ab

        # Check if ratio is "quasiperiodic" (not too close to rational)
        # Find closest rational approximation
        best_rational = find_closest_rational(ratio_ab, max_denom=20)
        results['rational_approximation'] = best_rational
        results['quasiperiodic_measure'] = abs(ratio_ab - best_rational[0]/best_rational[1])
    else:
        results['period_ratio'] = 0
        results['quasiperiodic_measure'] = 0

    # Mixing efficiency (how well periods are combined)
    if period_mixed > 0:
        lcm_estimate = period_a * period_b / gcd_estimate(period_a, period_b)
        results['lcm_estimate'] = lcm_estimate
        results['mixing_efficiency'] = min(period_mixed / lcm_estimate, lcm_estimate / period_mixed)
    else:
        results['lcm_estimate'] = 0
        results['mixing_efficiency'] = 0

    return results


def find_dominant_period(bitstream):
    """
    Find dominant period using autocorrelation
    """
    if len(bitstream) < 50:
        return 0

    # Compute autocorrelation
    autocorr = np.correlate(bitstream - 0.5, bitstream - 0.5, mode='full')
    autocorr = autocorr[autocorr.size // 2:]

    # Find peaks
    peaks = []
    for i in range(10, len(autocorr)//2):  # Start from lag 10
        if (autocorr[i] > autocorr[i-1] and autocorr[i] > autocorr[i+1] and
            autocorr[i] > 0.3):  # Significant peak
            peaks.append((i, autocorr[i]))

    if not peaks:
        return 0

    # Return period of strongest peak
    best_peak = max(peaks, key=lambda x: x[1])
    return best_peak[0]


def find_closest_rational(ratio, max_denom=20):
    """
    Find closest rational approximation to a real number
    Uses Farey sequence approach
    """
    best_num, best_denom = 1, 1
    best_error = abs(ratio - 1)

    for denom in range(1, max_denom + 1):
        for num in range(1, denom + 1):
            error = abs(ratio - num / denom)
            if error < best_error:
                best_error = error
                best_num, best_denom = num, denom

    return (best_num, best_denom)


def gcd_estimate(a, b):
    """Estimate GCD for floating point periods"""
    a, b = abs(a), abs(b)
    while b > 1:
        a, b = b, a % b
    return a


def analyze_mixing_modes(stream_a, stream_b, mixed_outputs):
    """
    Compare different mixing modes (XOR, AND, OR, etc.)
    """
    results = {}

    for mode, mixed in mixed_outputs.items():
        results[mode] = analyze_correlation_reduction(stream_a, stream_b, mixed)

    # Rank modes by effectiveness
    ranking = sorted(results.keys(),
                    key=lambda m: results[m]['cross_corr_reduction'],
                    reverse=True)
    results['ranking'] = ranking
    results['best_mode'] = ranking[0]

    return results


def statistical_significance_test(original_corr, mixed_corrs, alpha=0.05):
    """
    Test if correlation reduction is statistically significant
    """
    # t-test: is mixed correlation significantly different from original?
    t_stat, p_value = stats.ttest_1samp(mixed_corrs, original_corr)

    return {
        't_statistic': t_stat,
        'p_value': p_value,
        'significant': p_value < alpha,
        'effect_size': abs(np.mean(mixed_corrs) - original_corr) / np.std(mixed_corrs)
    }


def generate_correlation_report(results, save_path=None):
    """
    Generate detailed correlation analysis report
    """
    report = []
    report.append("# QBG Correlation Analysis Report")
    report.append("")

    report.append("## Core Hypothesis Results")
    report.append(f"- Cross-correlation reduction: {results['cross_corr_reduction']:.3f}")
    report.append(f"- Autocorrelation improvement: {results['autocorr_improvement']:.3f}")
    report.append(f"- Spectral flatness: {results['spectral_flatness']:.3f}")
    report.append(f"- Hypothesis supported: {results['hypothesis_supported']}")
    report.append("")

    report.append("## Detailed Metrics")
    report.append(f"- Original cross-correlation: {results['original_cross_corr']:.6f}")
    report.append(f"- Mixed vs A correlation: {results['mixed_corr_a']:.6f}")
    report.append(f"- Mixed vs B correlation: {results['mixed_corr_b']:.6f}")
    report.append("")

    if 'period_a' in results:
        report.append("## Quasiperiodic Analysis")
        report.append(f"- Period A: {results['period_a']}")
        report.append(f"- Period B: {results['period_b']}")
        report.append(f"- Period ratio: {results['period_ratio']:.3f}")
        report.append(f"- Quasiperiodic measure: {results['quasiperiodic_measure']:.6f}")
        report.append(f"- Mixing efficiency: {results['mixing_efficiency']:.3f}")
        report.append("")

    # Success criteria
    success_criteria = {
        'Correlation reduction > 50%': results['cross_corr_reduction'] > 0.5,
        'Autocorrelation improvement > 30%': results['autocorr_improvement'] > 0.3,
        'Spectral flatness > 70%': results['spectral_flatness'] > 0.7,
        'Quasiperiodic mixing effective': results.get('mixing_efficiency', 0) > 0.8
    }

    report.append("## Success Criteria")
    for criterion, passed in success_criteria.items():
        status = "✓" if passed else "✗"
        report.append(f"- {status} {criterion}")
    report.append("")

    report.append("## Conclusion")
    passed_count = sum(success_criteria.values())
    total_count = len(success_criteria)

    if passed_count == total_count:
        report.append("🎉 All criteria met! QBG hypothesis strongly supported.")
    elif passed_count >= total_count * 0.75:
        report.append("✅ Most criteria met. QBG hypothesis supported with minor caveats.")
    elif passed_count >= total_count * 0.5:
        report.append("⚠️ Mixed results. Further investigation needed.")
    else:
        report.append("❌ Hypothesis not supported. Alternative approaches recommended.")

    report_str = "\n".join(report)

    if save_path:
        with open(save_path, 'w') as f:
            f.write(report_str)

    return report_str


if __name__ == "__main__":
    # Test with synthetic data
    np.random.seed(42)

    # Create two correlated streams
    base = np.random.randint(0, 2, 1000)
    noise1 = np.random.randint(0, 2, 1000)
    noise2 = np.random.randint(0, 2, 1000)

    stream_a = (base + noise1) % 2
    stream_b = (base + noise2) % 2
    mixed = (stream_a + stream_b) % 2  # Simple XOR-like mixing

    results = analyze_correlation_reduction(stream_a, stream_b, mixed)
    print("Correlation Analysis Results:")
    for k, v in results.items():
        if isinstance(v, float):
            print(".3f")
        else:
            print(f"  {k}: {v}")

    print("\nReport:")
    print(generate_correlation_report(results))