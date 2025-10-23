#!/usr/bin/env python3
"""
Statistical Tests for Bitstream Analysis
Implements randomness tests for stochastic computing validation.
"""

import numpy as np
from scipy import stats
import warnings
warnings.filterwarnings('ignore')


def chi_square_test(bitstream, num_bins=16):
    """
    Chi-square test for uniformity
    Tests if bitstream values are uniformly distributed
    """
    if len(bitstream) < num_bins:
        return 1.0  # Not enough data

    # Convert to binary if needed
    if bitstream.dtype != bool:
        bitstream = bitstream.astype(bool)

    # Count transitions between bins
    bin_counts = np.zeros(num_bins)
    step = len(bitstream) // num_bins

    for i in range(num_bins):
        start = i * step
        end = (i + 1) * step if i < num_bins - 1 else len(bitstream)
        bin_counts[i] = np.sum(bitstream[start:end])

    # Expected count per bin
    expected = len(bitstream) / num_bins

    # Chi-square statistic
    chi2 = np.sum((bin_counts - expected) ** 2 / expected)

    # p-value (simplified - for large samples, chi2 follows chi-square distribution)
    df = num_bins - 1
    p_value = 1 - stats.chi2.cdf(chi2, df)

    return p_value


def runs_test(bitstream):
    """
    Runs test for randomness
    Tests if runs of 0s and 1s are random
    """
    if len(bitstream) < 20:
        return 0.5  # Not enough data

    # Convert to binary
    bits = bitstream.astype(int)

    # Count runs (sequences of identical bits)
    runs = 1
    for i in range(1, len(bits)):
        if bits[i] != bits[i-1]:
            runs += 1

    # Expected runs for random sequence
    n0 = len(bits) - np.sum(bits)  # Number of 0s
    n1 = np.sum(bits)              # Number of 1s

    if n0 == 0 or n1 == 0:
        return 0.0  # All same bits

    expected_runs = 2 * n0 * n1 / (n0 + n1) + 1

    # Standard deviation
    var_runs = 2 * n0 * n1 * (2 * n0 * n1 - n0 - n1) / ((n0 + n1) ** 2 * (n0 + n1 - 1))
    std_runs = np.sqrt(var_runs)

    # Z-score
    if std_runs == 0:
        return 0.5

    z = (runs - expected_runs) / std_runs

    # Two-tailed p-value
    p_value = 2 * (1 - stats.norm.cdf(abs(z)))

    return p_value


def autocorrelation_test(bitstream, max_lag=100):
    """
    Autocorrelation test
    Measures linear dependence between bits at different lags
    """
    if len(bitstream) < max_lag * 2:
        return 0.0

    # Convert to ±1 for correlation
    bits = 2 * bitstream.astype(int) - 1

    # Compute autocorrelation
    autocorr = np.correlate(bits, bits, mode='full')
    autocorr = autocorr[autocorr.size // 2: autocorr.size // 2 + max_lag + 1]

    # Normalize
    autocorr = autocorr / autocorr[0]

    # Maximum absolute autocorrelation (excluding lag 0)
    max_autocorr = np.max(np.abs(autocorr[1:]))

    return max_autocorr


def serial_test(bitstream, m=2):
    """
    Serial test (overlapping m-bit patterns)
    Tests if overlapping m-bit sequences are uniformly distributed
    """
    if len(bitstream) < 2**m * 10:
        return 1.0  # Not enough data

    bits = bitstream.astype(int)

    # Count overlapping m-bit patterns
    pattern_counts = np.zeros(2**m)

    for i in range(len(bits) - m + 1):
        pattern = 0
        for j in range(m):
            pattern |= bits[i + j] << (m - 1 - j)
        pattern_counts[pattern] += 1

    # Expected count per pattern
    expected = (len(bits) - m + 1) / 2**m

    # Chi-square statistic
    chi2 = np.sum((pattern_counts - expected) ** 2 / expected)

    # p-value
    df = 2**m - 1
    p_value = 1 - stats.chi2.cdf(chi2, df)

    return p_value


def poker_test(bitstream, m=4):
    """
    Poker test (frequency of m-bit patterns)
    Tests if m-bit sequences appear with equal frequency
    """
    if len(bitstream) < 2**m * 5:
        return 1.0  # Not enough data

    bits = bitstream.astype(int)

    # Count non-overlapping m-bit patterns
    pattern_counts = np.zeros(2**m)
    num_patterns = len(bits) // m

    for i in range(num_patterns):
        pattern = 0
        for j in range(m):
            pattern |= bits[i*m + j] << (m - 1 - j)
        pattern_counts[pattern] += 1

    # Expected count per pattern
    expected = num_patterns / 2**m

    # Chi-square statistic
    chi2 = np.sum((pattern_counts - expected) ** 2 / expected)

    # p-value
    df = 2**m - 1
    p_value = 1 - stats.chi2.cdf(chi2, df)

    return p_value


def run_statistical_tests(bitstream):
    """
    Run comprehensive statistical tests on bitstream
    Returns dictionary with test results
    """
    results = {}

    # Chi-square test
    results['chi_square'] = chi_square_test(bitstream)

    # Runs test
    results['runs_test'] = runs_test(bitstream)

    # Autocorrelation test
    results['autocorr_max'] = autocorrelation_test(bitstream)

    # Serial test (m=2)
    results['serial_test'] = serial_test(bitstream, m=2)

    # Poker test (m=4)
    results['poker_test'] = poker_test(bitstream, m=4)

    # Overall randomness score (geometric mean of p-values)
    p_values = [results['chi_square'], results['runs_test'],
                results['serial_test'], results['poker_test']]

    # Handle p-values of 0 (very non-random)
    p_values = [max(p, 1e-10) for p in p_values]
    results['randomness_score'] = np.exp(np.mean(np.log(p_values)))

    # Pass/fail based on autocorrelation (most important for stochastic computing)
    results['autocorr_pass'] = results['autocorr_max'] < 0.1

    return results


def print_test_results(results):
    """Pretty print statistical test results"""
    print("Statistical Test Results:")
    print(".6f")
    print(".6f")
    print(".6f")
    print(".6f")
    print(".6f")
    print(".6f")
    print(f"  Autocorr Pass: {results['autocorr_pass']}")
    print(".3f")


if __name__ == "__main__":
    # Test with random data
    np.random.seed(42)
    test_bits = np.random.randint(0, 2, 10000)

    results = run_statistical_tests(test_bits)
    print_test_results(results)