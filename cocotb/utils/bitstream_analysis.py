#!/usr/bin/env python3
"""
Bitstream Analysis Utilities
Advanced analysis tools for stochastic computing bitstreams.
"""

import numpy as np
from scipy import signal, fft
import warnings
warnings.filterwarnings('ignore')


def compute_entropy(bitstream):
    """
    Compute Shannon entropy of bitstream
    Measures information content (ideal random = 1.0)
    """
    if len(bitstream) == 0:
        return 0.0

    # Convert to binary
    bits = bitstream.astype(int)

    # Count 0s and 1s
    n0 = len(bits) - np.sum(bits)
    n1 = np.sum(bits)

    if n0 == 0 or n1 == 0:
        return 0.0  # No entropy if all same bits

    # Probabilities
    p0 = n0 / len(bits)
    p1 = n1 / len(bits)

    # Shannon entropy
    entropy = - (p0 * np.log2(p0) + p1 * np.log2(p1))

    return entropy


def compute_complexity(bitstream):
    """
    Compute Lempel-Ziv complexity (compression ratio)
    Measures algorithmic complexity (0 = simple, 1 = complex)
    """
    if len(bitstream) < 10:
        return 0.0

    bits = bitstream.astype(int).tolist()

    # Lempel-Ziv complexity calculation
    complexity = 0
    i = 0

    while i < len(bits):
        # Find longest substring starting at i that matches previous substring
        max_len = 0
        for j in range(i):
            # Check for match starting at j
            match_len = 0
            while (i + match_len < len(bits) and
                   j + match_len < i and
                   bits[j + match_len] == bits[i + match_len]):
                match_len += 1

            max_len = max(max_len, match_len)

        if max_len > 0:
            i += max_len
        else:
            i += 1

        complexity += 1

    # Normalize by theoretical maximum
    max_complexity = len(bits) / np.log2(len(bits)) if len(bits) > 1 else 1
    normalized_complexity = complexity / max_complexity

    return min(normalized_complexity, 1.0)


def compute_balance(bitstream):
    """
    Compute balance ratio (ideal = 1.0 for equal 0s and 1s)
    """
    if len(bitstream) == 0:
        return 0.0

    bits = bitstream.astype(int)
    n1 = np.sum(bits)
    n0 = len(bits) - n1

    if n0 == 0 or n1 == 0:
        return 0.0

    balance = min(n0, n1) / max(n0, n1)
    return balance


def compute_correlation(seq1, seq2, max_lag=None):
    """
    Compute cross-correlation between two sequences
    """
    if len(seq1) != len(seq2):
        min_len = min(len(seq1), len(seq2))
        seq1 = seq1[:min_len]
        seq2 = seq2[:min_len]

    if len(seq1) < 10:
        return 0.0

    # Convert to ±1 for correlation
    s1 = 2 * seq1.astype(int) - 1
    s2 = 2 * seq2.astype(int) - 1

    if max_lag is None:
        max_lag = len(seq1) // 4

    # Compute cross-correlation
    corr = np.correlate(s1, s2, mode='full')
    corr = corr[corr.size // 2: corr.size // 2 + max_lag + 1]

    # Normalize
    corr = corr / (len(seq1) * np.std(s1) * np.std(s2))

    return corr[0]  # Zero lag correlation


def compute_autocorrelation(bitstream, max_lag=100):
    """
    Compute autocorrelation function
    """
    if len(bitstream) < max_lag * 2:
        return np.array([1.0])

    # Convert to ±1
    bits = 2 * bitstream.astype(int) - 1

    # Compute autocorrelation
    autocorr = np.correlate(bits, bits, mode='full')
    autocorr = autocorr[autocorr.size // 2: autocorr.size // 2 + max_lag + 1]

    # Normalize
    autocorr = autocorr / autocorr[0]

    return autocorr


def spectral_analysis(bitstream, fs=1.0):
    """
    Compute power spectral density
    Returns frequencies and power spectrum
    """
    if len(bitstream) < 100:
        return np.array([0]), np.array([0])

    # Convert to ±1
    bits = 2 * bitstream.astype(int) - 1

    # Compute PSD using Welch's method
    freqs, psd = signal.welch(bits, fs=fs, nperseg=min(1024, len(bits)//4))

    return freqs, psd


def compute_spectral_flatness(psd):
    """
    Compute spectral flatness (0 = tonal, 1 = white noise)
    """
    if len(psd) == 0 or np.sum(psd) == 0:
        return 0.0

    # Geometric mean / arithmetic mean
    geometric_mean = np.exp(np.mean(np.log(psd + 1e-10)))
    arithmetic_mean = np.mean(psd)

    if arithmetic_mean == 0:
        return 0.0

    flatness = geometric_mean / arithmetic_mean
    return flatness


def run_length_statistics(bitstream):
    """
    Compute run length statistics
    Returns dict with run length distribution
    """
    if len(bitstream) == 0:
        return {'mean_run_0': 0, 'mean_run_1': 0, 'max_run_0': 0, 'max_run_1': 0}

    bits = bitstream.astype(int)

    # Find runs
    runs_0 = []
    runs_1 = []

    current_run = 1
    current_bit = bits[0]

    for i in range(1, len(bits)):
        if bits[i] == current_bit:
            current_run += 1
        else:
            if current_bit == 0:
                runs_0.append(current_run)
            else:
                runs_1.append(current_run)
            current_run = 1
            current_bit = bits[i]

    # Add last run
    if current_bit == 0:
        runs_0.append(current_run)
    else:
        runs_1.append(current_run)

    stats = {
        'mean_run_0': np.mean(runs_0) if runs_0 else 0,
        'mean_run_1': np.mean(runs_1) if runs_1 else 0,
        'max_run_0': np.max(runs_0) if runs_0 else 0,
        'max_run_1': np.max(runs_1) if runs_1 else 0,
        'total_runs_0': len(runs_0),
        'total_runs_1': len(runs_1)
    }

    return stats


def analyze_bitstream(bitstream):
    """
    Comprehensive bitstream analysis
    Returns dictionary with all metrics
    """
    analysis = {}

    # Basic properties
    analysis['length'] = len(bitstream)
    analysis['entropy'] = compute_entropy(bitstream)
    analysis['complexity'] = compute_complexity(bitstream)
    analysis['balance'] = compute_balance(bitstream)

    # Spectral properties
    freqs, psd = spectral_analysis(bitstream)
    analysis['spectral_flatness'] = compute_spectral_flatness(psd)
    analysis['dominant_frequency'] = freqs[np.argmax(psd)] if len(freqs) > 0 else 0

    # Autocorrelation
    autocorr = compute_autocorrelation(bitstream, max_lag=50)
    analysis['autocorr_max'] = np.max(np.abs(autocorr[1:]))  # Exclude lag 0
    analysis['autocorr_decay'] = np.mean(np.abs(autocorr[1:10]))  # First 10 lags

    # Run length statistics
    run_stats = run_length_statistics(bitstream)
    analysis.update(run_stats)

    # Quality score (weighted combination of metrics)
    entropy_weight = 0.3
    balance_weight = 0.2
    complexity_weight = 0.2
    spectral_weight = 0.2
    autocorr_weight = 0.1

    quality_score = (
        entropy_weight * analysis['entropy'] +
        balance_weight * analysis['balance'] +
        complexity_weight * analysis['complexity'] +
        spectral_weight * analysis['spectral_flatness'] +
        autocorr_weight * (1 - analysis['autocorr_max'])  # Lower autocorr is better
    )

    analysis['quality_score'] = quality_score

    return analysis


def compare_bitstreams(stream1, stream2):
    """
    Compare two bitstreams
    Returns similarity metrics
    """
    comparison = {}

    # Basic correlations
    comparison['correlation'] = compute_correlation(stream1, stream2)
    comparison['mutual_info'] = compute_entropy(stream1) + compute_entropy(stream2) - compute_entropy(stream1 + stream2)

    # Spectral similarity
    _, psd1 = spectral_analysis(stream1)
    _, psd2 = spectral_analysis(stream2)

    if len(psd1) == len(psd2):
        comparison['spectral_similarity'] = np.corrcoef(psd1, psd2)[0, 1]
    else:
        comparison['spectral_similarity'] = 0.0

    # Run length similarity
    runs1 = run_length_statistics(stream1)
    runs2 = run_length_statistics(stream2)

    comparison['run_similarity'] = (
        1 - abs(runs1['mean_run_0'] - runs2['mean_run_0']) / max(runs1['mean_run_0'], runs2['mean_run_0'], 1) +
        1 - abs(runs1['mean_run_1'] - runs2['mean_run_1']) / max(runs1['mean_run_1'], runs2['mean_run_1'], 1)
    ) / 2

    return comparison


if __name__ == "__main__":
    # Test with different types of sequences
    np.random.seed(42)

    # Random sequence
    random_bits = np.random.randint(0, 2, 1000)
    random_analysis = analyze_bitstream(random_bits)
    print("Random sequence analysis:")
    for k, v in random_analysis.items():
        print(".3f")

    # Periodic sequence
    periodic_bits = np.tile([0, 1], 500)
    periodic_analysis = analyze_bitstream(periodic_bits)
    print("\nPeriodic sequence analysis:")
    for k, v in periodic_analysis.items():
        print(".3f")

    # Compare them
    comparison = compare_bitstreams(random_bits, periodic_bits)
    print("\nComparison:")
    for k, v in comparison.items():
        print(".3f")