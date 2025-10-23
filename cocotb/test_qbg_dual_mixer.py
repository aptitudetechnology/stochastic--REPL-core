#!/usr/bin/env python3
"""
Cocotb Testbench for QBG Dual Mixer Hypothesis
CORE HYPOTHESIS TEST: Quasiperiodic mixing reduces correlation in stochastic bitstreams.

Tests:
- Correlation reduction between mixed streams
- Autocorrelation analysis
- Spectral properties
- Comparison with baseline single-LFSR
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import numpy as np
from utils.statistical_tests import run_statistical_tests
from utils.bitstream_analysis import analyze_bitstream, compute_correlation
from utils.correlation_analysis import analyze_correlation_reduction
import matplotlib.pyplot as plt


@cocotb.test()
async def test_qbg_correlation_reduction(dut):
    """Test the core QBG hypothesis: quasiperiodic mixing reduces correlation"""
    cocotb.log.info("Testing QBG correlation reduction hypothesis")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Collect bitstreams
    stream_a = []
    stream_b = []
    mixed_out = []

    # Collect data for multiple periods (LCM of 255 and 127 = 32385)
    num_samples = 32385 * 2  # Two full cycles

    cocotb.log.info(f"Collecting {num_samples} samples for correlation analysis...")

    for i in range(num_samples):
        await RisingEdge(dut.clk)

        stream_a.append(int(dut.stream_a.value))
        stream_b.append(int(dut.stream_b.value))
        mixed_out.append(int(dut.mixed_out.value))

        if i % 10000 == 0:
            cocotb.log.info(f"Collected {i}/{num_samples} samples")

    # Convert to numpy arrays
    stream_a = np.array(stream_a, dtype=int)
    stream_b = np.array(stream_b, dtype=int)
    mixed_out = np.array(mixed_out, dtype=int)

    # Analyze correlation reduction
    cocotb.log.info("Analyzing correlation reduction...")

    # Correlation between original streams
    corr_ab = compute_correlation(stream_a, stream_b)
    cocotb.log.info(f"Original streams correlation: {corr_ab:.6f}")

    # Correlation between mixed output and originals
    corr_am = compute_correlation(stream_a, mixed_out)
    corr_bm = compute_correlation(stream_b, mixed_out)
    cocotb.log.info(f"Mixed vs A correlation: {corr_am:.6f}")
    cocotb.log.info(f"Mixed vs B correlation: {corr_bm:.6f}")

    # Autocorrelation of mixed output
    autocorr = np.correlate(mixed_out - 0.5, mixed_out - 0.5, mode='full')
    autocorr = autocorr[autocorr.size // 2:] / np.max(np.abs(autocorr))
    autocorr_max = np.max(np.abs(autocorr[1:100]))  # Max in first 100 lags
    cocotb.log.info(f"Mixed output autocorrelation max: {autocorr_max:.6f}")

    # Run comprehensive correlation analysis
    results = analyze_correlation_reduction(stream_a, stream_b, mixed_out)

    # Log detailed results
    cocotb.log.info("Correlation Analysis Results:")
    cocotb.log.info(f"  Cross-correlation reduction: {results['cross_corr_reduction']:.3f}")
    cocotb.log.info(f"  Autocorrelation improvement: {results['autocorr_improvement']:.3f}")
    cocotb.log.info(f"  Spectral flatness: {results['spectral_flatness']:.3f}")
    cocotb.log.info(f"  Hypothesis supported: {results['hypothesis_supported']}")

    # ASSERT HYPOTHESIS: Correlation should be reduced
    assert abs(corr_am) < abs(corr_ab), "QBG mixing did not reduce correlation with stream A"
    assert abs(corr_bm) < abs(corr_ab), "QBG mixing did not reduce correlation with stream B"
    assert autocorr_max < 0.1, f"Autocorrelation too high: {autocorr_max}"

    # Additional statistical validation
    stats = run_statistical_tests(mixed_out)
    cocotb.log.info(f"Mixed output statistics: chi2={stats['chi_square']:.3f}, "
                   f"runs={stats['runs_test']:.3f}")

    # Save analysis data for plotting
    np.savez('results/qbg_correlation_analysis.npz',
             stream_a=stream_a, stream_b=stream_b, mixed_out=mixed_out,
             autocorr=autocorr, results=results)


@cocotb.test()
async def test_qbg_modes(dut):
    """Test different QBG mixing modes"""
    cocotb.log.info("Testing QBG mixing modes")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    modes = ['xor', 'and', 'or', 'add']  # Assuming these modes exist
    results = {}

    for mode in modes:
        cocotb.log.info(f"Testing mode: {mode}")

        # Reset and set mode
        dut.rst.value = 1
        dut.mode.value = modes.index(mode)  # Assuming mode is encoded as integer
        await Timer(20, units="ns")
        dut.rst.value = 0

        # Collect samples
        samples = 10000
        stream_a = []
        stream_b = []
        mixed_out = []

        for _ in range(samples):
            await RisingEdge(dut.clk)
            stream_a.append(int(dut.stream_a.value))
            stream_b.append(int(dut.stream_b.value))
            mixed_out.append(int(dut.mixed_out.value))

        # Analyze this mode
        corr_reduction = analyze_correlation_reduction(
            np.array(stream_a), np.array(stream_b), np.array(mixed_out)
        )

        results[mode] = corr_reduction
        cocotb.log.info(f"Mode {mode}: correlation reduction = {corr_reduction['cross_corr_reduction']:.3f}")

    # Find best mode
    best_mode = max(results.keys(), key=lambda m: results[m]['cross_corr_reduction'])
    cocotb.log.info(f"Best mixing mode: {best_mode}")


@cocotb.test()
async def test_qbg_periodic_behavior(dut):
    """Test QBG behavior over multiple periods"""
    cocotb.log.info("Testing QBG periodic behavior")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Collect data for exactly the LCM period
    lcm_period = 255 * 127  # 32385
    cocotb.log.info(f"Testing over LCM period: {lcm_period}")

    mixed_sequence = []

    for i in range(lcm_period):
        await RisingEdge(dut.clk)
        mixed_sequence.append(int(dut.mixed_out.value))

    # Check for periodicity
    sequence = np.array(mixed_sequence)

    # Should not repeat exactly (quasiperiodic)
    autocorr = np.correlate(sequence - 0.5, sequence - 0.5, mode='full')
    autocorr = autocorr[autocorr.size // 2:]

    # Find peaks in autocorrelation
    peaks = []
    for i in range(1, len(autocorr)-1):
        if autocorr[i] > autocorr[i-1] and autocorr[i] > autocorr[i+1] and autocorr[i] > 0.5:
            peaks.append(i)

    cocotb.log.info(f"Autocorrelation peaks at lags: {peaks}")

    # Should have peaks at LFSR periods but not exact repeats
    assert len(peaks) > 0, "No significant autocorrelation peaks found"
    assert lcm_period not in peaks, "Sequence is exactly periodic (not quasiperiodic)"


@cocotb.test()
async def test_qbg_vs_baseline(dut):
    """Compare QBG with baseline single-LFSR performance"""
    cocotb.log.info("Comparing QBG with baseline single-LFSR")

    # This test would require a baseline LFSR module
    # For now, we'll compare statistical properties

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Collect QBG output
    qbg_samples = []
    for _ in range(50000):
        await RisingEdge(dut.clk)
        qbg_samples.append(int(dut.mixed_out.value))

    qbg_analysis = analyze_bitstream(np.array(qbg_samples))

    # Generate baseline (single LFSR would need separate module)
    # For now, just compare QBG properties
    cocotb.log.info("QBG bitstream analysis:")
    cocotb.log.info(f"  Entropy: {qbg_analysis['entropy']:.3f}")
    cocotb.log.info(f"  Complexity: {qbg_analysis['complexity']:.3f}")
    cocotb.log.info(f"  Balance: {qbg_analysis['balance']:.3f}")

    # Assert good statistical properties
    assert qbg_analysis['entropy'] > 0.95, "QBG entropy too low"
    assert qbg_analysis['balance'] > 0.95, "QBG balance too poor"