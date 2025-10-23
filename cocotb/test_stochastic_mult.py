#!/usr/bin/env python3
"""
Cocotb Testbench for Stochastic Multiplication
Tests practical performance of QBG in stochastic computing applications.
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import numpy as np
from utils.statistical_tests import run_statistical_tests
from utils.bitstream_analysis import analyze_bitstream
from utils.correlation_analysis import analyze_correlation_reduction


@cocotb.test()
async def test_stochastic_multiplication_accuracy(dut):
    """Test stochastic multiplication accuracy with QBG vs baseline"""
    cocotb.log.info("Testing stochastic multiplication accuracy")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Test different input probabilities
    test_probs = [0.1, 0.25, 0.5, 0.75, 0.9]

    results_qbg = []
    results_baseline = []

    for p_a in test_probs:
        for p_b in test_probs:
            cocotb.log.info(f"Testing p_a={p_a}, p_b={p_b}")

            # Set input probabilities (assuming dut has probability inputs)
            # This would need to be adapted based on actual Verilog interface
            dut.prob_a.value = int(p_a * 255)  # Assuming 8-bit probability
            dut.prob_b.value = int(p_b * 255)

            # Collect multiplication results
            products_qbg = []
            products_baseline = []

            # Collect enough samples for accurate statistics
            num_samples = 10000

            for _ in range(num_samples):
                await RisingEdge(dut.clk)
                products_qbg.append(int(dut.product_qbg.value))
                products_baseline.append(int(dut.product_baseline.value))

            # Calculate actual probabilities
            p_qbg = np.mean(products_qbg)
            p_baseline = np.mean(products_baseline)

            # Expected probability (p_a * p_b)
            expected = p_a * p_b

            # Calculate errors
            error_qbg = abs(p_qbg - expected)
            error_baseline = abs(p_baseline - expected)

            results_qbg.append({
                'p_a': p_a, 'p_b': p_b, 'expected': expected,
                'measured': p_qbg, 'error': error_qbg
            })

            results_baseline.append({
                'p_a': p_a, 'p_b': p_b, 'expected': expected,
                'measured': p_baseline, 'error': error_baseline
            })

            cocotb.log.info(".6f")
            cocotb.log.info(".6f")

    # Analyze overall accuracy
    errors_qbg = [r['error'] for r in results_qbg]
    errors_baseline = [r['error'] for r in results_baseline]

    mean_error_qbg = np.mean(errors_qbg)
    mean_error_baseline = np.mean(errors_baseline)

    cocotb.log.info(".6f")
    cocotb.log.info(".6f")

    # QBG should be more accurate
    assert mean_error_qbg < mean_error_baseline, "QBG multiplication not more accurate than baseline"

    # Save results
    np.savez('results/multiplication_accuracy.npz',
             results_qbg=results_qbg, results_baseline=results_baseline)


@cocotb.test()
async def test_multiplication_correlation_effects(dut):
    """Test how correlation affects multiplication accuracy"""
    cocotb.log.info("Testing correlation effects on multiplication")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Test with different correlation levels
    correlations = [0.0, 0.3, 0.6, 0.9]

    results = []

    for corr_target in correlations:
        cocotb.log.info(f"Testing correlation level: {corr_target}")

        # Generate correlated inputs
        # This would need actual implementation based on Verilog interface
        dut.correlation_level.value = int(corr_target * 255)

        # Collect results
        products_qbg = []
        products_baseline = []
        correlations_measured = []

        num_samples = 5000

        for _ in range(num_samples):
            await RisingEdge(dut.clk)
            products_qbg.append(int(dut.product_qbg.value))
            products_baseline.append(int(dut.product_baseline.value))

            # Measure actual correlation between inputs
            # This assumes we can access the input bitstreams
            if hasattr(dut, 'stream_a') and hasattr(dut, 'stream_b'):
                corr = np.corrcoef([int(dut.stream_a.value), int(dut.stream_b.value)])[0,1]
                correlations_measured.append(corr)

        # Analyze accuracy vs correlation
        error_qbg = abs(np.mean(products_qbg) - 0.25)  # Assuming p_a=p_b=0.5
        error_baseline = abs(np.mean(products_baseline) - 0.25)

        results.append({
            'target_corr': corr_target,
            'measured_corr': np.mean(correlations_measured) if correlations_measured else 0,
            'error_qbg': error_qbg,
            'error_baseline': error_baseline,
            'improvement': error_baseline - error_qbg
        })

        cocotb.log.info(".6f")

    # QBG should show better performance at higher correlations
    high_corr_results = [r for r in results if r['target_corr'] > 0.5]
    if high_corr_results:
        avg_improvement = np.mean([r['improvement'] for r in high_corr_results])
        cocotb.log.info(".6f")
        assert avg_improvement > 0, "QBG does not improve multiplication at high correlations"


@cocotb.test()
async def test_multiplication_scalability(dut):
    """Test multiplication accuracy vs bitstream length"""
    cocotb.log.info("Testing multiplication scalability")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Test different bitstream lengths
    lengths = [1000, 5000, 10000, 50000]

    results = []

    for length in lengths:
        cocotb.log.info(f"Testing length: {length}")

        products_qbg = []
        products_baseline = []

        for _ in range(length):
            await RisingEdge(dut.clk)
            products_qbg.append(int(dut.product_qbg.value))
            products_baseline.append(int(dut.product_baseline.value))

        # Calculate accuracy
        p_qbg = np.mean(products_qbg)
        p_baseline = np.mean(products_baseline)
        expected = 0.25  # Assuming p_a=p_b=0.5

        error_qbg = abs(p_qbg - expected)
        error_baseline = abs(p_baseline - expected)

        results.append({
            'length': length,
            'error_qbg': error_qbg,
            'error_baseline': error_baseline,
            'improvement': error_baseline - error_qbg
        })

        cocotb.log.info(".6f")

    # Check that accuracy improves with length (1/sqrt(N) convergence)
    errors_qbg = [r['error_qbg'] for r in results]
    lengths_arr = np.array(lengths)

    # Should follow 1/sqrt(N) relationship
    theoretical_errors = 1 / np.sqrt(lengths_arr)
    theoretical_errors = theoretical_errors / theoretical_errors[0] * errors_qbg[0]

    # Check correlation with theoretical prediction
    correlation = np.corrcoef(errors_qbg, theoretical_errors)[0, 1]
    cocotb.log.info(".3f")

    assert correlation > 0.8, "Accuracy does not scale as expected with bitstream length"


@cocotb.test()
async def test_multiplication_bitstream_quality(dut):
    """Test bitstream quality in multiplication context"""
    cocotb.log.info("Testing bitstream quality in multiplication")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Collect bitstreams during multiplication
    stream_a = []
    stream_b = []
    product_qbg = []
    product_baseline = []

    num_samples = 10000

    for _ in range(num_samples):
        await RisingEdge(dut.clk)
        stream_a.append(int(dut.stream_a.value))
        stream_b.append(int(dut.stream_b.value))
        product_qbg.append(int(dut.product_qbg.value))
        product_baseline.append(int(dut.product_baseline.value))

    # Analyze bitstream quality
    analysis_a = analyze_bitstream(np.array(stream_a))
    analysis_b = analyze_bitstream(np.array(stream_b))
    analysis_qbg = analyze_bitstream(np.array(product_qbg))
    analysis_baseline = analyze_bitstream(np.array(product_baseline))

    cocotb.log.info("Input Stream A Quality:")
    cocotb.log.info(".3f")
    cocotb.log.info(".3f")

    cocotb.log.info("Input Stream B Quality:")
    cocotb.log.info(".3f")
    cocotb.log.info(".3f")

    cocotb.log.info("QBG Product Quality:")
    cocotb.log.info(".3f")
    cocotb.log.info(".3f")

    cocotb.log.info("Baseline Product Quality:")
    cocotb.log.info(".3f")
    cocotb.log.info(".3f")

    # QBG should produce higher quality output
    assert analysis_qbg['quality_score'] > analysis_baseline['quality_score'], \
        "QBG does not produce higher quality multiplication bitstreams"

    # Correlation analysis
    corr_results = analyze_correlation_reduction(
        np.array(stream_a), np.array(stream_b), np.array(product_qbg)
    )

    cocotb.log.info("Correlation Analysis:")
    cocotb.log.info(".3f")
    cocotb.log.info(f"  Hypothesis supported: {corr_results['hypothesis_supported']}")


@cocotb.test()
async def test_multiplication_edge_cases(dut):
    """Test multiplication with edge case inputs"""
    cocotb.log.info("Testing multiplication edge cases")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Test edge cases
    edge_cases = [
        (0.0, 0.0),  # 0 * 0 = 0
        (1.0, 0.0),  # 1 * 0 = 0
        (0.0, 1.0),  # 0 * 1 = 0
        (1.0, 1.0),  # 1 * 1 = 1
        (0.5, 0.5),  # 0.5 * 0.5 = 0.25
    ]

    for p_a, p_b in edge_cases:
        cocotb.log.info(f"Testing edge case: {p_a} * {p_b}")

        # Set inputs
        dut.prob_a.value = int(p_a * 255)
        dut.prob_b.value = int(p_b * 255)

        # Collect results
        products_qbg = []
        products_baseline = []

        num_samples = 5000

        for _ in range(num_samples):
            await RisingEdge(dut.clk)
            products_qbg.append(int(dut.product_qbg.value))
            products_baseline.append(int(dut.product_baseline.value))

        # Check results
        p_qbg = np.mean(products_qbg)
        p_baseline = np.mean(products_baseline)
        expected = p_a * p_b

        error_qbg = abs(p_qbg - expected)
        error_baseline = abs(p_baseline - expected)

        cocotb.log.info(".6f")

        # For edge cases, both should be reasonably accurate
        assert error_qbg < 0.05, f"QBG error too high for {p_a}*{p_b}: {error_qbg}"
        assert error_baseline < 0.05, f"Baseline error too high for {p_a}*{p_b}: {error_baseline}"