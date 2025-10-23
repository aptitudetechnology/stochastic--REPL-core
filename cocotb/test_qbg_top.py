#!/usr/bin/env python3
"""
Cocotb Testbench for QBG Top-Level Module
Integration tests for the complete QBG system.
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import numpy as np
from utils.statistical_tests import run_statistical_tests
from utils.bitstream_analysis import analyze_bitstream
from utils.correlation_analysis import analyze_correlation_reduction


@cocotb.test()
async def test_qbg_top_integration(dut):
    """Test complete QBG system integration"""
    cocotb.log.info("Testing QBG top-level integration")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Test different modes
    modes = ['qbg', 'baseline', 'comparison']

    results = {}

    for mode in modes:
        cocotb.log.info(f"Testing mode: {mode}")

        # Set mode
        mode_value = modes.index(mode)
        dut.mode.value = mode_value

        # Collect outputs
        outputs = []
        num_samples = 10000

        for _ in range(num_samples):
            await RisingEdge(dut.clk)
            outputs.append(int(dut.output.value))

        # Analyze outputs
        analysis = analyze_bitstream(np.array(outputs))
        stats = run_statistical_tests(np.array(outputs))

        results[mode] = {
            'analysis': analysis,
            'stats': stats,
            'outputs': outputs
        }

        cocotb.log.info(f"Mode {mode} results:")
        cocotb.log.info(".3f")
        cocotb.log.info(".3f")

    # Compare QBG vs baseline
    qbg_quality = results['qbg']['analysis']['quality_score']
    baseline_quality = results['baseline']['analysis']['quality_score']

    cocotb.log.info(".3f")

    assert qbg_quality > baseline_quality, "QBG does not outperform baseline"


@cocotb.test()
async def test_qbg_top_configuration(dut):
    """Test top-level configuration options"""
    cocotb.log.info("Testing QBG top-level configuration")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Test different configurations
    configs = [
        {'lfsr_a_period': 255, 'lfsr_b_period': 127, 'mixing_mode': 'xor'},
        {'lfsr_a_period': 511, 'lfsr_b_period': 255, 'mixing_mode': 'and'},
        {'lfsr_a_period': 127, 'lfsr_b_period': 511, 'mixing_mode': 'or'},
    ]

    for config in configs:
        cocotb.log.info(f"Testing config: {config}")

        # Set configuration (assuming dut has these inputs)
        if hasattr(dut, 'lfsr_a_period'):
            dut.lfsr_a_period.value = config['lfsr_a_period']
        if hasattr(dut, 'lfsr_b_period'):
            dut.lfsr_b_period.value = config['lfsr_b_period']
        if hasattr(dut, 'mixing_mode'):
            mixing_modes = ['xor', 'and', 'or', 'add']
            dut.mixing_mode.value = mixing_modes.index(config['mixing_mode'])

        # Allow configuration to settle
        await Timer(50, units="ns")

        # Collect samples
        outputs = []
        for _ in range(5000):
            await RisingEdge(dut.clk)
            outputs.append(int(dut.output.value))

        # Basic validation
        analysis = analyze_bitstream(np.array(outputs))
        assert analysis['entropy'] > 0.8, f"Poor entropy for config {config}"
        assert analysis['balance'] > 0.8, f"Poor balance for config {config}"

        cocotb.log.info(f"Config {config} validated")


@cocotb.test()
async def test_qbg_top_performance(dut):
    """Test QBG system performance metrics"""
    cocotb.log.info("Testing QBG system performance")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Measure throughput
    start_time = cocotb.utils.get_sim_time(units='ns')

    num_samples = 100000
    outputs = []

    for i in range(num_samples):
        await RisingEdge(dut.clk)
        outputs.append(int(dut.output.value))

        if i % 10000 == 0:
            cocotb.log.info(f"Collected {i}/{num_samples} samples")

    end_time = cocotb.utils.get_sim_time(units='ns')
    simulation_time = end_time - start_time

    throughput = num_samples / (simulation_time / 1e9)  # samples per second
    cocotb.log.info(".2e")

    # Analyze final output quality
    analysis = analyze_bitstream(np.array(outputs))
    stats = run_statistical_tests(np.array(outputs))

    cocotb.log.info("Final performance metrics:")
    cocotb.log.info(".3f")
    cocotb.log.info(".3f")
    cocotb.log.info(".3f")

    # Performance assertions
    assert analysis['entropy'] > 0.9, "Entropy too low for high-throughput operation"
    assert stats['autocorr_max'] < 0.05, "Autocorrelation too high"
    assert throughput > 1e6, "Throughput too low for practical use"


@cocotb.test()
async def test_qbg_top_reproducibility(dut):
    """Test reproducibility of QBG outputs with same seeds"""
    cocotb.log.info("Testing QBG reproducibility")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Test multiple runs with same seed
    seed = 42
    num_runs = 3
    run_outputs = []

    for run in range(num_runs):
        cocotb.log.info(f"Run {run + 1}/{num_runs}")

        # Reset and set seed
        dut.rst.value = 1
        dut.seed.value = seed
        await Timer(20, units="ns")
        dut.rst.value = 0

        # Collect outputs
        outputs = []
        for _ in range(1000):
            await RisingEdge(dut.clk)
            outputs.append(int(dut.output.value))

        run_outputs.append(outputs)

    # Check reproducibility
    for i in range(1, num_runs):
        matches = sum(a == b for a, b in zip(run_outputs[0], run_outputs[i]))
        match_rate = matches / len(run_outputs[0])

        cocotb.log.info(".3f")
        assert match_rate > 0.99, f"Run {i+1} not reproducible: {match_rate} match rate"

    cocotb.log.info("Reproducibility test passed")


@cocotb.test()
async def test_qbg_top_error_handling(dut):
    """Test error handling and edge cases"""
    cocotb.log.info("Testing QBG error handling")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Test invalid configurations
    invalid_configs = [
        {'lfsr_a_period': 0},      # Invalid period
        {'lfsr_b_period': -1},     # Negative period
        {'mixing_mode': 999},      # Invalid mode
    ]

    for config in invalid_configs:
        cocotb.log.info(f"Testing invalid config: {config}")

        # Set invalid config
        if 'lfsr_a_period' in config and hasattr(dut, 'lfsr_a_period'):
            dut.lfsr_a_period.value = config['lfsr_a_period']
        if 'lfsr_b_period' in config and hasattr(dut, 'lfsr_b_period'):
            dut.lfsr_b_period.value = config['lfsr_b_period']
        if 'mixing_mode' in config and hasattr(dut, 'mixing_mode'):
            dut.mixing_mode.value = config['mixing_mode']

        # System should handle gracefully (not crash)
        await Timer(100, units="ns")

        # Check that outputs are still generated
        outputs = []
        for _ in range(100):
            await RisingEdge(dut.clk)
            outputs.append(int(dut.output.value))

        # Should still produce valid outputs
        unique_outputs = len(set(outputs))
        assert unique_outputs > 1, f"No variation in output for invalid config {config}"

        cocotb.log.info(f"Invalid config {config} handled gracefully")

    # Test reset during operation
    cocotb.log.info("Testing reset during operation")

    # Run for a bit
    for _ in range(500):
        await RisingEdge(dut.clk)

    # Reset mid-operation
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Should recover
    outputs_after_reset = []
    for _ in range(100):
        await RisingEdge(dut.clk)
        outputs_after_reset.append(int(dut.output.value))

    assert len(set(outputs_after_reset)) > 1, "No output variation after reset"
    cocotb.log.info("Reset during operation handled correctly")