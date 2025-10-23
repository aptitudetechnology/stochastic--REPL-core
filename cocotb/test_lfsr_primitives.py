#!/usr/bin/env python3
"""
Cocotb Testbench for LFSR Primitives
Tests maximal-length sequence generation for QBG hypothesis validation.

Tests:
- Period verification (255, 127, 511)
- Uniqueness of states
- Statistical properties (balance, runs)
- Initial state handling
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import numpy as np
from utils.statistical_tests import run_statistical_tests
from utils.bitstream_analysis import analyze_bitstream


class LFSRTest:
    """Base class for LFSR testing"""

    def __init__(self, dut, period, taps):
        self.dut = dut
        self.expected_period = period
        self.taps = taps
        self.states = []
        self.outputs = []

    async def collect_sequence(self, num_samples=1000):
        """Collect LFSR sequence"""
        await RisingEdge(self.dut.clk)

        for _ in range(num_samples):
            self.states.append(int(self.dut.state.value))
            self.outputs.append(int(self.dut.out.value))
            await RisingEdge(self.dut.clk)

    def verify_period(self):
        """Verify the LFSR period"""
        # Find first repeat of initial state
        initial_state = self.states[0]
        period = None

        for i, state in enumerate(self.states[1:], 1):
            if state == initial_state:
                period = i
                break

        assert period == self.expected_period, f"Expected period {self.expected_period}, got {period}"
        cocotb.log.info(f"LFSR period verified: {period}")

    def verify_uniqueness(self):
        """Verify all states are unique within period"""
        unique_states = len(set(self.states[:self.expected_period]))
        assert unique_states == self.expected_period, f"Expected {self.expected_period} unique states, got {unique_states}"
        cocotb.log.info(f"Unique states verified: {unique_states}")

    def verify_maximal_length(self):
        """Verify maximal-length properties"""
        # Check balance (roughly equal 0s and 1s)
        ones = sum(self.outputs[:self.expected_period])
        zeros = self.expected_period - ones
        balance_ratio = min(ones, zeros) / max(ones, zeros)

        assert 0.8 < balance_ratio < 1.2, f"Poor balance: {ones} ones, {zeros} zeros"
        cocotb.log.info(f"Balance verified: {ones} ones, {zeros} zeros")

        # Run statistical tests
        bitstream = np.array(self.outputs[:self.expected_period])
        stats = run_statistical_tests(bitstream)

        # Log results
        cocotb.log.info(f"Statistical tests: chi2={stats['chi_square']:.3f}, "
                       f"runs={stats['runs_test']:.3f}, "
                       f"autocorr={stats['autocorr_max']:.3f}")


@cocotb.test()
async def test_lfsr_8bit(dut):
    """Test 8-bit LFSR (period 255)"""
    cocotb.log.info("Testing 8-bit LFSR (period 255)")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Test LFSR
    test = LFSRTest(dut, period=255, taps=[8, 6, 5, 4])  # x^8 + x^6 + x^5 + x^4 + 1
    await test.collect_sequence(300)  # Collect more than period

    test.verify_period()
    test.verify_uniqueness()
    test.verify_maximal_length()

    # Additional analysis
    analysis = analyze_bitstream(np.array(test.outputs[:255]))
    cocotb.log.info(f"Bitstream analysis: entropy={analysis['entropy']:.3f}, "
                   f"complexity={analysis['complexity']:.3f}")


@cocotb.test()
async def test_lfsr_7bit(dut):
    """Test 7-bit LFSR (period 127)"""
    cocotb.log.info("Testing 7-bit LFSR (period 127)")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Test LFSR
    test = LFSRTest(dut, period=127, taps=[7, 6])  # x^7 + x^6 + 1
    await test.collect_sequence(150)

    test.verify_period()
    test.verify_uniqueness()
    test.verify_maximal_length()


@cocotb.test()
async def test_lfsr_9bit(dut):
    """Test 9-bit LFSR (period 511)"""
    cocotb.log.info("Testing 9-bit LFSR (period 511)")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Test LFSR
    test = LFSRTest(dut, period=511, taps=[9, 5])  # x^9 + x^5 + 1
    await test.collect_sequence(550)

    test.verify_period()
    test.verify_uniqueness()
    test.verify_maximal_length()


@cocotb.test()
async def test_lfsr_initial_states(dut):
    """Test LFSR with different initial states"""
    cocotb.log.info("Testing LFSR initial state handling")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Test different initial states (avoid all zeros)
    initial_states = [1, 42, 127, 255]

    for init_val in initial_states:
        # Reset and set initial state
        dut.rst.value = 1
        dut.init.value = init_val
        await Timer(20, units="ns")
        dut.rst.value = 0

        # Collect sequence
        states = []
        for _ in range(10):  # Just check first few states
            await RisingEdge(dut.clk)
            states.append(int(dut.state.value))

        # Verify initial state was loaded
        assert states[0] == init_val, f"Initial state not set correctly: expected {init_val}, got {states[0]}"
        cocotb.log.info(f"Initial state {init_val} verified")


@cocotb.test()
async def test_lfsr_reset_behavior(dut):
    """Test LFSR reset behavior"""
    cocotb.log.info("Testing LFSR reset behavior")

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Run for a bit
    dut.rst.value = 0
    for _ in range(50):
        await RisingEdge(dut.clk)

    state_before_reset = int(dut.state.value)

    # Reset
    dut.rst.value = 1
    await Timer(20, units="ns")
    dut.rst.value = 0

    # Check reset state
    await RisingEdge(dut.clk)
    state_after_reset = int(dut.state.value)

    # Should be back to initial state (1 for most LFSRs)
    assert state_after_reset != state_before_reset, "Reset did not change state"
    cocotb.log.info("Reset behavior verified")