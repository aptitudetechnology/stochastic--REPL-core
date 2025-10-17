#!/usr/bin/env python3
"""
Test script for Verilog FPGA modules using Icarus Verilog
"""

import subprocess
import os
import sys

def test_verilog_simulation():
    """Compile and run Verilog testbench"""
    print("Testing Verilog FPGA modules...")

    verilog_dir = os.path.join(os.path.dirname(__file__), '..', 'verilog')
    testbench_file = os.path.join(verilog_dir, 'tb_stochastic_repl_core.v')

    if not os.path.exists(testbench_file):
        print("✗ Testbench file not found")
        return False

    # Check if iverilog is available
    try:
        subprocess.run(['iverilog', '-v'], capture_output=True, check=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("✗ Icarus Verilog (iverilog) not installed")
        print("  Install with: sudo apt install iverilog")
        return False

    try:
        # Compile the testbench
        print("Compiling Verilog modules...")
        vvp_file = os.path.join(verilog_dir, 'tb_stochastic_repl_core.vvp')

        cmd = [
            'iverilog',
            '-o', vvp_file,
            os.path.join(verilog_dir, 'stochastic_repl_core.v'),
            os.path.join(verilog_dir, 'sng.v'),
            os.path.join(verilog_dir, 'stochastic_multiplier.v'),
            os.path.join(verilog_dir, 'stochastic_adder.v'),
            os.path.join(verilog_dir, 'bitstream_converter.v'),
            testbench_file
        ]

        result = subprocess.run(cmd, cwd=verilog_dir, capture_output=True, text=True)
        if result.returncode != 0:
            print("✗ Compilation failed:")
            print(result.stderr)
            return False

        print("✓ Compilation successful")

        # Run the simulation
        print("Running simulation...")
        result = subprocess.run(['vvp', vvp_file], cwd=verilog_dir, capture_output=True, text=True, timeout=30)

        if result.returncode != 0:
            print("✗ Simulation failed:")
            print(result.stderr)
            return False

        print("✓ Simulation completed successfully")
        print("Simulation output:")
        print(result.stdout[-1000:])  # Last 1000 chars

        return True

    except subprocess.TimeoutExpired:
        print("✗ Simulation timed out")
        return False
    except Exception as e:
        print(f"✗ Error: {e}")
        return False

if __name__ == "__main__":
    success = test_verilog_simulation()
    sys.exit(0 if success else 1)