#!/usr/bin/env python3
"""
Run QBG Cocotb Tests
Simple script to execute the test suite.
"""

import subprocess
import sys
import os
from pathlib import Path

def run_test(test_name, verilog_files, top_module):
    """Run a single cocotb test"""
    print(f"\n{'='*50}")
    print(f"Running test: {test_name}")
    print(f"{'='*50}")

    cmd = [
        "cocotb-run",
        "--module", test_name,
        "--top", top_module,
        "--sim", "icarus",
        "--gui", "0"
    ]

    # Add Verilog files
    for vfile in verilog_files:
        cmd.extend(["--include", str(vfile.parent), str(vfile)])

    print(f"Command: {' '.join(cmd)}")

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, cwd=".")

        if result.returncode == 0:
            print("✓ PASSED")
            print(result.stdout)
        else:
            print("✗ FAILED")
            print("STDOUT:", result.stdout)
            print("STDERR:", result.stderr)
            return False

    except FileNotFoundError:
        print("✗ cocotb-run not found. Please install cocotb:")
        print("  pip install cocotb")
        return False
    except Exception as e:
        print(f"✗ Error running test: {e}")
        return False

    return True

def main():
    """Run all QBG tests"""
    print("QBG Hypothesis Cocotb Test Suite")
    print("=================================")

    # Check if we're in the right directory
    if not Path("Makefile").exists():
        print("Error: Please run from the cocotb directory")
        sys.exit(1)

    # Check if Verilog files exist
    verilog_dir = Path("../verilog/rtl")
    if not verilog_dir.exists():
        print(f"Error: Verilog directory not found: {verilog_dir}")
        sys.exit(1)

    # Define test configurations
    tests = [
        {
            "name": "test_lfsr_primitives",
            "top": "lfsr_8bit",  # Will be overridden for each LFSR
            "files": [
                verilog_dir / "primitives" / "lfsr_8bit.v",
                verilog_dir / "primitives" / "lfsr_7bit.v",
                verilog_dir / "primitives" / "lfsr_9bit.v"
            ]
        },
        {
            "name": "test_qbg_dual_mixer",
            "top": "qbg_dual_mixer",
            "files": [
                verilog_dir / "primitives" / "lfsr_8bit.v",
                verilog_dir / "primitives" / "lfsr_7bit.v",
                verilog_dir / "qbg" / "qbg_dual_mixer.v"
            ]
        },
        {
            "name": "test_stochastic_mult",
            "top": "stochastic_mult_test",
            "files": [
                verilog_dir / "primitives" / "lfsr_8bit.v",
                verilog_dir / "primitives" / "lfsr_7bit.v",
                verilog_dir / "qbg" / "qbg_dual_mixer.v",
                verilog_dir / "qbg" / "sng_baseline.v",
                verilog_dir / "test" / "stochastic_mult_test.v"
            ]
        },
        {
            "name": "test_qbg_top",
            "top": "qbg_test_top",
            "files": [
                verilog_dir / "primitives" / "lfsr_8bit.v",
                verilog_dir / "primitives" / "lfsr_7bit.v",
                verilog_dir / "qbg" / "qbg_dual_mixer.v",
                verilog_dir / "test" / "qbg_test_top.v"
            ]
        }
    ]

    # Run tests
    passed = 0
    total = len(tests)

    for test_config in tests:
        if run_test(test_config["name"], test_config["files"], test_config["top"]):
            passed += 1

    # Summary
    print(f"\n{'='*50}")
    print("TEST SUMMARY")
    print(f"{'='*50}")
    print(f"Passed: {passed}/{total}")

    if passed == total:
        print("🎉 All tests passed!")
        return 0
    else:
        print("❌ Some tests failed")
        return 1

if __name__ == "__main__":
    sys.exit(main())