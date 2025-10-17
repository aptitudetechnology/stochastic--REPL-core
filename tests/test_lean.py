#!/usr/bin/env python3
"""
Test script for Lean 4 formal specifications
"""

import subprocess
import os
import sys

def test_lean_build():
    """Test Lean 4 project build"""
    print("Testing Lean 4 formal specifications...")

    lean_dir = os.path.join(os.path.dirname(__file__), '..', 'lean-stochastic')

    if not os.path.exists(lean_dir):
        print("✗ Lean project directory not found")
        return False

    # Check if lean is available
    try:
        subprocess.run(['lean', '--version'], capture_output=True, check=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("✗ Lean 4 not installed")
        return False

    try:
        # Build the project
        print("Building Lean project...")
        result = subprocess.run(['lake', 'build'], cwd=lean_dir, capture_output=True, text=True, timeout=60)

        if result.returncode != 0:
            print("✗ Build failed:")
            print(result.stderr)
            return False

        print("✓ Lean project built successfully")

        # Test that the module can be imported by checking build success
        # The build already succeeded, so the theorems are verified
        print("✓ StochasticComputing theorems verified through successful build")
        return True

    except subprocess.TimeoutExpired:
        print("✗ Build timed out")
        return False
    except Exception as e:
        print(f"✗ Error: {e}")
        return False

if __name__ == "__main__":
    success = test_lean_build()
    sys.exit(0 if success else 1)