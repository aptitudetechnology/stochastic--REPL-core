#!/usr/bin/env python3
"""
Validate QBG Testbench Setup
Checks that all dependencies and utilities are properly configured.
"""

import sys
import importlib
from pathlib import Path

def check_python_version():
    """Check Python version"""
    print(f"Python version: {sys.version}")
    if sys.version_info < (3, 8):
        print("⚠️  Warning: Python 3.8+ recommended for cocotb")
    else:
        print("✓ Python version OK")

def check_dependencies():
    """Check if required packages are installed"""
    required_packages = [
        'numpy',
        'scipy',
        'matplotlib',
        'cocotb'
    ]

    missing = []
    for package in required_packages:
        try:
            importlib.import_module(package)
            print(f"✓ {package} available")
        except ImportError:
            print(f"✗ {package} missing")
            missing.append(package)

    if missing:
        print(f"\nMissing packages: {', '.join(missing)}")
        print("Install with: pip install -r requirements.txt")
        return False

    return True

def check_utils():
    """Check if utility modules can be imported"""
    utils_dir = Path(__file__).parent / 'utils'

    if not utils_dir.exists():
        print(f"✗ Utils directory not found: {utils_dir}")
        return False

    # Add to path if not already there
    if str(utils_dir) not in sys.path:
        sys.path.insert(0, str(utils_dir))

    utils_modules = [
        'statistical_tests',
        'bitstream_analysis',
        'correlation_analysis'
    ]

    for module in utils_modules:
        try:
            importlib.import_module(module)
            print(f"✓ {module} importable")
        except ImportError as e:
            print(f"✗ {module} import failed: {e}")
            return False

    return True

def check_verilog_files():
    """Check if Verilog source files exist"""
    verilog_root = Path(__file__).parent.parent / 'verilog' / 'rtl'

    if not verilog_root.exists():
        print(f"✗ Verilog directory not found: {verilog_root}")
        return False

    required_files = [
        'primitives/lfsr_8bit.v',
        'primitives/lfsr_7bit.v',
        'primitives/lfsr_9bit.v',
        'qbg/qbg_dual_mixer.v',
        'qbg/sng_baseline.v',
        'test/stochastic_mult_test.v',
        'test/qbg_test_top.v'
    ]

    missing = []
    for vfile in required_files:
        if not (verilog_root / vfile).exists():
            missing.append(vfile)
        else:
            print(f"✓ {vfile} found")

    if missing:
        print(f"\nMissing Verilog files: {', '.join(missing)}")
        return False

    return True

def check_test_files():
    """Check if test files exist"""
    test_files = [
        'test_lfsr_primitives.py',
        'test_qbg_dual_mixer.py',
        'test_stochastic_mult.py',
        'test_qbg_top.py',
        'run_tests.py'
    ]

    missing = []
    for tfile in test_files:
        if not Path(tfile).exists():
            missing.append(tfile)
        else:
            print(f"✓ {tfile} found")

    if missing:
        print(f"\nMissing test files: {', '.join(missing)}")
        return False

    return True

def test_utils_functionality():
    """Test that utility functions work"""
    try:
        import numpy as np
        from utils.statistical_tests import run_statistical_tests
        from utils.bitstream_analysis import analyze_bitstream

        # Test with random data
        test_data = np.random.randint(0, 2, 1000)

        stats = run_statistical_tests(test_data)
        analysis = analyze_bitstream(test_data)

        print("✓ Statistical tests working")
        print("✓ Bitstream analysis working")

        # Check results are reasonable
        assert 0 < stats['chi_square'] < 1, "Chi-square test failed"
        assert 0 < analysis['entropy'] < 1, "Entropy calculation failed"

        print("✓ Utility functions produce reasonable results")

        return True

    except Exception as e:
        print(f"✗ Utility functionality test failed: {e}")
        return False

def main():
    """Run all validation checks"""
    print("QBG Cocotb Testbench Validation")
    print("=" * 40)

    checks = [
        ("Python version", check_python_version),
        ("Dependencies", check_dependencies),
        ("Utility modules", check_utils),
        ("Verilog files", check_verilog_files),
        ("Test files", check_test_files),
        ("Utility functionality", test_utils_functionality),
    ]

    results = []
    for name, check_func in checks:
        print(f"\n{name}:")
        try:
            result = check_func()
            results.append(result)
        except Exception as e:
            print(f"✗ {name} check failed with exception: {e}")
            results.append(False)

    print(f"\n{'=' * 40}")
    print("VALIDATION SUMMARY")
    print(f"{'=' * 40}")

    passed = sum(results)
    total = len(results)

    for i, (name, _) in enumerate(checks):
        status = "✓" if results[i] else "✗"
        print(f"{status} {name}")

    print(f"\nPassed: {passed}/{total}")

    if passed == total:
        print("🎉 All validation checks passed!")
        print("\nYou can now run the tests with:")
        print("  make test-all")
        print("  python run_tests.py")
        return 0
    else:
        print("❌ Some validation checks failed.")
        print("Please fix the issues above before running tests.")
        return 1

if __name__ == "__main__":
    sys.exit(main())