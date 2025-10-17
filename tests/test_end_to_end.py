#!/usr/bin/env python3
"""
End-to-end test for stochastic REPL core
Tests integration between all components
"""

import subprocess
import time
import serial
import os
import sys

def test_end_to_end(port='/dev/ttyUSB1', baudrate=115200):
    """Test complete stochastic computation workflow"""
    print("Running end-to-end stochastic REPL test...")

    # Step 1: Test Lean formal verification
    print("\n1. Testing Lean 4 specifications...")
    lean_success = subprocess.run([sys.executable, 'test_lean.py'], cwd=os.path.dirname(__file__)).returncode == 0
    if lean_success:
        print("✓ Lean specifications verified")
    else:
        print("✗ Lean test failed")
        return False

    # Step 2: Test Verilog simulation
    print("\n2. Testing Verilog FPGA simulation...")
    verilog_success = subprocess.run([sys.executable, 'test_verilog.py'], cwd=os.path.dirname(__file__)).returncode == 0
    if verilog_success:
        print("✓ Verilog simulation passed")
    else:
        print("✗ Verilog test failed")
        return False

    # Step 3: Test ELM11 Lua REPL
    print("\n3. Testing ELM11 Lua REPL...")
    lua_success = subprocess.run([sys.executable, 'test_lua_repl.py', port], cwd=os.path.dirname(__file__)).returncode == 0
    if lua_success:
        print("✓ Lua REPL test passed")
    else:
        print("✗ Lua REPL test failed")
        return False

    # Step 4: Test stochastic computation accuracy
    print("\n4. Testing stochastic computation accuracy...")
    try:
        ser = serial.Serial(port, baudrate, timeout=2)
        time.sleep(1)

        # Clear buffer
        ser.read(1000)

        # Load test values
        ser.write(b'load a 128\r\n')  # 0.5
        time.sleep(0.5)
        ser.read(1000)

        ser.write(b'load b 64\r\n')   # 0.25
        time.sleep(0.5)
        ser.read(1000)

        # Perform multiplication
        ser.write(b'mul\r\n')
        time.sleep(0.5)
        ser.read(1000)

        # Get result
        ser.write(b'print r\r\n')
        time.sleep(0.5)
        response = ser.read(1000).decode('utf-8', errors='ignore')

        ser.close()

        # Check accuracy (0.5 * 0.25 = 0.125)
        if "0.125" in response or "0.12" in response:
            print("✓ Stochastic computation accuracy verified")
            accuracy_success = True
        else:
            print(f"✗ Accuracy test failed. Response: {response}")
            accuracy_success = False

    except Exception as e:
        print(f"✗ Accuracy test error: {e}")
        accuracy_success = False

    # Summary
    print("\n" + "="*50)
    print("END-TO-END TEST RESULTS")
    print("="*50)
    print(f"Lean 4 Formal Verification: {'PASS' if lean_success else 'FAIL'}")
    print(f"Verilog FPGA Simulation: {'PASS' if verilog_success else 'FAIL'}")
    print(f"Lua REPL Functionality: {'PASS' if lua_success else 'FAIL'}")
    print(f"Stochastic Accuracy: {'PASS' if accuracy_success else 'FAIL'}")

    all_passed = lean_success and verilog_success and lua_success and accuracy_success
    print(f"\nOverall Result: {'ALL TESTS PASSED' if all_passed else 'SOME TESTS FAILED'}")

    return all_passed

if __name__ == "__main__":
    port = sys.argv[1] if len(sys.argv) > 1 else '/dev/ttyUSB1'
    success = test_end_to_end(port)
    sys.exit(0 if success else 1)