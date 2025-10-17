#!/usr/bin/env python3
"""
Test script for ELM11 Lua REPL functionality
"""

import subprocess
import time
import serial
import sys

def test_lua_repl(port='/dev/ttyUSB1', baudrate=115200):
    """Test the Lua REPL by sending commands and checking responses"""
    print("Testing Lua REPL on ELM11...")

    try:
        ser = serial.Serial(port, baudrate, timeout=2)
        time.sleep(1)  # Wait for connection

        # Clear any pending data
        ser.read(1000)

        # Test help command
        print("Sending 'help' command...")
        ser.write(b'help\r\n')
        time.sleep(0.5)
        response = ser.read(1000).decode('utf-8', errors='ignore')
        print(f"Response: {response}")

        if "Commands:" in response:
            print("✓ Help command works")
        else:
            print("✗ Help command failed")

        # Test load command
        print("Sending 'load a 128' command...")
        ser.write(b'load a 128\r\n')
        time.sleep(0.5)
        response = ser.read(1000).decode('utf-8', errors='ignore')
        print(f"Response: {response}")

        if "OK" in response:
            print("✓ Load command works")
        else:
            print("✗ Load command failed")

        # Test print command
        print("Sending 'print a' command...")
        ser.write(b'print a\r\n')
        time.sleep(0.5)
        response = ser.read(1000).decode('utf-8', errors='ignore')
        print(f"Response: {response}")

        if "0.500" in response:
            print("✓ Print command works")
        else:
            print("✗ Print command failed")

        # Test mul command
        print("Sending 'load b 64' command...")
        ser.write(b'load b 64\r\n')
        time.sleep(0.5)
        ser.read(1000)

        print("Sending 'mul' command...")
        ser.write(b'mul\r\n')
        time.sleep(0.5)
        response = ser.read(1000).decode('utf-8', errors='ignore')
        print(f"Response: {response}")

        if "OK" in response:
            print("✓ Mul command works")
        else:
            print("✗ Mul command failed")

        # Test print result
        print("Sending 'print r' command...")
        ser.write(b'print r\r\n')
        time.sleep(0.5)
        response = ser.read(1000).decode('utf-8', errors='ignore')
        print(f"Response: {response}")

        expected = (128 * 64) / 255 / 255  # Approximate 0.125
        if "0.125" in response or "0.12" in response:
            print("✓ Result calculation works")
        else:
            print("✗ Result calculation failed")

        ser.close()
        print("Test completed!")

    except Exception as e:
        print(f"Error: {e}")
        return False

    return True

if __name__ == "__main__":
    port = sys.argv[1] if len(sys.argv) > 1 else '/dev/ttyUSB1'
    test_lua_repl(port)