#!/usr/bin/env python3
"""
Device Detection Script for ELM11 and Tang Nano 9K
"""

import serial.tools.list_ports
import serial
import time

def detect_devices():
    ports = list(serial.tools.list_ports.comports())
    print("Found USB serial devices:")
    for port in ports:
        print(f"  {port.device}: {port.description} ({port.manufacturer or 'Unknown'})")

    # Test each port
    elm11_candidates = []
    tang_nano_candidates = []

    for port in ports:
        print(f"\nTesting {port.device}...")
        try:
            ser = serial.Serial(port.device, 115200, timeout=1)
            time.sleep(0.1)

            # Send newline
            ser.write(b'\n')
            time.sleep(0.1)
            response = ser.read(100)

            ser.close()

            if response:
                response_str = response.decode('utf-8', errors='ignore').strip()
                print(f"  Response: {response_str}")

                # Check for ELM11 patterns (Lua REPL)
                if any(marker in response_str.lower() for marker in ['lua', '>', '>>>', 'elm']):
                    elm11_candidates.append((port.device, response_str))
                    print("  -> Likely ELM11 (Lua REPL)")

                # Check for Tang Nano patterns
                elif any(marker in response_str for marker in ['$', 'OK', 'FPGA']):
                    tang_nano_candidates.append((port.device, response_str))
                    print("  -> Likely Tang Nano 9K (FPGA)")

                else:
                    print("  -> Unknown device type")
            else:
                print("  -> No response")

        except Exception as e:
            print(f"  -> Error: {e}")

    print("\nSummary:")
    print(f"ELM11 candidates: {[dev[0] for dev in elm11_candidates]}")
    print(f"Tang Nano candidates: {[dev[0] for dev in tang_nano_candidates]}")

    return elm11_candidates, tang_nano_candidates

if __name__ == "__main__":
    detect_devices()