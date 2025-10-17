#!/usr/bin/env python3
"""
Simple serial terminal for testing ELM11
"""

import serial
import sys

def serial_terminal(port, baudrate=115200):
    try:
        ser = serial.Serial(port, baudrate, timeout=1)
        print(f"Connected to {port} at {baudrate} baud")
        print("Type commands, Ctrl+C to exit")

        # Initialize ELM11
        ser.write(b'q\r\n')
        ser.flush()
        import time
        time.sleep(0.5)
        ser.read(256)
        ser.write(b'exit\r\n')
        time.sleep(0.5)
        ser.read(256)
        ser.write(b'exit\r\n')
        time.sleep(0.5)
        ser.read(256)
        ser.write(b'\r\n')
        time.sleep(0.5)
        response = ser.read(100)
        print(f"Init response: {response}")

        while True:
            # Read from serial
            if ser.in_waiting:
                data = ser.read(ser.in_waiting)
                print(data.decode('utf-8', errors='ignore'), end='')

            # Read from stdin
            import select
            if select.select([sys.stdin], [], [], 0)[0]:
                line = sys.stdin.readline().strip()
                if line:
                    ser.write((line + '\r\n').encode())
                    ser.flush()

    except KeyboardInterrupt:
        print("\nExiting...")
    except Exception as e:
        print(f"Error: {e}")
    finally:
        if 'ser' in locals():
            ser.close()

if __name__ == "__main__":
    if len(sys.argv) > 1:
        port = sys.argv[1]
    else:
        port = '/dev/ttyUSB0'
    serial_terminal(port)