# ELM11 Multi-Hardware GPIO Wiring Schematic

## Complete System Interconnection Diagram

```
┌──────────────────────────────────────────────────────────────────┐
│                         ELM11 Board                               │
│                    (4x RISC-V Cores + Lua)                       │
│                                                                   │
│  ┌────────────┐                                                  │
│  │   USB      │◄──────────────── To Computer (REPL Terminal)    │
│  │   UART     │                                                  │
│  └────────────┘                                                  │
│                                                                   │
│  GPIO Pinout (32 pins):                                          │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │ 0-7:   Tang Nano #1   │ 16-23: 4000-CMOS    │ 28: LED0    │ │
│  │ 8-15:  Tang Nano #2   │ 24-27: Analog/Power │ 29: LED1    │ │
│  │                       │                      │ 30-31: Spare│ │
│  └────────────────────────────────────────────────────────────┘ │
│         │         │              │           │          │        │
└─────────┼─────────┼──────────────┼───────────┼──────────┼────────┘
          │         │              │           │          │
          │         │              │           │          │
          ▼         ▼              ▼           ▼          ▼
    ┌─────────┬─────────┬───────────────┬──────────┬────────┐
    │         │         │               │          │        │
    │  Tang   │  Tang   │  4000-Series  │  Analog  │  Power │
    │  Nano   │  Nano   │  CMOS Logic   │  RNG     │Monitor │
    │   #1    │   #2    │  ICs          │  Circuit │  INA219│
    │         │         │               │          │        │
    └─────────┴─────────┴───────────────┴──────────┴────────┘
```

---

## Detailed Pin Assignments

### ELM11 GPIO Bank 0 (GPIO 0-7): Tang Nano 9K #1

| ELM11 Pin | Signal Name | Direction | Tang Nano Pin | Function |
|-----------|-------------|-----------|---------------|----------|
| GPIO0 | FPGA1_CLK | Output | IO3 | Master clock (1-10 MHz) |
| GPIO1 | FPGA1_MOSI | Output | IO4 | SPI-like data to FPGA |
| GPIO2 | FPGA1_MISO | Input | IO5 | SPI-like data from FPGA |
| GPIO3 | FPGA1_CS | Output | IO6 | Chip select / enable |
| GPIO4 | FPGA1_READY | Input | IO7 | FPGA computation done |
| GPIO5 | FPGA1_RESET | Output | IO8 | Hardware reset |
| GPIO6 | FPGA1_MODE0 | Output | IO9 | Mode select bit 0 |
| GPIO7 | FPGA1_MODE1 | Output | IO10 | Mode select bit 1 |

**Mode Select Encoding:**
```
MODE[1:0] = 00: Idle
MODE[1:0] = 01: Bitstream generation (LFSR)
MODE[1:0] = 10: Stochastic multiply (AND)
MODE[1:0] = 11: Stochastic add (MUX)
```

---

### ELM11 GPIO Bank 1 (GPIO 8-15): Tang Nano 9K #2

| ELM11 Pin | Signal Name | Direction | Tang Nano Pin | Function |
|-----------|-------------|-----------|---------------|----------|
| GPIO8 | FPGA2_CLK | Output | IO3 | Master clock (1-10 MHz) |
| GPIO9 | FPGA2_MOSI | Output | IO4 | SPI-like data to FPGA |
| GPIO10 | FPGA2_MISO | Input | IO5 | SPI-like data from FPGA |
| GPIO11 | FPGA2_CS | Output | IO6 | Chip select / enable |
| GPIO12 | FPGA2_READY | Input | IO7 | FPGA computation done |
| GPIO13 | FPGA2_RESET | Output | IO8 | Hardware reset |
| GPIO14 | FPGA2_MODE0 | Output | IO9 | Mode select bit 0 |
| GPIO15 | FPGA2_MODE1 | Output | IO10 | Mode select bit 1 |

**Identical protocol to FPGA1 for easy code reuse**

---

### ELM11 GPIO Bank 2 (GPIO 16-23): 4000-Series CMOS ICs

| ELM11 Pin | Signal Name | Direction | CMOS IC Pins | Function |
|-----------|-------------|-----------|--------------|----------|
| GPIO16 | CMOS_LFSR_CLK | Output | CD4094 pin 3 (CLK) | Clock for shift registers |
| GPIO17 | CMOS_LFSR_DATA | Output | CD4094 pin 2 (DATA) | Serial data input |
| GPIO18 | CMOS_LFSR_STROBE | Output | CD4094 pin 1 (STB) | Latch/strobe signal |
| GPIO19 | CMOS_COUNTER_READ | Input | CD4040 pins 9-12 | Parallel counter outputs |
| GPIO20 | CMOS_MUX_SEL | Output | CD4053 pin 9 (SEL) | MUX select signal |
| GPIO21 | CMOS_RESULT | Input | CD4081 output | AND gate result |
| GPIO22 | CMOS_RESET | Output | All ICs pin 15 | Master reset |
| GPIO23 | CMOS_ENABLE | Output | Power control | Enable CMOS circuit |

**Note:** Counter read uses 4 wires (GPIO19 + 3 adjacent GPIO on separate header)

---

### ELM11 GPIO Bank 3 (GPIO 24-27): Analog & Power

| ELM11 Pin | Signal Name | Direction | Device | Function |
|-----------|-------------|-----------|--------|----------|
| GPIO24 | I2C_SDA | Bidirectional | INA219 pin 5 | Power monitor data |
| GPIO25 | I2C_SCL | Output | INA219 pin 6 | Power monitor clock |
| GPIO26 | ADC_MISO | Input | MCP3008 pin 12 | ADC data (analog RNG) |
| GPIO27 | ADC_CS | Output | MCP3008 pin 10 | ADC chip select |

**Shared SPI bus for ADC:**
- CLK: Use GPIO0 (shared with FPGA1_CLK, time-multiplexed)
- MOSI: Use GPIO1 (shared with FPGA1_MOSI)

---

### ELM11 Status LEDs (GPIO 28-31)

| ELM11 Pin | Signal Name | Color | Function |
|-----------|-------------|-------|----------|
| GPIO28 | STATUS_LED0 | Green | System active / heartbeat |
| GPIO29 | STATUS_LED1 | Blue | FPGA computing |
| GPIO30 | STATUS_LED2 | Yellow | CMOS computing |
| GPIO31 | STATUS_LED3 | Red | Error / fault |

---

## Physical Wiring Diagrams

### Breadboard Layout (Top View)

```
┌─────────────────────────────────────────────────────────────────┐
│  +5V Rail  ══════════════════════════════════════════════════  │
│  +3.3V Rail══════════════════════════════════════════════════  │
│  GND Rail  ══════════════════════════════════════════════════  │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│                        ELM11 Board                               │
│  ┌──────────────────────────────────────────────┐               │
│  │ [USB]  RISC-V x4   [GPIO 0-31]              │               │
│  │         + Lua                                │               │
│  └──────────────────────────────────────────────┘               │
│       │││││││││                         │││││││││               │
│       GPIO 0-7                         GPIO 16-23               │
└───────┬┬┬┬┬┬┬┬─────────────────────────┬┬┬┬┬┬┬┬─────────────────┘
        ││││││││                         ││││││││
        ││││││││                         ││││││││
        ▼▼▼▼▼▼▼▼                         ▼▼▼▼▼▼▼▼

┌───────────────┐  ┌───────────────┐  ┌─────────────────────────┐
│ Tang Nano #1  │  │ Tang Nano #2  │  │ 4000-Series CMOS Board  │
│ ┌───────────┐ │  │ ┌───────────┐ │  │ ┌────┐ ┌────┐ ┌────┐  │
│ │ GW1NR-9   │ │  │ │ GW1NR-9   │ │  │ │4094│ │4094│ │4081│  │
│ │ FPGA      │ │  │ │ FPGA      │ │  │ │LFSR│ │LFSR│ │AND │  │
│ │           │ │  │ │           │ │  │ └────┘ └────┘ └────┘  │
│ └───────────┘ │  │ └───────────┘ │  │ ┌────┐ ┌────┐ ┌────┐  │
│               │  │               │  │ │4053│ │4053│ │4040│  │
│ [Pins 3-10]   │  │ [Pins 3-10]   │  │ │MUX │ │MUX │ │CNT │  │
└───────────────┘  └───────────────┘  │ └────┘ └────┘ └────┘  │
                                      └─────────────────────────┘

┌──────────────────────────────────────────────────────────────┐
│  Lower Board: Analog & Power Monitoring                      │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌────────────┐  │
│  │ MCP3008  │  │2N3904+   │  │ INA219   │  │ Level      │  │
│  │ ADC      │  │Zener RNG │  │ Power    │  │ Shifters   │  │
│  │ (SPI)    │  │ Circuit  │  │ Monitor  │  │ 3.3V↔5V    │  │
│  └──────────┘  └──────────┘  └──────────┘  └────────────┘  │
└──────────────────────────────────────────────────────────────┘
```

---

## Detailed Connection Schematics

### 1. ELM11 to Tang Nano #1 (SPI-like Protocol)

```
ELM11 Side:                    Tang Nano 9K Side:
                               
GPIO0 (3.3V) ─────────────────► IO3 (CLK)
             100Ω              
GPIO1 (3.3V) ─────────────────► IO4 (MOSI)
             100Ω
GPIO2 (3.3V) ◄───────────────── IO5 (MISO)
             (direct)
GPIO3 (3.3V) ─────────────────► IO6 (CS)
             100Ω
GPIO4 (3.3V) ◄───────────────── IO7 (READY)
             (direct)
GPIO5 (3.3V) ─────────────────► IO8 (RESET)
             100Ω
GPIO6 (3.3V) ─────────────────► IO9 (MODE0)
             100Ω
GPIO7 (3.3V) ─────────────────► IO10 (MODE1)
             100Ω

Common:
GND ──────────────────────────── GND
3.3V ─┬───────────────────────── VCC (Tang Nano)
      │
      └─── 10µF decoupling cap to GND
           (physically close to Tang Nano)

Notes:
- 100Ω series resistors for current limiting
- All signals are 3.3V logic (compatible)
- Keep wires < 15cm for signal integrity
```

### 2. ELM11 to 4000-Series CMOS (5V Logic)

```
ELM11 Side (3.3V):              4000-Series ICs (5V):

GPIO16 ───┬────► Level ───────► CD4094 #1 Pin 3 (CLK)
          │      Shifter        CD4094 #2 Pin 3 (CLK)
          │      74LVC245               
GPIO17 ───┼────► or      ───────► CD4094 #1 Pin 2 (DATA)
          │      BSS138          CD4094 #2 Pin 2 (DATA)
GPIO18 ───┼────►         ───────► CD4094 #1 Pin 1 (STROBE)
          │                      CD4094 #2 Pin 1 (STROBE)
GPIO20 ───┘─────►         ───────► CD4053 Pin 9 (SELECT)

                         ┌─── CD4081 Output
GPIO21 ◄─── Level ◄──────┤
            Shifter      ├─── CD4040 Pin 9 (Q0)
GPIO19 ◄─── (5V→3.3V) ◄──┼─── CD4040 Pin 7 (Q1)
                         ├─── CD4040 Pin 6 (Q2)
                         └─── CD4040 Pin 5 (Q3)

GPIO22 ───► Level ───────► All ICs Pin 15 (RESET)
            Shifter

Power:
5V ────┬─────────────────► CD40xx VDD (Pin 16)
       │
       └─── 100nF decoupling caps (one per IC)
            + 10µF bulk cap

GND ──────────────────────► CD40xx VSS (Pin 8)

Level Shifter Detail:
┌────────────────────────────────────┐
│  74LVC245 (Bidirectional)          │
│                                    │
│  3.3V side ◄───►  5V side          │
│  (ELM11)          (4000-series)    │
│                                    │
│  VCC1: 3.3V       VCC2: 5V         │
│  DIR: Control direction            │
│  OE: Always enabled (GND)          │
└────────────────────────────────────┘

Alternative (cheaper):
BSS138 MOSFET level shifter:
  3.3V ─┬─[10kΩ]─┬─── 5V
        │        │
   3.3V │   5V   │
   GPIO ┼───||───┤ To CMOS IC
        │ BSS138 │
       GND      GND
```

### 3. ELM11 to Analog RNG (MCP3008 ADC)

```
ELM11 Side:                     MCP3008 ADC:

GPIO0 (shared) ──────────────►  Pin 13 (CLK)
                100Ω
GPIO1 (shared) ──────────────►  Pin 11 (DIN)
                100Ω
GPIO26 ◄─────────────────────  Pin 12 (DOUT)
       (direct)
GPIO27 ──────────────────────►  Pin 10 (CS/SHDN)
       100Ω

Analog Input (from RNG circuit):
┌────────────────────────────┐
│  Avalanche Noise Generator │
│                            │
│  +5V                       │
│   │                        │
│   R1 (100kΩ)               │
│   │                        │
│   ├──── Zener 5.1V         │
│   │     (reverse bias)     │
│   C1 (100pF)               │
│   │                        │
│   ├──── LM358 Op-Amp       │
│   │     (gain = 100x)      │
│   │                        │
│   └─────────────────────►  MCP3008 Pin 1 (CH0)
│                         │
│  RC filter (1kΩ + 10nF) │
│  to remove DC offset    │
└─────────────────────────┘

Power for MCP3008:
3.3V ────────────────►  Pin 16 (VDD)
                       Pin 15 (VREF)
GND ─────────────────►  Pin 9 (DGND)
                       Pin 14 (AGND)

Decoupling:
- 100nF ceramic cap between VDD-GND
- 10µF electrolytic cap between VDD-GND
- Keep analog ground separate, star ground point
```

### 4. ELM11 to Power Monitor (INA219)

```
ELM11 Side:                   INA219 Power Monitor:

GPIO24 (SDA) ◄───┬──────────►  Pin 5 (SDA)
                 │   4.7kΩ
                 ├─── pullup to 3.3V
GPIO25 (SCL) ─────┼──────────►  Pin 6 (SCL)
                 │   4.7kΩ
                 └─── pullup to 3.3V

Power measurement circuit:
┌────────────────────────────────────┐
│                                    │
│  +5V (from supply)                 │
│   │                                │
│   │   INA219 measures current here │
│   ├──► Pin 1 (VIN+)                │
│   │                                │
│   R_shunt (0.1Ω, 1W)               │
│   │                                │
│   ├──► Pin 2 (VIN-)                │
│   │                                │
│   └──► To FPGA/CMOS/etc VCC        │
│                                    │
│  Note: Separate INA219 for each    │
│        power domain to measure     │
│        individually:               │
│        - FPGA1 power               │
│        - FPGA2 power               │
│        - CMOS power                │
│        - Total system power        │
└────────────────────────────────────┘

I2C Address Configuration:
- INA219 #1 (FPGA1): A0=GND, A1=GND → 0x40
- INA219 #2 (FPGA2): A0=VCC, A1=GND → 0x41
- INA219 #3 (CMOS):  A0=GND, A1=VCC → 0x44
- INA219 #4 (Total): A0=VCC, A1=VCC → 0x45

All share same I2C bus (GPIO24/25)
```

---

## Component Bill of Materials (BOM)

### Interconnect Components

| Part | Qty | Description | Unit Price | Total |
|------|-----|-------------|-----------|-------|
| **Level Shifters** | | | | |
| 74LVC245 (DIP) | 2 | Bidirectional 8-bit | $0.75 | $1.50 |
| BSS138 MOSFET | 10 | Alternative shifter | $0.15 | $1.50 |
| **Resistors** | | | | |
| 100Ω (1/4W) | 20 | Series protection | $0.02 | $0.40 |
| 4.7kΩ (1/4W) | 4 | I2C pullups | $0.02 | $0.08 |
| 10kΩ (1/4W) | 10 | General purpose | $0.02 | $0.20 |
| **Capacitors** | | | | |
| 100nF ceramic | 20 | Decoupling | $0.10 | $2.00 |
| 10µF electrolytic | 10 | Bulk decoupling | $0.15 | $1.50 |
| **Connectors** | | | | |
| 2.54mm headers (40pin) | 4 | Pin headers | $0.50 | $2.00 |
| Dupont cables (F-F) | 100 | Jumper wires | $0.05 | $5.00 |
| Dupont cables (M-F) | 50 | Jumper wires | $0.05 | $2.50 |
| **Breadboards** | | | | |
| 830-point breadboard | 3 | Main boards | $4.00 | $12.00 |
| 400-point breadboard | 2 | Auxiliary | $2.00 | $4.00 |
| **Power** | | | | |
| 0.1Ω 1W shunt resistor | 4 | Current sensing | $0.50 | $2.00 |
| Breadboard power supply | 2 | 5V/3.3V rails | $3.00 | $6.00 |
| **Total** | | | | **$40.68** |

### Optional: Professional PCB Instead of Breadboard

```
Custom PCB Design:
┌─────────────────────────────────────┐
│  ELM11 → Multi-Hardware Interface   │
│  PCB (2-layer, 100mm x 80mm)        │
│                                     │
│  - ELM11 header                     │
│  - 2x Tang Nano headers             │
│  - 4000-series IC sockets           │
│  - Built-in level shifters          │
│  - Power monitoring headers         │
│  - Status LEDs                      │
│  - All decoupling caps              │
│                                     │
│  Cost: $2 per board (JLCPCB)        │
│  MOQ: 5 boards → $10 total          │
└─────────────────────────────────────┘
```

---

## Wiring Checklist

### Pre-Wiring Tests

- [ ] Verify ELM11 GPIO voltage (should be 3.3V)
- [ ] Verify Tang Nano IO voltage (should be 3.3V)
- [ ] Verify 4000-series VCC (should be 5V)
- [ ] Test level shifters with multimeter
- [ ] Check for shorts on power rails

### Tang Nano #1 Connections

- [ ] GPIO0 → IO3 (CLK) with 100Ω resistor
- [ ] GPIO1 → IO4 (MOSI) with 100Ω resistor
- [ ] GPIO2 ← IO5 (MISO) direct
- [ ] GPIO3 → IO6 (CS) with 100Ω resistor
- [ ] GPIO4 ← IO7 (READY) direct
- [ ] GPIO5 → IO8 (RESET) with 100Ω resistor
- [ ] GPIO6 → IO9 (MODE0) with 100Ω resistor
- [ ] GPIO7 → IO10 (MODE1) with 100Ω resistor
- [ ] 3.3V and GND connected
- [ ] 10µF decoupling cap near Tang Nano VCC

### Tang Nano #2 Connections

- [ ] GPIO8-15 connected same as GPIO0-7
- [ ] Separate 10µF decoupling cap
- [ ] Verify no shorts to Tang Nano #1

### 4000-Series CMOS Connections

- [ ] Level shifter installed (3.3V ↔ 5V)
- [ ] GPIO16 → CD4094 CLK through level shifter
- [ ] GPIO17 → CD4094 DATA through level shifter
- [ ] GPIO18 → CD4094 STROBE through level shifter
- [ ] GPIO19 ← CD4040 outputs through level shifter
- [ ] GPIO20 → CD4053 SELECT through level shifter
- [ ] GPIO21 ← CD4081 output through level shifter
- [ ] GPIO22 → RESET (all ICs) through level shifter
- [ ] 100nF cap on each IC (VDD to GND)
- [ ] 10µF bulk cap on 5V rail

### Analog RNG Connections

- [ ] GPIO0 shared → MCP3008 CLK
- [ ] GPIO1 shared → MCP3008 DIN
- [ ] GPIO26 ← MCP3008 DOUT
- [ ] GPIO27 → MCP3008 CS
- [ ] Avalanche noise circuit built and tested
- [ ] Op-amp powered and stable
- [ ] MCP3008 decoupling caps installed

### Power Monitor Connections

- [ ] GPIO24 ↔ INA219 SDA (all units)
- [ ] GPIO25 → INA219 SCL (all units)
- [ ] 4.7kΩ pullups on SDA and SCL
- [ ] 0.1Ω shunt resistors installed
- [ ] I2C addresses configured correctly
- [ ] Test I2C communication before power

### Status LEDs

- [ ] GPIO28 → Green LED + 220Ω resistor
- [ ] GPIO29 → Blue LED + 220Ω resistor
- [ ] GPIO30 → Yellow LED + 220Ω resistor
- [ ] GPIO31 → Red LED + 220Ω resistor

---

## Testing Procedure

### Step 1: Power-On Test (No ICs Installed)

```lua
-- ELM11 Test Script
print("Testing GPIO outputs...")

-- Toggle each GPIO
for pin = 0, 31 do
    gpio.mode(pin, gpio.OUTPUT)
    gpio.write(pin, 1)
    sleep(100)
    gpio.write(pin, 0)
end

print("Check with multimeter: Each pin should pulse 3.3V")
```

### Step 2: Tang Nano Communication Test

```lua
-- Test FPGA #1 connection
print("Testing Tang Nano #1...")

gpio.write(GPIO_FPGA1_RESET, 0)
sleep(10)
gpio.write(GPIO_FPGA1_RESET, 1)
sleep(100)

-- Send test pattern
gpio.write(GPIO_FPGA1_CS, 0)
for i = 1, 8 do
    gpio.write(GPIO_FPGA1_MOSI, i % 2)
    gpio.write(GPIO_FPGA1_CLK, 1)
    sleep(1)
    gpio.write(GPIO_FPGA1_CLK, 0)
    sleep(1)
end
gpio.write(GPIO_FPGA1_CS, 1)

-- Check READY signal
if gpio.read(GPIO_FPGA1_READY) == 1 then
    print("✓ Tang Nano #1 responding")
else
    print("✗ Tang Nano #1 not ready")
end
```

### Step 3: Level Shifter Test

```lua
-- Test 3.3V → 5V conversion
print("Testing level shifters...")

gpio.mode(GPIO_CMOS_LFSR_CLK, gpio.OUTPUT)
gpio.write(GPIO_CMOS_LFSR_CLK, 1)
sleep(100)

-- Measure with multimeter on CMOS side
-- Should read ~5V

print("Check with multimeter: CMOS side should be ~5V")
```

### Step 4: CMOS IC Test

```lua
-- Test 4000-series communication
print("Testing 4000-series CMOS...")

-- Reset all ICs
gpio.write(GPIO_CMOS_RESET, 0)
sleep(10)
gpio.write(GPIO_CMOS_RESET, 1)
sleep(10)

-- Clock in test pattern to CD4094
for i = 1, 8 do
    gpio.write(GPIO_CMOS_LFSR_DATA, i % 2)
    gpio.write(GPIO_CMOS_LFSR_CLK, 1)
    sleep(1)
    gpio.write(GPIO_CMOS_LFSR_CLK, 0)
    sleep(1)
end

-- Strobe to latch
gpio.write(GPIO_CMOS_LFSR_STROBE, 1)
sleep(1)
gpio.write(GPIO_CMOS_LFSR_STROBE, 0)

print("✓ CMOS ICs programmed")
```

### Step 5: I2C Power Monitor Test

```lua
-- Test INA219 communication
i2c_init(GPIO24, GPIO25, 100000)  -- 100kHz

-- Try to read from each INA219
addresses = {0x40, 0x41, 0x44, 0x45}
for _, addr in ipairs(addresses) do
    i2c_start()
    if i2c_address(addr, I2C_WRITE) then
        print(string.format("✓ INA219 at 0x%02X responding", addr))
    else
        print(string.format("✗ INA219 at 0x%02X not found", addr))
    end
    i2c_stop()
end
```

### Step 6: End-to-End Test

```lua
-- Complete system test
print("Running end-to-end test...")

-- 1. Generate bitstream on FPGA
fpga_load_value(1, 128)  -- 0.5
fpga_load_value(2, 64)   -- 0.25

-- 2. Multiply using CMOS
cmos_multiply()

-- 3. Read result
result = cmos_read_counter()
print(string.format("Result: %.3f (expected: 0.125)", result/256))

-- 4. Measure power
power_fpga1 = ina219_read(0x40)
power_cmos = ina219_read(0x44)
print(string.format("FPGA power: %.2f mW", power_fpga1))
print(string.format("CMOS power: %.6f mW", power_cmos))

print("✓ System fully operational!")
```

---

## Advanced Wiring: Multi-Board Clustering

### Cascading Multiple ELM11 Systems

For scaling beyond one ELM11 + 2 FPGAs, you can network multiple ELM11 boards:

```
                    Master ELM11
                         │
           ┌─────────────┼─────────────┐
           │             │             │
      Slave ELM11   Slave ELM11   Slave ELM11
           │             │             │
      Tang Nano x2   Tang Nano x2  Tang Nano x2
      + CMOS ICs     + CMOS ICs    + CMOS ICs

Total: 6 FPGAs + 3x CMOS IC sets
```

**Inter-ELM11 Communication:**

```
Master ELM11:                 Slave ELM11 #1:
GPIO30 (TX) ──────────────►  GPIO31 (RX)
GPIO31 (RX) ◄──────────────  GPIO30 (TX)

Protocol: Simple serial at 115200 baud
Commands:
  - JOB_ASSIGN <data>
  - JOB_COMPLETE <result>
  - STATUS_REQUEST
  - STATUS_RESPONSE <stats>
```

---

## Physical Construction Guide

### Method 1: Breadboard Stack (Quick Prototype)

**Materials Needed:**
- 3x 830-point breadboards
- 2x 400-point breadboards
- Acrylic standoffs or 3D printed spacers
- M3 screws and nuts

**Assembly:**

```
Layer 1 (Bottom): Power Distribution
┌────────────────────────────────────┐
│  Breadboard Power Supply Modules   │
│  - 5V regulators                   │
│  - 3.3V regulators                 │
│  - Bulk capacitors                 │
│  - Fuse protection                 │
└────────────────────────────────────┘
     ││││ (Power rails up)
     
Layer 2 (Middle): Control & Interface
┌────────────────────────────────────┐
│  ELM11 Board                       │
│  - GPIO headers pointing down      │
│  - USB cable accessible from side  │
│  - Status LEDs visible on edge     │
└────────────────────────────────────┘
     ││││ (GPIO signals down & up)
     
Layer 3 (Top): Computation Hardware
┌────────────────────────────────────┐
│  Left: Tang Nano #1 & #2           │
│  Right: 4000-Series CMOS ICs       │
│  Center: Analog RNG + Power Mon.   │
└────────────────────────────────────┘
```

**Wire Routing:**
- Power: Vertical through all layers
- Signals: Bus bars on breadboard edges
- Keep high-speed (CLK) separate from power
- Twist pairs for I2C signals

### Method 2: Custom PCB (Production Quality)

**PCB Design Specifications:**

```
Board Dimensions: 160mm x 100mm (Eurocard size)
Layers: 2-layer (adequate for this design)
Copper: 1oz (35µm)
Finish: ENIG (better for reliability)

Layer Stack:
  Top: Components + Signal traces
  Bottom: Ground plane + Power traces

Sections:
┌─────────────────────────────────────────┐
│  [ELM11 Socket]     [Status LEDs]       │
│                                         │
│  [Tang #1]   [Tang #2]   [Power Mon.]  │
│  [Socket]    [Socket]    [INA219]      │
│                                         │
│  [CD4094] [CD4094] [CD4081] [CD4081]   │
│  [CD4053] [CD4053] [CD4040] [CD4069]   │
│                                         │
│  [Level Shifters]  [ADC]  [RNG Circuit]│
│                                         │
│  [Power Input] [I2C] [GPIO Test Points]│
└─────────────────────────────────────────┘

Cost Estimate:
  - PCB fabrication (5 units): $15 @ JLCPCB
  - Components: $40 (from BOM)
  - Assembly time: 2-3 hours
  - Total per board: $55
```

**KiCad Design Files Structure:**

```
stochastic-elm11-interface/
├── stochastic_interface.kicad_pro
├── stochastic_interface.kicad_sch    # Schematic
├── stochastic_interface.kicad_pcb    # PCB layout
├── symbols/
│   ├── ELM11.kicad_sym
│   ├── Tang_Nano_9K.kicad_sym
│   └── CD40xx_series.kicad_sym
├── footprints/
│   ├── ELM11_header.kicad_mod
│   └── Tang_Nano_header.kicad_mod
├── 3d_models/
│   └── (optional 3D visualization)
└── gerbers/
    └── (manufacturing files)
```

---

## Troubleshooting Guide

### Common Issues and Solutions

#### Issue 1: FPGA Not Responding

**Symptoms:**
- FPGA1_READY never goes high
- No response on MISO line

**Check:**
```
1. Verify 3.3V power at Tang Nano VCC pin
   Measure: Should be 3.28V - 3.35V
   
2. Check clock signal with oscilloscope
   GPIO0 should show clean square wave
   Rise time < 10ns
   
3. Verify chip select timing
   CS should go low BEFORE first clock edge
   CS should stay low during entire transaction
   
4. Check RESET signal
   Should pulse low for >10ms on power-up
   Then stay high during normal operation

5. Verify FPGA programming
   Re-flash Tang Nano with known-good bitstream
   Check LED blinks to confirm code running
```

**Solution:**
```lua
-- Add debug output
function fpga_debug()
    print("=== FPGA Debug ===")
    print("VCC:", measure_voltage(FPGA1_VCC))
    print("CLK:", gpio.read(GPIO0))
    print("CS:", gpio.read(GPIO3))
    print("RESET:", gpio.read(GPIO5))
    print("READY:", gpio.read(GPIO4))
    
    -- Try slower clock
    fpga_set_clock_speed(100000)  -- 100kHz instead of 10MHz
    print("Retry with slow clock...")
end
```

#### Issue 2: Level Shifter Not Working

**Symptoms:**
- 4000-series ICs don't respond
- Voltages on CMOS side are wrong (not 5V)

**Check:**
```
1. Level shifter power:
   - 74LVC245 pin 20: Should be 3.3V
   - 74LVC245 pin 10: Should be GND
   - 74LVC245 pin 1 (DIR): Check direction setting
   - 74LVC245 pin 19 (OE): Should be LOW (enabled)

2. For BSS138 shifters:
   - 10kΩ pullup to 5V on drain side
   - 10kΩ pullup to 3.3V on source side
   - Check MOSFET orientation (source/drain)

3. Voltage test points:
   ELM11 side: 3.3V when high
   CMOS side: 5.0V when high (4.5V - 5.5V acceptable)
```

**Solution - Replace with resistor divider (output only):**
```
For 3.3V → 5V (output from ELM11):
  Just connect directly! 4000-series accepts 3.3V as HIGH
  (VIH min = 3.5V at 5V supply, but typically works at 3.0V+)

For 5V → 3.3V (input to ELM11):
  Voltage divider:
  5V ─┬─ R1 (10kΩ) ─┬─ To ELM11 GPIO (3.3V max)
      │             │
      └─ R2 (15kΩ) ─┴─ GND
  
  Output = 5V × (15kΩ / 25kΩ) = 3V (safe!)
```

#### Issue 3: I2C Communication Failure

**Symptoms:**
- INA219 not responding
- i2c_address() returns false

**Check:**
```
1. Pullup resistors present?
   Measure resistance from SDA to 3.3V: Should be ~4.7kΩ
   Measure resistance from SCL to 3.3V: Should be ~4.7kΩ

2. Check I2C addresses with scanner:
```

```lua
function i2c_scan()
    print("Scanning I2C bus...")
    for addr = 0x00, 0x7F do
        i2c_start()
        if i2c_address(addr, I2C_WRITE) then
            print(string.format("Found device at 0x%02X", addr))
        end
        i2c_stop()
    end
end
```

```
3. Verify INA219 power:
   Pin 3 (VS+): Should be 3.3V
   Pin 4 (GND): Should be 0V

4. Check shunt resistor:
   Measure resistance: Should be ~0.1Ω
   Measure voltage across shunt: Should be < 100mV
   (If > 100mV, too much current = possible short)

5. Slow down I2C clock:
```

```lua
-- Try slower I2C speed
i2c_init(GPIO24, GPIO25, 10000)  -- 10kHz instead of 100kHz
```

#### Issue 4: Stochastic Results Incorrect

**Symptoms:**
- Multiplication gives wrong answer
- Results inconsistent between runs

**Check:**
```
1. LFSR initialization:
   - Must start with non-zero seed
   - Verify maximal-length polynomial
   - Check for stuck-at-zero condition

2. Bitstream length:
   - Too short (< 256 bits) = high variance
   - Verify counter wraps at correct length
   - Check for premature counter reset

3. Clock synchronization:
   - All LFSRs must use same clock
   - No clock skew between devices
   - Verify setup/hold times met

4. Gate propagation delay:
   - Add delay between clock cycles
   - Verify AND/MUX outputs stable before sampling
```

**Solution:**
```lua
function verify_stochastic_operation()
    -- Test with known values
    local test_cases = {
        {a=128, b=128, expected=64},   -- 0.5 × 0.5 = 0.25
        {a=192, b=128, expected=96},   -- 0.75 × 0.5 = 0.375
        {a=64,  b=128, expected=32},   -- 0.25 × 0.5 = 0.125
    }
    
    for _, test in ipairs(test_cases) do
        local result = stochastic_multiply(test.a, test.b)
        local error = math.abs(result - test.expected)
        local percent_error = (error / test.expected) * 100
        
        print(string.format(
            "Test: %d × %d = %d (expected %d, error %.1f%%)",
            test.a, test.b, result, test.expected, percent_error
        ))
        
        if percent_error > 10 then
            print("  ✗ FAIL - Error too high!")
            return false
        else
            print("  ✓ PASS")
        end
    end
    
    return true
end
```

#### Issue 5: Power Consumption Too High

**Symptoms:**
- CMOS circuit using more than 1mW
- Components getting warm

**Check:**
```
1. Oscillation / ringing on clock lines:
   - Check with oscilloscope
   - Look for overshoot > 20%
   - Add series resistor (47Ω) to dampen

2. Floating inputs:
   - All unused IC inputs must be tied high or low
   - Check CD40xx datasheet for each IC
   - Never leave CMOS inputs floating!

3. Multiple ICs driving same net:
   - Verify only one output drives each signal
   - Check for bus contention
   - Use tri-state or multiplexing

4. Power supply noise:
   - Verify decoupling caps installed
   - Check for ground loops
   - Add bulk capacitance (100µF)

5. Wrong voltage level:
   - CMOS power should be 5V, not more
   - Verify no overvoltage on any pin
```

**Solution:**
```
Tie off unused inputs:

CD4081 (Quad AND):
  - If only using 2 gates, tie unused inputs:
    Pin 5 → GND or VCC
    Pin 6 → GND or VCC
    Pin 8 → GND or VCC  (ensure pin 9 not floating)
    Pin 9 → See above
    Pin 12 → GND or VCC
    Pin 13 → GND or VCC

Repeat for all ICs with unused sections.
```

---

## Performance Optimization

### Maximize Throughput

**1. Pipeline Operations:**

```lua
-- Instead of sequential:
function slow_compute()
    fpga1_load(data1)
    fpga1_wait_ready()
    fpga1_read_result()
    
    fpga2_load(data2)
    fpga2_wait_ready()
    fpga2_read_result()
end

-- Use pipelined:
function fast_compute()
    fpga1_load(data1)
    fpga2_load(data2)  -- Start immediately, don't wait
    
    fpga1_wait_ready()
    result1 = fpga1_read_result()
    
    fpga2_wait_ready()  -- Already computing!
    result2 = fpga2_read_result()
end

-- Speedup: 2x
```

**2. Parallel Multi-Core:**

```lua
-- Core 0: Keep REPL responsive
function core0_repl()
    while true do
        cmd = get_command()
        ipc.send(1, cmd)  -- Non-blocking send
        -- REPL immediately ready for next command
    end
end

-- Core 2: Batch operations
function core2_compute()
    local job_queue = {}
    
    while true do
        -- Collect multiple jobs
        for i = 1, 8 do
            table.insert(job_queue, ipc.receive(1))
        end
        
        -- Execute batch on all hardware simultaneously
        execute_batch(job_queue)
    end
end

-- Throughput: 8x higher
```

**3. DMA-like Streaming:**

```lua
-- Stream continuous data without CPU polling
function stream_mode()
    -- Configure FPGA for autonomous operation
    fpga_set_mode(STREAM_MODE)
    
    -- FPGA generates bitstreams continuously
    -- Results stored in FIFO buffer
    -- ELM11 reads when convenient (no tight timing)
    
    while streaming do
        if fifo_available() > 128 then
            results = fifo_read_burst(128)
            process_results(results)
        end
        sleep(10)  -- Check every 10ms, not every cycle
    end
end

-- CPU usage: 10% instead of 100%
```

### Minimize Power

**1. Dynamic Frequency Scaling:**

```lua
function power_aware_compute(job)
    if job.priority == "low" then
        -- Use CMOS (ultra low power)
        -- Slow but efficient
        set_hardware(CMOS)
        set_clock(100000)  -- 100kHz
        
    elseif job.priority == "medium" then
        -- Use FPGA at low speed
        set_hardware(FPGA1)
        set_clock(1000000)  -- 1MHz
        
    else  -- high priority
        -- Use FPGA at full speed
        set_hardware(FPGA1)
        set_clock(27000000)  -- 27MHz
    end
    
    execute(job)
end
```

**2. Power Gating:**

```lua
function enable_hardware(device)
    if device == FPGA1 then
        gpio.write(GPIO_FPGA1_POWER_EN, 1)
        sleep(10)  -- Wait for power stable
    elseif device == CMOS then
        gpio.write(GPIO_CMOS_ENABLE, 1)
        sleep(1)   -- CMOS powers up faster
    end
end

function disable_hardware(device)
    if device == FPGA1 then
        gpio.write(GPIO_FPGA1_POWER_EN, 0)
        -- FPGA now consumes 0W!
    end
end

-- Power when idle: Near zero
-- Wake-up time: 10ms (acceptable for many applications)
```

**3. Adaptive Bitstream Length:**

```lua
function adaptive_precision(value, tolerance)
    -- Start with short bitstream
    local length = 64
    local result = compute_with_length(value, length)
    
    -- Increase length until within tolerance
    while math.abs(result - expected) > tolerance do
        length = length * 2
        result = compute_with_length(value, length)
        
        if length > 4096 then
            break  -- Maximum precision reached
        end
    end
    
    return result, length
end

-- Power saved: 2-8x for low-precision requirements
```

---

## Safety and Reliability

### Overcurrent Protection

```
Power Input → Fuse → Regulator → Load

Fuse ratings:
  - 5V rail: 2A fast-blow fuse
  - 3.3V rail: 1A fast-blow fuse

Protection circuitry:
┌──────────────────────────────┐
│  +5V Input                   │
│   │                          │
│  [Fuse 2A]                   │
│   │                          │
│  [TVS Diode] (transient)     │
│   │                          │
│  [7805 Regulator]            │
│   │                          │
│  [LED + Resistor] (indicator)│
│   │                          │
│   └─► To load                │
└──────────────────────────────┘
```

### ESD Protection

```
All external connections should have:

GPIO_x ─┬─ 100Ω ─┬─ To external device
        │        │
      [TVS]    [Schottky]
        │        │
       GND      GND

TVS: CDSOT23-SM712 (dual diode array)
Schottky: BAT54 (low capacitance)
```

### Thermal Management

```
Temperature monitoring:

function check_temperatures()
    -- Use internal ELM11 temp sensor
    local elm_temp = read_internal_temp()
    
    -- Estimate FPGA temp from power
    local fpga_power = ina219_read(0x40)
    local fpga_temp_est = 25 + (fpga_power / 10)  -- ~10mW per °C
    
    if elm_temp > 70 or fpga_temp_est > 85 then
        print("⚠ Temperature warning!")
        reduce_clock_speed()
        activate_cooling()
    end
end

-- Run every 10 seconds
```

---

## Expansion Options

### Adding More Devices

**Headers for future expansion:**

```
ELM11 Spare GPIOs (30-31):
┌───────────────────────────────┐
│  Expansion Header             │
│  Pin 1: +3.3V                 │
│  Pin 2: GPIO30                │
│  Pin 3: GPIO31                │
│  Pin 4: GND                   │
│  Pin 5: I2C SDA (shared)      │
│  Pin 6: I2C SCL (shared)      │
└───────────────────────────────┘

Possible expansions:
- Additional Tang Nano FPGAs (up to 4 total)
- SPI SRAM (external memory)
- SD card (data logging)
- OLED display (local visualization)
- WiFi module (remote access)
- CAN bus (automotive applications)
```

### Modular Design

```
Create pluggable modules:

┌─────────────────────┐
│  Base Board         │
│  - ELM11 socket     │
│  - Power regulation │
│  - Expansion slots  │
└─────────────────────┘
         │
    ┌────┴────┬────────┬────────┐
    │         │        │        │
┌───▼───┐ ┌──▼──┐ ┌───▼───┐ ┌──▼──┐
│ FPGA  │ │CMOS │ │ Analog│ │More │
│Module │ │Module│ │Module │ │...  │
└───────┘ └─────┘ └───────┘ └─────┘

Each module:
- Standard pinout (like Arduino shields)
- Auto-detection via I2C EEPROM
- Hot-swappable (with proper design)
```

---

## Documentation and Labeling

### Wire Labeling System

```
Use colored wires + labels:

Power:
  Red: +5V
  Orange: +3.3V
  Black: GND

Signals:
  Blue: Clock signals (CLK)
  Green: Data signals (MOSI, MISO)
  Yellow: Control signals (CS, EN)
  Purple: I2C (SDA, SCL)
  White: Analog signals
  
Label every wire with:
  "GPIO5→FPGA1_RST"
  "3.3V→IC5_VCC"
```

### Board Documentation

Print and laminate this reference card:

```
┌─────────────────────────────────────────────────────────────────┐
│         STOCHASTIC COMPUTING SYSTEM - QUICK REFERENCE           │
├─────────────────────────────────────────────────────────────────┤
│ ELM11 GPIO ASSIGNMENTS:                                         │
│  0-7:   Tang Nano #1 (3.3V)     16-23: 4000-CMOS (5V via LS)   │
│  8-15:  Tang Nano #2 (3.3V)     24-27: Analog/Power (3.3V)     │
│  28-31: Status LEDs              LS = Level Shifter Required   │
│                                                                 │
│ I2C ADDRESSES:                                                  │
│  0x40: INA219 #1 (FPGA1 power)  0x44: INA219 #3 (CMOS power)  │
│  0x41: INA219 #2 (FPGA2 power)  0x45: INA219 #4 (Total power) │
│                                                                 │
│ POWER REQUIREMENTS:                                             │
│  +5V @ 500mA max    +3.3V @ 300mA max    GND (common)          │
│                                                                 │
│ EMERGENCY SHUTDOWN:                                             │
│  Press RESET button OR disconnect USB power                    │
│                                                                 │
│ STATUS LEDS:                                                    │
│  Green: Heartbeat    Blue: FPGA active                          │
│  Yellow: CMOS active Red: Error/fault                           │
│                                                                 │
│ SUPPORT: github.com/aptitudetechnology/stochastic-REPL-core    │
└─────────────────────────────────────────────────────────────────┘
```

---

## Complete Wiring Example (Step-by-Step Photos Guide)

### Photo 1: Power Distribution

```
╔═══════════════════════════════════════════════════════════════╗
║  Step 1: Wire Power Rails                                     ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  Power Supply → [+5V Rail] ═════════════════════════════     ║
║                 [+3.3V Rail] ═══════════════════════════     ║
║                 [GND Rail] ═════════════════════════════     ║
║                                                               ║
║  1. Connect USB power to breadboard power module             ║
║  2. Verify voltages with multimeter                          ║
║     +5V rail: 4.8V - 5.2V acceptable                         ║
║     +3.3V rail: 3.2V - 3.4V acceptable                       ║
║  3. Install bulk capacitors (10µF) near regulators           ║
║  4. Test under no-load condition                             ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝
```

### Photo 2: ELM11 Placement

```
╔═══════════════════════════════════════════════════════════════╗
║  Step 2: Mount ELM11 Board                                    ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  ┌─────────────────┐                                         ║
║  │    ELM11        │                                         ║
║  │  [USB Port] ←───┼──── To computer                        ║
║  │                 │                                         ║
║  │  GPIO 0-15 ●●●● │                                         ║
║  │  GPIO16-31 ●●●● │                                         ║
║  └─────────────────┘                                         ║
║                                                               ║
║  1. Orient USB port toward edge of breadboard                ║
║  2. Insert GPIO headers into breadboard                      ║
║  3. Verify no short circuits (check with multimeter)         ║
║  4. Connect power:                                           ║
║     ELM11 VCC → +3.3V rail                                   ║
║     ELM11 GND → GND rail                                     ║
║  5. Install 10µF cap between VCC and GND near ELM11          ║
║  6. Power on and verify LED blinks                           ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝
```

### Photo 3: Tang Nano Connections

```
╔═══════════════════════════════════════════════════════════════╗
║  Step 3: Connect Tang Nano #1                                 ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  ELM11 GPIO0 ─[100Ω]─┬─────► Tang IO3 (CLK)                 ║
║  ELM11 GPIO1 ─[100Ω]─┼─────► Tang IO4 (MOSI)                ║
║  ELM11 GPIO2 ◄───────┼─────  Tang IO5 (MISO)                ║
║  ELM11 GPIO3 ─[100Ω]─┼─────► Tang IO6 (CS)                  ║
║  ELM11 GPIO4 ◄───────┼─────  Tang IO7 (READY)               ║
║  ELM11 GPIO5 ─[100Ω]─┼─────► Tang IO8 (RESET)               ║
║  ELM11 GPIO6 ─[100Ω]─┼─────► Tang IO9 (MODE0)               ║
║  ELM11 GPIO7 ─[100Ω]─┴─────► Tang IO10 (MODE1)              ║
║                                                               ║
║  Tang VCC ←────────── +3.3V rail                             ║
║  Tang GND ←────────── GND rail                               ║
║                                                               ║
║  Verification:                                               ║
║  ✓ All resistors in place (protect GPIOs)                    ║
║  ✓ 10µF cap between Tang VCC and GND                         ║
║  ✓ No crossed wires (double-check!)                          ║
║  ✓ Secure connections (push wires fully in)                  ║
║                                                               ║
║  Repeat for Tang Nano #2 with GPIO8-15                       ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝
```

### Photo 4: Level Shifter Installation

```
╔═══════════════════════════════════════════════════════════════╗
║  Step 4: Install Level Shifter (3.3V ↔ 5V)                   ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  Using 74LVC245 (recommended):                                ║
║                                                               ║
║         74LVC245 Pinout (DIP-20):                            ║
║  ┌──────────────────────────────────┐                        ║
║  │ DIR  1  ●  20  VCC (3.3V)       │                        ║
║  │ A1   2     19  OE (→GND)        │                        ║
║  │ A2   3     18  B8                │                        ║
║  │ A3   4     17  B7                │                        ║
║  │ A4   5     16  B6                │                        ║
║  │ A5   6     15  B5                │                        ║
║  │ A6   7     14  B4                │                        ║
║  │ A7   8     13  B3                │                        ║
║  │ A8   9     12  B2                │                        ║
║  │ GND 10     11  B1                │                        ║
║  └──────────────────────────────────┘                        ║
║     ↑ 3.3V side       ↑ 5V side                              ║
║                                                               ║
║  A-side: Connect to ELM11 GPIOs (16-23)                      ║
║  B-side: Connect to 4000-series ICs                          ║
║                                                               ║
║  Pin 1 (DIR): Tie to VCC or GND (set direction)             ║
║  Pin 19