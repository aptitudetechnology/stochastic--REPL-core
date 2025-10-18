# Stochastic Computing Hardware Setup - Photo Descriptions for Google Gemini

## System Block Diagram

```mermaid
graph TB
    A[Computer USB] --> B[ELM11 Microcontroller]
    B --> C[Tang Nano 9K FPGA #1]
    B --> D[Tang Nano 9K FPGA #2]
    B --> E[4000-Series CMOS ICs]
    B --> F[Analog Circuits]

    C --> G[Stochastic Computing]
    D --> G
    E --> G

    F --> H[Power Monitoring]
    G --> I[UART REPL Interface]

    style A fill:#e1f5fe
    style B fill:#f3e5f5
    style C fill:#e8f5e8
    style D fill:#e8f5e8
    style E fill:#fff3e0
    style G fill:#ffebee
    style I fill:#f3e5f5
```

## Photo 1: Power Distribution Setup

**Description for Image Generation:**
Create a detailed photograph of a breadboard setup showing power distribution for a stochastic computing system. Show a large solderless breadboard with red, blue, and black power rails clearly visible. The +5V rail should be connected to a USB power supply or voltage regulator, the +3.3V rail should show a voltage regulator circuit, and the GND rail should be connected to the power supply ground. Include several 10µF electrolytic capacitors placed near the power rails for decoupling. Show jumper wires connecting the power rails to various points on the breadboard. Include a digital multimeter measuring the voltage on the +5V rail, showing a reading around 5.0V. The breadboard should be clean and well-organized with no components yet installed, just the power infrastructure. Use realistic lighting and focus on the power rails and connections.

**Key Elements to Include:**
- Large solderless breadboard (830-point or similar)
- Red stripe for +5V rail, blue/black for GND rails
- USB power input or 7805 voltage regulator
- AMS1117-3.3 or similar 3.3V regulator
- Multiple 10µF capacitors on power rails
- Multimeter displaying voltage measurement
- Clean, professional wiring with no shorts

```mermaid
graph TD
    A[USB Power Supply<br/>5V 2A] --> B[7805 Regulator]
    B --> C[+5V Rail<br/>Red Stripe]
    A --> D[AMS1117-3.3]
    D --> E[+3.3V Rail<br/>Orange Stripe]
    A --> F[GND Rail<br/>Blue/Black Stripes]

    C --> G[10µF Caps<br/>Decoupling]
    E --> H[10µF Caps<br/>Decoupling]
    F --> I[10µF Caps<br/>Decoupling]

    J[Multimeter<br/>5.02V] --> C

    style A fill:#4caf50
    style C fill:#f44336
    style E fill:#ff9800
    style F fill:#2196f3
```

## Photo 2: ELM11 Board Placement

**Description for Image Generation:**
Create a detailed photograph showing an ELM11 microcontroller board mounted on a breadboard. The ELM11 should be oriented with its USB port facing the edge of the breadboard for easy access. Show the 32 GPIO pins (divided into banks 0-3) inserted into the breadboard sockets. Include power connections: a red wire from the ELM11 VCC pin to the +3.3V power rail, and a black wire from GND to the ground rail. Add a 10µF decoupling capacitor between VCC and GND pins on the ELM11. Show the board's status LEDs (if visible) and the USB connector clearly. The breadboard should have the power rails established from Photo 1. Include a small ruler or measurement reference to show scale. Use realistic lighting showing the components clearly.

**Key Elements to Include:**
- ELM11 board with RISC-V processors and Lua firmware
- USB port oriented toward breadboard edge
- 32 GPIO header pins inserted into breadboard
- Red wire: ELM11 VCC → +3.3V rail
- Black wire: ELM11 GND → GND rail
- 10µF capacitor near ELM11 power pins
- Clean breadboard with established power rails
- Professional component placement

```mermaid
graph TD
    A[ELM11 Board] --> B[USB Port<br/>→ Computer]
    A --> C[GPIO Bank 0<br/>0-7 → FPGA1]
    A --> D[GPIO Bank 1<br/>8-15 → FPGA2]
    A --> E[GPIO Bank 2<br/>16-23 → CMOS]
    A --> F[GPIO Bank 3<br/>24-31 → Analog]

    A --> G[VCC Pin<br/>Red Wire]
    G --> H[+3.3V Rail]
    A --> I[GND Pin<br/>Black Wire]
    I --> J[GND Rail]

    K[10µF Cap] --> G
    K --> I

    L[Status LEDs<br/>Green/Blue/Yellow/Red] --> A

    style A fill:#9c27b0
    style B fill:#4caf50
    style H fill:#ff9800
    style J fill:#2196f3
```

## Photo 3: Tang Nano FPGA Connections

**Description for Image Generation:**
Create a detailed photograph showing a Tang Nano 9K FPGA board connected to an ELM11 microcontroller via GPIO wires. Show 8 signal wires connecting ELM11 GPIO pins 0-7 to Tang Nano IO pins 3-10. Include 100 ohm current-limiting resistors on each output line from ELM11 (GPIO0,1,3,5,6,7). Show bidirectional connections without resistors for input lines (GPIO2,4). Include power connections: red wire from +3.3V rail to Tang Nano VCC, black wire to GND. Add a 10µF decoupling capacitor near the Tang Nano power pins. Show wire labels or color coding indicating the signal names (CLK, MOSI, MISO, CS, READY, RESET, MODE0, MODE1). The ELM11 should be mounted as in Photo 2. Use close-up photography to clearly show the connections and components.

**Key Elements to Include:**
- Tang Nano 9K FPGA board with GW1NR-9 FPGA chip
- ELM11 board with GPIO connections
- 8 jumper wires with 100Ω resistors on outputs
- Color-coded wires indicating signal functions
- Power connections with decoupling capacitor
- Professional wiring with strain relief
- Clear visibility of both boards and connections
- Close-up view showing pin connections

```mermaid
graph TD
    A[ELM11 GPIO 0-7] --> B[100Ω Resistor]
    B --> C[Tang Nano IO3<br/>CLK]

    A --> D[100Ω Resistor]
    D --> E[Tang Nano IO4<br/>MOSI]

    A --> F[Tang Nano IO5<br/>MISO]

    A --> G[100Ω Resistor]
    G --> H[Tang Nano IO6<br/>CS]

    A --> I[Tang Nano IO7<br/>READY]

    A --> J[100Ω Resistor]
    J --> K[Tang Nano IO8<br/>RESET]

    A --> L[100Ω Resistor]
    L --> M[Tang Nano IO9<br/>MODE0]

    A --> N[100Ω Resistor]
    N --> O[Tang Nano IO10<br/>MODE1]

    P[+3.3V Rail] --> Q[Tang Nano VCC]
    R[GND Rail] --> S[Tang Nano GND]

    T[10µF Cap] --> Q
    T --> S

    style A fill:#9c27b0
    style C fill:#4caf50
    style E fill:#4caf50
    style F fill:#2196f3
    style H fill:#4caf50
    style I fill:#2196f3
    style K fill:#4caf50
    style M fill:#4caf50
    style O fill:#4caf50
    style Q fill:#ff9800
    style S fill:#2196f3
```

## Photo 4: Level Shifter Installation

**Description for Image Generation:**
Create a detailed photograph showing a 74LVC245 level shifter IC installed on a breadboard, bridging 3.3V and 5V logic levels. Show the DIP-20 package inserted into the breadboard with clear pin numbering visible. Include connections from ELM11 GPIO pins 16-23 (A-side) to the level shifter A-pins (1-8), and from level shifter B-pins (11-18) to 4000-series CMOS IC pins. Show the direction control: pin 1 (DIR) tied to VCC for A-to-B translation. Show pin 19 (OE) tied to GND for always-enabled operation. Include power connections: pin 20 (VCC) to +3.3V rail, pin 10 (GND) to ground. Show a 4000-series CMOS IC (like CD4081) connected to the B-side outputs. Include decoupling capacitors near power pins. Use detailed, close-up photography to show the IC pin connections clearly.

**Key Elements to Include:**
- 74LVC245 level shifter in DIP-20 package
- Clear pin numbering and orientation
- A-side connections to ELM11 GPIOs (3.3V logic)
- B-side connections to CMOS ICs (5V logic)
- Direction control pin tied appropriately
- Power and ground connections
- 4000-series CMOS IC connected to outputs
- Decoupling capacitors
- Professional component placement and wiring
- Close-up view showing IC details

```mermaid
graph TD
    A[ELM11 GPIO 16-23<br/>3.3V Logic] --> B[74LVC245<br/>A-side pins 1-8]

    B --> C[74LVC245<br/>B-side pins 11-18]
    C --> D[4000-Series CMOS IC<br/>CD4081, CD4053, etc.]

    E[+3.3V Rail] --> F[74LVC245 Pin 20<br/>VCC]
    G[GND Rail] --> H[74LVC245 Pin 10<br/>GND]

    E --> I[74LVC245 Pin 1<br/>DIR = High<br/>A→B direction]
    G --> J[74LVC245 Pin 19<br/>OE = Low<br/>Always enabled]

    K[10µF Cap] --> F
    K --> H

    style A fill:#9c27b0
    style B fill:#ff9800
    style C fill:#ff5722
    style D fill:#795548
    style F fill:#ff9800
    style H fill:#2196f3
```

## GPIO Pin Mapping Summary

```mermaid
graph LR
    subgraph "ELM11 GPIO Banks"
        A0[GPIO 0-7<br/>Tang Nano #1]
        A1[GPIO 8-15<br/>Tang Nano #2]
        A2[GPIO 16-23<br/>4000-CMOS]
        A3[GPIO 24-27<br/>Analog/Power]
        A4[GPIO 28-31<br/>Status LEDs]
    end

    subgraph "Signal Types"
        B0[Outputs<br/>100Ω protected]
        B1[Inputs<br/>Direct]
        B2[Bidirectional<br/>I2C/SPI]
        B3[LEDs<br/>Direct drive]
    end

    A0 --> B0
    A0 --> B1
    A1 --> B0
    A1 --> B1
    A2 --> B0
    A2 --> B1
    A3 --> B2
    A4 --> B3

    style A0 fill:#e8f5e8
    style A1 fill:#e8f5e8
    style A2 fill:#fff3e0
    style A3 fill:#fce4ec
    style A4 fill:#f3e5f5
```

## Complete System Wiring Flow

```mermaid
flowchart TD
    A[Start Setup] --> B[Photo 1: Power Distribution]
    B --> C[Photo 2: ELM11 Placement]
    C --> D[Photo 3: Tang Nano #1 Connections]
    D --> E[Photo 3: Tang Nano #2 Connections]
    E --> F[Photo 4: Level Shifter Installation]
    F --> G[4000-Series CMOS IC Connections]
    G --> H[System Testing]
    H --> I[REPL Interface Ready]

    style A fill:#4caf50
    style I fill:#4caf50
```
