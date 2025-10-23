Here's the minimal Verilog for your QBG hypothesis testing:

## Core QBG Modules

### 1. LFSR Primitives (Reusable)

```verilog
// rtl/primitives/lfsr_8bit.v
// 8-bit maximal-length LFSR (period = 255)
// Polynomial: x^8 + x^6 + x^5 + x^4 + 1

module lfsr_8bit (
    input wire clk,
    input wire reset,
    input wire enable,
    output wire [7:0] data,
    output wire data_valid
);
    reg [7:0] lfsr_reg;
    
    // Polynomial taps: bits 7, 5, 4, 3
    wire feedback = lfsr_reg[7] ^ lfsr_reg[5] ^ lfsr_reg[4] ^ lfsr_reg[3];
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            lfsr_reg <= 8'hAC;  // Non-zero seed (avoid all-zeros lock)
        end else if (enable) begin
            lfsr_reg <= {lfsr_reg[6:0], feedback};
        end
    end
    
    assign data = lfsr_reg;
    assign data_valid = (lfsr_reg != 8'h00);  // Sanity check
    
endmodule
```

```verilog
// rtl/primitives/lfsr_7bit.v
// 7-bit maximal-length LFSR (period = 127)
// Polynomial: x^7 + x^6 + 1
// INCOMMENSURATE with 8-bit (127 and 255 are coprime)

module lfsr_7bit (
    input wire clk,
    input wire reset,
    input wire enable,
    output wire [6:0] data,
    output wire data_valid
);
    reg [6:0] lfsr_reg;
    
    // Polynomial taps: bits 6, 5
    wire feedback = lfsr_reg[6] ^ lfsr_reg[5];
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            lfsr_reg <= 7'h55;  // Non-zero seed
        end else if (enable) begin
            lfsr_reg <= {lfsr_reg[5:0], feedback};
        end
    end
    
    assign data = lfsr_reg;
    assign data_valid = (lfsr_reg != 7'h00);
    
endmodule
```

```verilog
// rtl/primitives/lfsr_9bit.v
// 9-bit maximal-length LFSR (period = 511)
// Polynomial: x^9 + x^5 + 1
// For 3-LFSR testing (H₅)

module lfsr_9bit (
    input wire clk,
    input wire reset,
    input wire enable,
    output wire [8:0] data,
    output wire data_valid
);
    reg [8:0] lfsr_reg;
    
    // Polynomial taps: bits 8, 4
    wire feedback = lfsr_reg[8] ^ lfsr_reg[4];
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            lfsr_reg <= 9'h1A5;  // Non-zero seed
        end else if (enable) begin
            lfsr_reg <= {lfsr_reg[7:0], feedback};
        end
    end
    
    assign data = lfsr_reg;
    assign data_valid = (lfsr_reg != 9'h000);
    
endmodule
```

### 2. QBG Mixer (YOUR HYPOTHESIS - Novel Contribution)

```verilog
// rtl/qbg/qbg_dual_mixer.v
// Quasiperiodic Bitstream Generator with dual-LFSR mixing
// Tests H₂: Does quasiperiodic mixing reduce correlation?

module qbg_dual_mixer (
    input wire clk,
    input wire reset,
    input wire [7:0] value,          // P(A) as 8-bit unsigned (0-255 → 0.0-1.0)
    input wire [1:0] mixing_mode,    // 00=single, 01=dual-simple, 10=dual-weighted, 11=dual-xor
    output reg bitstream_out,
    output wire [7:0] debug_lfsr1,   // For verification
    output wire [6:0] debug_lfsr2
);

    // Instantiate two LFSRs with incommensurate periods
    wire [7:0] lfsr1_data;
    wire [6:0] lfsr2_data;
    
    lfsr_8bit lfsr1 (
        .clk(clk),
        .reset(reset),
        .enable(1'b1),
        .data(lfsr1_data),
        .data_valid()
    );
    
    lfsr_7bit lfsr2 (
        .clk(clk),
        .reset(reset),
        .enable(1'b1),
        .data(lfsr2_data),
        .data_valid()
    );
    
    // Debug outputs
    assign debug_lfsr1 = lfsr1_data;
    assign debug_lfsr2 = lfsr2_data;
    
    // Mixing logic - THE CORE HYPOTHESIS
    reg [7:0] mixed_value;
    
    always @(*) begin
        case (mixing_mode)
            2'b00: begin
                // Single LFSR baseline (control)
                mixed_value = lfsr1_data;
            end
            
            2'b01: begin
                // Simple average mixing (equal weight)
                // Extend lfsr2 to 8 bits, then average
                mixed_value = (lfsr1_data + {1'b0, lfsr2_data}) >> 1;
            end
            
            2'b10: begin
                // Golden ratio weighted mixing (φ ≈ 1.618)
                // Approximate φ/(1+φ) ≈ 0.618 using 158/256
                // and 1/(1+φ) ≈ 0.382 using 98/256
                wire [15:0] weighted_sum;
                assign weighted_sum = (lfsr1_data * 8'd158) + ({1'b0, lfsr2_data} * 8'd98);
                mixed_value = weighted_sum[15:8];  // Take upper 8 bits (divide by 256)
            end
            
            2'b11: begin
                // XOR mixing (alternative decorrelation method)
                mixed_value = lfsr1_data ^ {1'b0, lfsr2_data};
            end
            
            default: mixed_value = lfsr1_data;
        endcase
    end
    
    // Stochastic comparison: output 1 if mixed_value < threshold
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            bitstream_out <= 1'b0;
        end else begin
            bitstream_out <= (mixed_value < value);
        end
    end
    
endmodule
```

### 3. Three-LFSR Mixer (For H₅ Testing)

```verilog
// rtl/qbg/qbg_triple_mixer.v
// Three-LFSR quasiperiodic mixer
// Tests H₅: Does 3-LFSR beat 2-LFSR for long bitstreams?

module qbg_triple_mixer (
    input wire clk,
    input wire reset,
    input wire [7:0] value,
    output reg bitstream_out,
    output wire [7:0] debug_lfsr1,
    output wire [6:0] debug_lfsr2,
    output wire [8:0] debug_lfsr3
);

    wire [7:0] lfsr1_data;
    wire [6:0] lfsr2_data;
    wire [8:0] lfsr3_data;
    
    // Three incommensurate periods: 255, 127, 511
    lfsr_8bit lfsr1 (.clk(clk), .reset(reset), .enable(1'b1), .data(lfsr1_data), .data_valid());
    lfsr_7bit lfsr2 (.clk(clk), .reset(reset), .enable(1'b1), .data(lfsr2_data), .data_valid());
    lfsr_9bit lfsr3 (.clk(clk), .reset(reset), .enable(1'b1), .data(lfsr3_data), .data_valid());
    
    assign debug_lfsr1 = lfsr1_data;
    assign debug_lfsr2 = lfsr2_data;
    assign debug_lfsr3 = lfsr3_data;
    
    // Three-way mixing with approximate equal weights (85 each ≈ 256/3)
    wire [15:0] sum;
    assign sum = (lfsr1_data * 8'd85) + 
                 ({1'b0, lfsr2_data} * 8'd85) + 
                 (lfsr3_data[7:0] * 8'd85);  // Truncate lfsr3 to 8 bits
    
    wire [7:0] mixed_value;
    assign mixed_value = sum[15:8];
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            bitstream_out <= 1'b0;
        end else begin
            bitstream_out <= (mixed_value < value);
        end
    end
    
endmodule
```

### 4. Baseline Single-LFSR SNG (Control)

```verilog
// rtl/qbg/sng_baseline.v
// Standard single-LFSR Stochastic Number Generator
// Control condition for H₂ testing

module sng_baseline (
    input wire clk,
    input wire reset,
    input wire [7:0] value,
    output reg bitstream_out,
    output wire [7:0] debug_lfsr
);

    wire [7:0] lfsr_data;
    
    lfsr_8bit lfsr (
        .clk(clk),
        .reset(reset),
        .enable(1'b1),
        .data(lfsr_data),
        .data_valid()
    );
    
    assign debug_lfsr = lfsr_data;
    
    // Standard stochastic comparison
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            bitstream_out <= 1'b0;
        end else begin
            bitstream_out <= (lfsr_data < value);
        end
    end
    
endmodule
```

### 5. Test Harness (Stochastic Multiplication)

```verilog
// rtl/test/stochastic_mult_test.v
// Test harness for H₂ validation
// Computes A × B using stochastic multiplication (AND gate)

module stochastic_mult_test (
    input wire clk,
    input wire reset,
    input wire [7:0] value_a,        // P(A)
    input wire [7:0] value_b,        // P(B)
    input wire [1:0] mode,           // Which generator to test
    input wire start,
    input wire [15:0] num_bits,      // Bitstream length (e.g., 256)
    output reg [15:0] ones_count,    // Number of 1s in result
    output reg done,
    output wire [7:0] debug_stream_a,
    output wire [7:0] debug_stream_b
);

    // Generate two bitstreams
    wire bitstream_a, bitstream_b;
    
    generate
        if (1) begin : gen_mode_select
            // Choose generator based on mode
            case (mode)
                2'b00: begin  // Baseline single-LFSR
                    sng_baseline sng_a (.clk(clk), .reset(reset), .value(value_a), 
                                       .bitstream_out(bitstream_a), .debug_lfsr(debug_stream_a));
                    sng_baseline sng_b (.clk(clk), .reset(reset), .value(value_b), 
                                       .bitstream_out(bitstream_b), .debug_lfsr(debug_stream_b));
                end
                
                2'b01: begin  // Dual-LFSR QBG
                    qbg_dual_mixer qbg_a (.clk(clk), .reset(reset), .value(value_a), 
                                         .mixing_mode(2'b01), .bitstream_out(bitstream_a),
                                         .debug_lfsr1(debug_stream_a), .debug_lfsr2());
                    qbg_dual_mixer qbg_b (.clk(clk), .reset(reset), .value(value_b), 
                                         .mixing_mode(2'b01), .bitstream_out(bitstream_b),
                                         .debug_lfsr1(debug_stream_b), .debug_lfsr2());
                end
                
                // Add more modes as needed
            endcase
        end
    endgenerate
    
    // Stochastic multiplication: AND gate
    wire product_bit;
    assign product_bit = bitstream_a & bitstream_b;
    
    // Count ones over num_bits cycles
    reg [15:0] bit_counter;
    reg running;
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            bit_counter <= 16'd0;
            ones_count <= 16'd0;
            running <= 1'b0;
            done <= 1'b0;
        end else begin
            if (start && !running) begin
                running <= 1'b1;
                bit_counter <= 16'd0;
                ones_count <= 16'd0;
                done <= 1'b0;
            end else if (running) begin
                bit_counter <= bit_counter + 16'd1;
                if (product_bit) begin
                    ones_count <= ones_count + 16'd1;
                end
                
                if (bit_counter >= num_bits - 16'd1) begin
                    running <= 1'b0;
                    done <= 1'b1;
                end
            end
        end
    end
    
endmodule
```

### 6. Top-Level Test Module

```verilog
// rtl/test/qbg_test_top.v
// Top-level module for Tang Nano 9K
// Maps to physical pins for hardware testing

module qbg_test_top (
    input wire clk,              // 27 MHz on-board oscillator
    input wire reset_btn,        // S2 button (active low)
    input wire [7:0] value_in,   // DIP switches or buttons
    output wire bitstream_led,   // Visual output
    output wire test_pin_out,    // For oscilloscope/logic analyzer
    output wire [2:0] debug_leds // RGB LED
);

    // Debounce reset
    reg reset_sync;
    reg reset;
    always @(posedge clk) begin
        reset_sync <= ~reset_btn;  // Active low button
        reset <= reset_sync;
    end
    
    // Instantiate QBG mixer
    wire bitstream;
    wire [7:0] debug_lfsr1;
    wire [6:0] debug_lfsr2;
    
    qbg_dual_mixer qbg (
        .clk(clk),
        .reset(reset),
        .value(value_in),
        .mixing_mode(2'b01),  // Simple averaging mode
        .bitstream_out(bitstream),
        .debug_lfsr1(debug_lfsr1),
        .debug_lfsr2(debug_lfsr2)
    );
    
    // Outputs
    assign bitstream_led = bitstream;
    assign test_pin_out = bitstream;
    
    // Debug: Show LFSR activity on RGB LED
    assign debug_leds[0] = debug_lfsr1[0];  // Green
    assign debug_leds[1] = debug_lfsr2[0];  // Blue  
    assign debug_leds[2] = bitstream;       // Red
    
endmodule
```

## File Summary

```
rtl/
├── primitives/
│   ├── lfsr_8bit.v       (35 lines) - Period 255
│   ├── lfsr_7bit.v       (35 lines) - Period 127 (incommensurate)
│   └── lfsr_9bit.v       (35 lines) - Period 511 (for 3-LFSR)
├── qbg/
│   ├── qbg_dual_mixer.v  (90 lines) - YOUR HYPOTHESIS ★
│   ├── qbg_triple_mixer.v(60 lines) - For H₅ testing
│   └── sng_baseline.v    (30 lines) - Control condition
└── test/
    ├── stochastic_mult_test.v (80 lines) - Test harness
    └── qbg_test_top.v        (40 lines) - Tang Nano 9K top-level
```

**Total novel code**: ~405 lines of Verilog  
**Core hypothesis code**: ~90 lines (qbg_dual_mixer.v)

## Key Design Decisions

1. **Multiple mixing modes** (2'b00 to 2'b11) let you test different strategies in hardware without resynthesis
2. **Debug outputs** expose internal LFSR state for verification
3. **Parameterizable test harness** allows running multiple trials on FPGA
4. **Simple golden ratio approximation** (158/256, 98/256) avoids floating-point
5. **All synchronous design** for reliable synthesis

## Next Steps

1. **Simulate first**: Use cocotb to verify this matches your Python reference
2. **Synthesize**: Run `make synth` to check resource usage
3. **Measure**: Program Tang Nano 9K and capture bitstreams with logic analyzer

Would you like:
1. **Cocotb testbench** to verify this Verilog?
2. **Python reference implementation** to compare against?
3. **Synthesis script** tuned for these specific modules?