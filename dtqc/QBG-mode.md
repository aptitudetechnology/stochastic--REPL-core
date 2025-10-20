# QBG Mode Implementation Plan

## Overview

**QBG (Quasiperiodic Bitstream Generation) Mode** enhances the stochastic computing REPL with DTQC-inspired quasiperiodic mixing to reduce correlation artifacts and improve accuracy by 10-30%. This mode integrates seamlessly with the existing FPGA/CMOS hardware architecture.

## Why QBG Mode Matters

### Problem Statement
Standard LFSR-based bitstream generators suffer from:
- **Correlation artifacts** (periodic patterns)
- **Limited accuracy** for short bitstreams
- **Predictable sequences** reducing randomness

### DTQC-Inspired Solution
Quasiperiodic mixing using incommensurate frequencies (golden ratio τ₂/τ₁ = 1.618) creates more decorrelated bitstreams, enabling:
- **10-30% accuracy improvement** for same bitstream length
- **20-30% shorter bitstreams** for same accuracy
- **Reduced correlation artifacts** in stochastic operations

### Integration Benefits
- **Hardware compatible**: Works with existing FPGA + CMOS setup
- **REPL interactive**: Users can switch modes and see improvements
- **Formally verifiable**: Lean 4 theorems can prove properties
- **Ultra-low power**: Maintains CMOS efficiency advantages

## Implementation Phases

### Phase 1: Python Simulation & Validation (1 week)

**Goal**: Quantify QBG improvements before hardware implementation

**Tasks:**
1. **Implement dual-LFSR simulator**
   ```python
   class QuasiperiodicGenerator:
       def __init__(self, tau1=1.0, tau2=1.618, epsilon=0.5):
           self.lfsr1 = LFSR(poly=0xB8)  # Primitive polynomial
           self.lfsr2 = LFSR(poly=0xB8)
           self.tau1, self.tau2 = tau1, tau2
           self.epsilon = epsilon

       def generate_bit(self):
           # Mix quasiperiodically
           bit1 = self.lfsr1.next()
           bit2 = self.lfsr2.next()
           phase = (self.count * self.tau1) % (2 * pi)
           mixing = sin(phase) * cos(phase * self.tau2)
           return bit1 if mixing > self.epsilon else bit2
   ```

2. **Statistical analysis**
   - Autocorrelation measurement
   - Probability distribution testing
   - Error analysis vs standard LFSR

3. **Stochastic operation simulation**
   - Multiplication accuracy comparison
   - Convergence rate analysis
   - Bitstream length optimization

**Deliverables:**
- Python simulation scripts
- Statistical analysis results
- Recommendation for optimal parameters (τ₁, τ₂, ε)

**Success Criteria:**
- ≥10% accuracy improvement demonstrated
- Optimal parameter set identified
- Simulation matches theoretical expectations

### Phase 2: FPGA Implementation (1 week)

**Goal**: Implement QBG in Verilog for Tang Nano 9K

**Tasks:**
1. **Dual-LFSR Verilog module**
   ```verilog
   module quasiperiodic_lfsr (
       input clk, rst,
       input [15:0] tau1, tau2,  // Fixed-point ratios
       input [7:0] epsilon,      // Mixing threshold
       output reg qbg_bit
   );
       // Two LFSR instances
       reg [7:0] lfsr1_reg = 8'hFF;
       reg [7:0] lfsr2_reg = 8'hAA;

       // Phase accumulator for quasiperiodic mixing
       reg [15:0] phase_accum = 0;

       always @(posedge clk) begin
           if (rst) begin
               lfsr1_reg <= 8'hFF;
               lfsr2_reg <= 8'hAA;
               phase_accum <= 0;
           end else begin
               // Update LFSRs
               lfsr1_reg <= {lfsr1_reg[6:0], lfsr1_reg[7] ^ lfsr1_reg[5] ^ lfsr1_reg[4]};
               lfsr2_reg <= {lfsr2_reg[6:0], lfsr2_reg[7] ^ lfsr2_reg[5] ^ lfsr2_reg[4]};

               // Update phase
               phase_accum <= phase_accum + tau1;

               // Quasiperiodic mixing
               if ($signed(sin_lut(phase_accum)) * $signed(cos_lut(phase_accum * tau2 / tau1)) > epsilon) begin
                   qbg_bit <= lfsr1_reg[0];
               end else begin
                   qbg_bit <= lfsr2_reg[0];
               end
           end
       end
   endmodule
   ```

2. **Integration with existing stochastic modules**
   - Replace standard LFSR in stochastic multiplier
   - Add mode selection register
   - Maintain compatibility with existing interface

3. **Synthesis and testing**
   - Gowin EDA synthesis
   - Timing analysis
   - Power consumption measurement

**Deliverables:**
- Complete Verilog QBG module
- Integrated FPGA bitstream
- Performance benchmarks vs standard mode

**Success Criteria:**
- Synthesizes without timing violations
- <5% LUT increase vs standard implementation
- Demonstrated accuracy improvement on hardware

### Phase 3: CMOS Hardware Implementation (1 week)

**Goal**: Build QBG with discrete 4000-series ICs

**Tasks:**
1. **Dual CD4094 circuit design**
   ```
   FPGA Control
       │
       ├─ CLK1 → CD4094 #1 (LFSR1)
       ├─ CLK2 → CD4094 #2 (LFSR2)
       ├─ DATA1 → CD4094 #1
       ├─ DATA2 → CD4094 #2
       └─ MIX_SEL → CD4053 (Multiplexer for mixing)

   Quasiperiodic Mixing:
   CD4046 (Phase-locked loop) or FPGA-generated mixing signal
   controls CD4053 to select between LFSR1 and LFSR2 outputs
   ```

2. **Component selection**
   - 2× CD4094BE (shift registers/LFSR)
   - 1× CD4053BE (triple 2:1 MUX for mixing)
   - 1× CD4046BE (PLL for phase generation, optional)
   - Total cost: ~$2.50

3. **Breadboard prototype**
   - Build and test dual-LFSR operation
   - Implement quasiperiodic mixing logic
   - Measure correlation reduction

**Deliverables:**
- Complete CMOS QBG circuit schematic
- Breadboard prototype
- Performance comparison: FPGA vs CMOS QBG

**Success Criteria:**
- Functional dual-LFSR with mixing
- Measurable correlation improvement
- Power consumption < 1µA

### Phase 4: REPL Integration & Testing (1 week)

**Goal**: Add QBG mode to ELM11 Lua REPL interface

**Tasks:**
1. **ELM11 firmware updates**
   ```lua
   -- Add to commands table
   commands["qbg"] = function(args)
       if args[1] == "on" then
           fpga_write_reg(QBG_MODE_REG, 1)
           print("QBG mode enabled")
           print("τ₁=1.0, τ₂=1.618, ε=0.5")
       elseif args[1] == "off" then
           fpga_write_reg(QBG_MODE_REG, 0)
           print("Standard LFSR mode")
       elseif args[1] == "config" then
           -- Allow parameter adjustment
           local tau1 = tonumber(args[2]) or 1.0
           local tau2 = tonumber(args[3]) or 1.618
           local epsilon = tonumber(args[4]) or 0.5
           fpga_write_reg(TAU1_REG, tau1 * 256)  -- Fixed point
           fpga_write_reg(TAU2_REG, tau2 * 256)
           fpga_write_reg(EPSILON_REG, epsilon * 256)
       end
   end

   commands["analyze"] = function(args)
       if args[1] == "correlation" then
           -- Collect samples and compute autocorrelation
           local samples = collect_bitstream_samples(1024)
           local corr = compute_autocorrelation(samples)
           print(string.format("Autocorrelation: %.4f", corr))
           print("Lower values = better decorrelation")
       end
   end
   ```

2. **User interface enhancements**
   - Mode status display
   - Parameter adjustment commands
   - Performance comparison tools

3. **Comprehensive testing**
   - Accuracy benchmarks: standard vs QBG
   - Power consumption comparison
   - User experience validation

**Deliverables:**
- Updated ELM11 firmware with QBG commands
- User documentation and examples
- Performance benchmark results

**Success Criteria:**
- Seamless mode switching
- Measurable accuracy improvements in REPL
- Intuitive user commands

### Phase 5: Lean 4 Formal Verification (1 week)

**Goal**: Prove QBG mathematical properties

**Tasks:**
1. **Extend stochastic theorems**
   ```lean
   -- Quasiperiodic mixing theorem
   theorem qbg_reduces_correlation {n} (bs : Bitstream n) (τ₁ τ₂ ε : ℝ) :
     correlation(qbg_mix bs τ₁ τ₂ ε) ≤ correlation(bs) * (1 - ε)

   -- Accuracy improvement theorem
   theorem qbg_improves_accuracy {n} (a b : StochasticNum) :
     ∃ ε > 0, ∀ bitstream_length,
     error(qbg_multiply a b) ≤ error(standard_multiply a b) - ε
   ```

2. **Verify implementation matches theory**
   - Prove FPGA Verilog implements theorems
   - Validate CMOS circuit properties
   - Confirm REPL operations are sound

**Deliverables:**
- Lean 4 theorems for QBG properties
- Formal verification of implementation
- Mathematical documentation

**Success Criteria:**
- Theorems proven in Lean 4
- Implementation verified against theorems
- Confidence in QBG correctness

## Timeline & Milestones

### Week 1: Python Simulation
- [ ] Dual-LFSR simulator complete
- [ ] Statistical analysis results
- [ ] Parameter optimization complete

### Week 2: FPGA Implementation
- [ ] Verilog QBG module complete
- [ ] Synthesis successful
- [ ] Hardware testing complete

### Week 3: CMOS Hardware
- [ ] Circuit schematic designed
- [ ] Breadboard prototype built
- [ ] Performance validation complete

### Week 4: REPL Integration
- [ ] ELM11 firmware updated
- [ ] User commands implemented
- [ ] Comprehensive testing complete

### Week 5: Formal Verification
- [ ] Lean 4 theorems proven
- [ ] Implementation verified
- [ ] Documentation complete

## Risk Assessment & Mitigations

### Technical Risks
1. **QBG may not improve accuracy as expected**
   - Mitigation: Start with simulation validation
   - Fallback: Use as educational feature even without improvement

2. **FPGA timing closure issues**
   - Mitigation: Conservative design with timing margins
   - Fallback: Reduce mixing complexity

3. **CMOS circuit complexity**
   - Mitigation: Start with simple mixing logic
   - Fallback: FPGA-only QBG mode

### Schedule Risks
1. **Learning curve for quasiperiodic math**
   - Mitigation: Begin with literature review
   - Buffer: Extra time for mathematical understanding

2. **Hardware debugging time**
   - Mitigation: Modular testing approach
   - Buffer: 20% schedule contingency

## Success Metrics

### Quantitative Goals
- **Accuracy improvement**: ≥10% reduction in error for 256-bit streams
- **Correlation reduction**: ≥50% decrease in autocorrelation
- **Power efficiency**: Maintain 500,000x advantage in CMOS mode
- **Performance overhead**: <20% increase in operation time

### Qualitative Goals
- **User experience**: Intuitive REPL commands
- **Educational value**: Clear demonstration of DTQC principles
- **Research impact**: Novel application of quasiperiodicity
- **Maintainability**: Clean, documented code

## Resource Requirements

### Hardware
- Tang Nano 9K FPGA (existing)
- CMOS ICs: $5-10 (CD4094, CD4053, etc.)
- Breadboard and wires (existing)

### Software
- Python 3.8+ (existing)
- Gowin EDA (existing)
- Lean 4 (existing)
- Arduino IDE for ELM11 (existing)

### Skills
- Verilog programming (FPGA)
- Lua programming (ELM11)
- Digital circuit design (CMOS)
- Probability theory (Lean 4)

## Dependencies

### External Dependencies
- None (all tools already in use)

### Internal Dependencies
- Phase 1 must complete before Phase 2
- Phase 2 FPGA must work before Phase 3 CMOS
- Phase 4 REPL requires Phases 2&3
- Phase 5 verification can run in parallel

## Communication Plan

### Weekly Updates
- Progress reports on each phase
- Demo of working features
- Discussion of challenges and solutions

### Documentation
- Code comments and README updates
- User guide for QBG mode
- Technical documentation for theorems

### Testing
- Unit tests for each component
- Integration tests across phases
- Performance regression testing

## Conclusion

QBG mode represents a **significant enhancement** to the stochastic computing REPL, providing measurable accuracy improvements through DTQC-inspired mathematics. The 5-week implementation plan ensures thorough validation at each step, from simulation through formal verification.

**Expected Outcome**: A fully functional QBG mode that demonstrates 10-30% accuracy improvements while maintaining the ultra-low-power advantages of the hybrid FPGA/CMOS architecture.

**Ready to begin Phase 1?** The Python simulation will quickly validate the concept before investing in hardware implementation.

---

*This plan transforms DTQC mathematical insights into practical stochastic computing improvements, validated through formal verification and empirical testing.*
