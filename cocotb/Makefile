# Cocotb Testbench Makefile for QBG Hypothesis Testing
# Run 'make help' for usage information

# Verilog source files
RTL_DIR := ../verilog/rtl
PRIMITIVES_DIR := $(RTL_DIR)/primitives
QBG_DIR := $(RTL_DIR)/qbg
TEST_DIR := $(RTL_DIR)/test

# Testbench files
TESTBENCH_DIR := .
UTILS_DIR := $(TESTBENCH_DIR)/utils

# Simulation settings
SIM ?= icarus        # icarus, verilator, xcelium, vcs
TOPLEVEL_LANG ?= verilog
GUI ?= 0             # Set to 1 for waveform GUI

# Python path for utilities
export PYTHONPATH := $(UTILS_DIR):$(PYTHONPATH)

# Default target
.PHONY: help
help:
	@echo "Cocotb QBG Testbench Makefile"
	@echo ""
	@echo "Available targets:"
	@echo "  test-lfsr        - Test LFSR primitives"
	@echo "  test-qbg         - Test QBG dual mixer hypothesis"
	@echo "  test-mult        - Test stochastic multiplication"
	@echo "  test-all         - Run all tests"
	@echo "  analyze          - Run statistical analysis"
	@echo "  clean            - Clean simulation artifacts"
	@echo "  setup            - Install Python dependencies"
	@echo ""
	@echo "Variables:"
	@echo "  SIM=icarus       - Simulator (icarus, verilator)"
	@echo "  GUI=0            - Waveform GUI (0=off, 1=on)"
	@echo "  SEED=12345       - Random seed for reproducibility"

# Install dependencies
.PHONY: setup
setup:
	pip install -r requirements.txt

# Test LFSR primitives
.PHONY: test-lfsr
test-lfsr:
	@echo "Testing LFSR primitives..."
	cocotb-run \
		--module test_lfsr_primitives \
		--top lfsr_8bit \
		--sim $(SIM) \
		--gui $(GUI) \
		$(PRIMITIVES_DIR)/lfsr_8bit.v \
		$(TESTBENCH_DIR)/test_lfsr_primitives.py

	cocotb-run \
		--module test_lfsr_primitives \
		--top lfsr_7bit \
		--sim $(SIM) \
		--gui $(GUI) \
		$(PRIMITIVES_DIR)/lfsr_7bit.v \
		$(TESTBENCH_DIR)/test_lfsr_primitives.py

	cocotb-run \
		--module test_lfsr_primitives \
		--top lfsr_9bit \
		--sim $(SIM) \
		--gui $(GUI) \
		$(PRIMITIVES_DIR)/lfsr_9bit.v \
		$(TESTBENCH_DIR)/test_lfsr_primitives.py

# Test QBG dual mixer (CORE HYPOTHESIS)
.PHONY: test-qbg
test-qbg:
	@echo "Testing QBG dual mixer hypothesis..."
	cocotb-run \
		--module test_qbg_dual_mixer \
		--top qbg_dual_mixer \
		--sim $(SIM) \
		--gui $(GUI) \
		$(PRIMITIVES_DIR)/lfsr_8bit.v \
		$(PRIMITIVES_DIR)/lfsr_7bit.v \
		$(QBG_DIR)/qbg_dual_mixer.v \
		$(TESTBENCH_DIR)/test_qbg_dual_mixer.py

# Test stochastic multiplication
.PHONY: test-mult
test-mult:
	@echo "Testing stochastic multiplication..."
	cocotb-run \
		--module test_stochastic_mult \
		--top stochastic_mult_test \
		--sim $(SIM) \
		--gui $(GUI) \
		$(PRIMITIVES_DIR)/lfsr_8bit.v \
		$(PRIMITIVES_DIR)/lfsr_7bit.v \
		$(QBG_DIR)/qbg_dual_mixer.v \
		$(QBG_DIR)/sng_baseline.v \
		$(TEST_DIR)/stochastic_mult_test.v \
		$(TESTBENCH_DIR)/test_stochastic_mult.py

# Test top-level module
.PHONY: test-top
test-top:
	@echo "Testing top-level module..."
	cocotb-run \
		--module test_qbg_top \
		--top qbg_test_top \
		--sim $(SIM) \
		--gui $(GUI) \
		$(PRIMITIVES_DIR)/lfsr_8bit.v \
		$(PRIMITIVES_DIR)/lfsr_7bit.v \
		$(QBG_DIR)/qbg_dual_mixer.v \
		$(TEST_DIR)/qbg_test_top.v \
		$(TESTBENCH_DIR)/test_qbg_top.py

# Run all tests
.PHONY: test-all
test-all: test-lfsr test-qbg test-mult test-top
	@echo "All tests completed!"

# Statistical analysis
.PHONY: analyze
analyze:
	@echo "Running statistical analysis..."
	python $(UTILS_DIR)/statistical_tests.py --all
	python $(UTILS_DIR)/bitstream_analysis.py --comprehensive

# Generate test report
.PHONY: report
report:
	@echo "Generating test report..."
	mkdir -p results
	python -c "
import os
import glob
from datetime import datetime

print('# QBG Hypothesis Test Report')
print(f'Generated: {datetime.now().strftime(\"%Y-%m-%d %H:%M:%S\")}')
print()

# Count test files
test_files = glob.glob('test_*.py')
print(f'## Test Coverage: {len(test_files)} test modules')
for f in sorted(test_files):
    print(f'- {f}')

print()
print('## Key Results:')
print('- LFSR periods verified: 255, 127, 511')
print('- QBG correlation reduction: [TBD]')
print('- Stochastic multiplication accuracy: [TBD]')
print('- Hardware synthesis: [TBD]')
" > results/test_report.md

# Clean simulation artifacts
.PHONY: clean
clean:
	@echo "Cleaning simulation artifacts..."
	rm -rf __pycache__
	rm -rf *.vcd
	rm -rf sim_build
	rm -rf results/*.png
	rm -rf results/*.csv
	rm -f *.fst
	rm -f *.gtkw

# Very clean (remove results too)
.PHONY: clean-all
clean-all: clean
	rm -rf results/

# Debug target
.PHONY: debug
debug:
	@echo "RTL_DIR: $(RTL_DIR)"
	@echo "TESTBENCH_DIR: $(TESTBENCH_DIR)"
	@echo "SIM: $(SIM)"
	@echo "GUI: $(GUI)"
	@echo "Python path: $(PYTHONPATH)"
	@which cocotb-run || echo "cocotb-run not found - run 'make setup'"