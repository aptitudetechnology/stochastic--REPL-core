#!/usr/bin/env python3
"""
Comprehensive accuracy testing for stochastic computing operations.
Tests multiplication and addition across various input ranges and stream lengths.
"""

import random
import numpy as np
from dataclasses import dataclass
from typing import List, Tuple
import matplotlib.pyplot as plt

@dataclass
class TestResult:
    """Store results from a single test."""
    operation: str
    input_a: float
    input_b: float
    expected: float
    computed: float
    error: float
    stream_length: int

class StochasticSimulator:
    """Software simulator for stochastic computing operations."""
    
    @staticmethod
    def generate_bitstream(value: float, length: int, seed: int = None) -> List[int]:
        """Generate stochastic bitstream for a value in [0, 1]."""
        if seed is not None:
            random.seed(seed)
        return [1 if random.random() < value else 0 for _ in range(length)]
    
    @staticmethod
    def multiply(a_stream: List[int], b_stream: List[int]) -> float:
        """Stochastic multiplication using AND gates."""
        result_stream = [a & b for a, b in zip(a_stream, b_stream)]
        return sum(result_stream) / len(result_stream)
    
    @staticmethod
    def scaled_add(a_stream: List[int], b_stream: List[int]) -> float:
        """Stochastic scaled addition: (a + b) / 2 using MUX."""
        # MUX with 50% select probability
        select_stream = StochasticSimulator.generate_bitstream(0.5, len(a_stream))
        result_stream = [a if s else b for a, b, s in zip(a_stream, b_stream, select_stream)]
        return sum(result_stream) / len(result_stream)

def test_multiplication_accuracy(stream_lengths: List[int] = [128, 256, 512, 1024, 2048]) -> List[TestResult]:
    """Test multiplication accuracy across different stream lengths."""
    results = []
    test_cases = [
        (0.5, 0.5),   # 0.25
        (0.25, 0.75), # 0.1875
        (0.1, 0.9),   # 0.09
        (0.8, 0.8),   # 0.64
        (1.0, 0.5),   # 0.5
        (0.0, 0.5),   # 0.0
    ]
    
    for length in stream_lengths:
        for a_val, b_val in test_cases:
            # Generate independent bitstreams
            a_stream = StochasticSimulator.generate_bitstream(a_val, length, seed=42)
            b_stream = StochasticSimulator.generate_bitstream(b_val, length, seed=43)
            
            computed = StochasticSimulator.multiply(a_stream, b_stream)
            expected = a_val * b_val
            error = abs(computed - expected)
            
            results.append(TestResult(
                operation="multiply",
                input_a=a_val,
                input_b=b_val,
                expected=expected,
                computed=computed,
                error=error,
                stream_length=length
            ))
    
    return results

def test_addition_accuracy(stream_lengths: List[int] = [128, 256, 512, 1024, 2048]) -> List[TestResult]:
    """Test scaled addition accuracy across different stream lengths."""
    results = []
    test_cases = [
        (0.5, 0.5),   # 0.5
        (0.25, 0.75), # 0.5
        (0.2, 0.8),   # 0.5
        (0.0, 1.0),   # 0.5
        (0.6, 0.4),   # 0.5
        (0.1, 0.3),   # 0.2
    ]
    
    for length in stream_lengths:
        for a_val, b_val in test_cases:
            a_stream = StochasticSimulator.generate_bitstream(a_val, length, seed=44)
            b_stream = StochasticSimulator.generate_bitstream(b_val, length, seed=45)
            
            computed = StochasticSimulator.scaled_add(a_stream, b_stream)
            expected = (a_val + b_val) / 2
            error = abs(computed - expected)
            
            results.append(TestResult(
                operation="scaled_add",
                input_a=a_val,
                input_b=b_val,
                expected=expected,
                computed=computed,
                error=error,
                stream_length=length
            ))
    
    return results

def analyze_results(results: List[TestResult]):
    """Analyze and print test results."""
    print("\n" + "="*80)
    print("STOCHASTIC COMPUTING ACCURACY ANALYSIS")
    print("="*80)
    
    for op in ["multiply", "scaled_add"]:
        op_results = [r for r in results if r.operation == op]
        
        print(f"\n{op.upper()} Operation:")
        print("-" * 80)
        
        # Group by stream length
        lengths = sorted(set(r.stream_length for r in op_results))
        
        for length in lengths:
            length_results = [r for r in op_results if r.stream_length == length]
            errors = [r.error for r in length_results]
            
            mean_error = np.mean(errors)
            max_error = np.max(errors)
            std_error = np.std(errors)
            
            print(f"  Stream Length: {length:4d} | "
                  f"Mean Error: {mean_error:.6f} | "
                  f"Max Error: {max_error:.6f} | "
                  f"Std Dev: {std_error:.6f}")
        
        # Show worst cases
        print(f"\n  Worst {op} cases:")
        worst = sorted(op_results, key=lambda r: r.error, reverse=True)[:3]
        for r in worst:
            print(f"    {r.input_a:.2f} × {r.input_b:.2f} = {r.expected:.4f}, "
                  f"got {r.computed:.4f} (error: {r.error:.4f}, length: {r.stream_length})")

def plot_error_analysis(results: List[TestResult], filename: str = "error_analysis.png"):
    """Generate error analysis plots."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    for idx, op in enumerate(["multiply", "scaled_add"]):
        op_results = [r for r in results if r.operation == op]
        
        # Error vs Stream Length
        lengths = sorted(set(r.stream_length for r in op_results))
        mean_errors = [np.mean([r.error for r in op_results if r.stream_length == l]) 
                      for l in lengths]
        
        axes[idx, 0].plot(lengths, mean_errors, 'o-', linewidth=2)
        axes[idx, 0].set_xlabel('Stream Length')
        axes[idx, 0].set_ylabel('Mean Absolute Error')
        axes[idx, 0].set_title(f'{op.upper()} - Error vs Stream Length')
        axes[idx, 0].grid(True, alpha=0.3)
        axes[idx, 0].set_xscale('log', base=2)
        
        # Error distribution histogram
        errors = [r.error for r in op_results]
        axes[idx, 1].hist(errors, bins=30, alpha=0.7, edgecolor='black')
        axes[idx, 1].set_xlabel('Absolute Error')
        axes[idx, 1].set_ylabel('Frequency')
        axes[idx, 1].set_title(f'{op.upper()} - Error Distribution')
        axes[idx, 1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(filename, dpi=150)
    print(f"\nPlot saved to {filename}")

def test_correlation_effects():
    """Test the effect of correlated bitstreams (common issue in stochastic computing)."""
    print("\n" + "="*80)
    print("CORRELATION EFFECTS TEST")
    print("="*80)
    
    length = 1024
    a_val, b_val = 0.5, 0.5
    expected = a_val * b_val
    
    # Independent streams
    a_stream = StochasticSimulator.generate_bitstream(a_val, length, seed=100)
    b_stream = StochasticSimulator.generate_bitstream(b_val, length, seed=101)
    result_indep = StochasticSimulator.multiply(a_stream, b_stream)
    
    # Perfectly correlated streams (same stream)
    result_corr = StochasticSimulator.multiply(a_stream, a_stream)
    
    print(f"\nMultiplying 0.5 × 0.5 (expected: {expected}):")
    print(f"  Independent streams: {result_indep:.4f} (error: {abs(result_indep - expected):.4f})")
    print(f"  Correlated streams:  {result_corr:.4f} (error: {abs(result_corr - expected):.4f})")
    print(f"\nCorrelation introduces {abs(result_corr - expected) / abs(result_indep - expected):.1f}× more error")

if __name__ == "__main__":
    # Run all tests
    print("Running stochastic computing accuracy tests...")
    
    mul_results = test_multiplication_accuracy()
    add_results = test_addition_accuracy()
    all_results = mul_results + add_results
    
    analyze_results(all_results)
    
    # Test correlation effects
    test_correlation_effects()
    
    # Generate plots
    try:
        plot_error_analysis(all_results)
    except Exception as e:
        print(f"\nWarning: Could not generate plots: {e}")
    
    print("\n" + "="*80)
    print("Testing complete!")
    print("="*80 + "\n")