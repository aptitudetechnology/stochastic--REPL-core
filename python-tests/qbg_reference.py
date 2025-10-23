# python/qbg_reference.py
"""
QBG (Quasiperiodic Bitstream Generation) Reference Implementation
Tests H₂: Does dual-LFSR quasiperiodic mixing reduce correlation and improve accuracy?

Usage:
    python qbg_reference.py --trials 1000 --length 256
    python qbg_reference.py --mode full --output results/
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy import signal, stats
from dataclasses import dataclass
from typing import List, Tuple, Dict
import argparse
import json
from pathlib import Path
import time

# =============================================================================
# LFSR Implementations
# =============================================================================

class LFSR:
    """Base class for Linear Feedback Shift Registers"""
    
    def __init__(self, num_bits: int, polynomial: List[int], seed: int):
        """
        Args:
            num_bits: Width of LFSR
            polynomial: Tap positions (e.g., [7, 5, 4, 3] for x^8+x^6+x^5+x^4+1)
            seed: Initial state (must be non-zero)
        """
        self.num_bits = num_bits
        self.polynomial = polynomial
        self.state = seed
        self.mask = (1 << num_bits) - 1
        
        if seed == 0:
            raise ValueError("LFSR seed cannot be zero")
    
    def step(self) -> int:
        """Advance LFSR by one cycle, return current output"""
        # Calculate feedback bit (XOR of tapped positions)
        feedback = 0
        for tap in self.polynomial:
            feedback ^= (self.state >> tap) & 1
        
        # Shift and insert feedback
        self.state = ((self.state << 1) | feedback) & self.mask
        
        return self.state
    
    def get_value(self) -> int:
        """Get current state value"""
        return self.state
    
    def reset(self, seed: int):
        """Reset to initial seed"""
        if seed == 0:
            raise ValueError("LFSR seed cannot be zero")
        self.state = seed


class LFSR8bit(LFSR):
    """8-bit LFSR with period 255 (polynomial: x^8+x^6+x^5+x^4+1)"""
    
    def __init__(self, seed: int = 0xAC):
        super().__init__(num_bits=8, polynomial=[7, 5, 4, 3], seed=seed)


class LFSR7bit(LFSR):
    """7-bit LFSR with period 127 (polynomial: x^7+x^6+1)"""
    
    def __init__(self, seed: int = 0x55):
        super().__init__(num_bits=7, polynomial=[6, 5], seed=seed)


class LFSR9bit(LFSR):
    """9-bit LFSR with period 511 (polynomial: x^9+x^5+1)"""
    
    def __init__(self, seed: int = 0x1A5):
        super().__init__(num_bits=9, polynomial=[8, 4], seed=seed)


# =============================================================================
# Stochastic Number Generators
# =============================================================================

class SingleLFSR_SNG:
    """Baseline single-LFSR stochastic number generator (control)"""
    
    def __init__(self, seed: int = 0xAC):
        self.lfsr = LFSR8bit(seed)
    
    def generate_bitstream(self, probability: float, length: int) -> np.ndarray:
        """
        Generate stochastic bitstream
        
        Args:
            probability: Target probability (0.0 to 1.0)
            length: Number of bits to generate
        
        Returns:
            Binary array of length 'length'
        """
        threshold = int(probability * 256)  # Convert to 8-bit threshold
        bitstream = np.zeros(length, dtype=np.uint8)
        
        for i in range(length):
            self.lfsr.step()
            bitstream[i] = 1 if self.lfsr.get_value() < threshold else 0
        
        return bitstream
    
    def reset(self, seed: int = 0xAC):
        self.lfsr.reset(seed)


class DualLFSR_QBG:
    """Quasiperiodic bitstream generator with dual-LFSR mixing"""
    
    def __init__(self, seed1: int = 0xAC, seed2: int = 0x55, mixing_mode: str = 'average'):
        """
        Args:
            seed1: Seed for 8-bit LFSR (period 255)
            seed2: Seed for 7-bit LFSR (period 127)
            mixing_mode: 'average', 'golden', or 'xor'
        """
        self.lfsr1 = LFSR8bit(seed1)
        self.lfsr2 = LFSR7bit(seed2)
        self.mixing_mode = mixing_mode
    
    def _mix_values(self, val1: int, val2: int) -> int:
        """Mix two LFSR outputs using specified mode"""
        if self.mixing_mode == 'average':
            # Simple average
            return (val1 + val2) // 2
        
        elif self.mixing_mode == 'golden':
            # Golden ratio weighted: φ/(1+φ) ≈ 0.618, 1/(1+φ) ≈ 0.382
            weighted_sum = int(val1 * 0.618 + val2 * 0.382)
            return weighted_sum & 0xFF  # Keep 8-bit
        
        elif self.mixing_mode == 'xor':
            # XOR mixing
            return val1 ^ val2
        
        else:
            raise ValueError(f"Unknown mixing mode: {self.mixing_mode}")
    
    def generate_bitstream(self, probability: float, length: int) -> np.ndarray:
        """Generate quasiperiodically-mixed bitstream"""
        threshold = int(probability * 256)
        bitstream = np.zeros(length, dtype=np.uint8)
        
        for i in range(length):
            self.lfsr1.step()
            self.lfsr2.step()
            
            mixed = self._mix_values(self.lfsr1.get_value(), self.lfsr2.get_value())
            bitstream[i] = 1 if mixed < threshold else 0
        
        return bitstream
    
    def reset(self, seed1: int = 0xAC, seed2: int = 0x55):
        self.lfsr1.reset(seed1)
        self.lfsr2.reset(seed2)


class TripleLFSR_QBG:
    """Three-LFSR quasiperiodic generator (for H₅ testing)"""
    
    def __init__(self, seed1: int = 0xAC, seed2: int = 0x55, seed3: int = 0x1A5):
        self.lfsr1 = LFSR8bit(seed1)
        self.lfsr2 = LFSR7bit(seed2)
        self.lfsr3 = LFSR9bit(seed3)
    
    def generate_bitstream(self, probability: float, length: int) -> np.ndarray:
        threshold = int(probability * 256)
        bitstream = np.zeros(length, dtype=np.uint8)
        
        for i in range(length):
            self.lfsr1.step()
            self.lfsr2.step()
            self.lfsr3.step()
            
            # Three-way average (equal weights)
            val1 = self.lfsr1.get_value()
            val2 = self.lfsr2.get_value()
            val3 = self.lfsr3.get_value() & 0xFF  # Truncate to 8 bits
            
            mixed = (val1 + val2 + val3) // 3
            bitstream[i] = 1 if mixed < threshold else 0
        
        return bitstream
    
    def reset(self, seed1: int = 0xAC, seed2: int = 0x55, seed3: int = 0x1A5):
        self.lfsr1.reset(seed1)
        self.lfsr2.reset(seed2)
        self.lfsr3.reset(seed3)


# =============================================================================
# Analysis Functions
# =============================================================================

def compute_autocorrelation(bitstream: np.ndarray, max_lag: int = 50) -> np.ndarray:
    """
    Compute normalized autocorrelation function
    
    Returns:
        Array of autocorrelation values for lags 0 to max_lag
    """
    # Convert to -1/+1 for proper correlation
    signal_centered = bitstream.astype(float) * 2 - 1
    
    acf = np.correlate(signal_centered, signal_centered, mode='full')
    acf = acf[len(acf)//2:]  # Take positive lags only
    acf = acf / acf[0]  # Normalize
    
    return acf[:max_lag+1]


def compute_autocorr_peak(bitstream: np.ndarray) -> float:
    """
    Return maximum autocorrelation (excluding lag 0)
    This is the primary metric for H₂.₂ (secondary hypothesis)
    """
    acf = compute_autocorrelation(bitstream, max_lag=50)
    return np.max(np.abs(acf[1:]))  # Exclude lag 0


def stochastic_multiply(stream_a: np.ndarray, stream_b: np.ndarray) -> np.ndarray:
    """Stochastic multiplication via AND gate"""
    return stream_a & stream_b


def stochastic_add(stream_a: np.ndarray, stream_b: np.ndarray) -> np.ndarray:
    """Stochastic addition via MUX (alternate bits)"""
    result = np.zeros_like(stream_a)
    result[::2] = stream_a[::2]
    result[1::2] = stream_b[1::2]
    return result


def measure_operation_error(generator, p_a: float, p_b: float, 
                           operation: str, length: int, trials: int) -> Dict:
    """
    Measure error for stochastic operation
    
    Args:
        generator: SNG instance (SingleLFSR_SNG or DualLFSR_QBG)
        p_a, p_b: Input probabilities
        operation: 'multiply' or 'add'
        length: Bitstream length
        trials: Number of trials
    
    Returns:
        Dictionary with error statistics
    """
    errors = []
    
    for trial in range(trials):
        # Generate two independent bitstreams
        # Use different seeds for independence
        gen_a = type(generator)(seed1=0xAC + trial, seed2=0x55 + trial) \
                if isinstance(generator, DualLFSR_QBG) else type(generator)(seed=0xAC + trial)
        gen_b = type(generator)(seed1=0xAC + trial + 1000, seed2=0x55 + trial + 1000) \
                if isinstance(generator, DualLFSR_QBG) else type(generator)(seed=0xAC + trial + 1000)
        
        stream_a = gen_a.generate_bitstream(p_a, length)
        stream_b = gen_b.generate_bitstream(p_b, length)
        
        # Perform operation
        if operation == 'multiply':
            result = stochastic_multiply(stream_a, stream_b)
            expected = p_a * p_b
        elif operation == 'add':
            result = stochastic_add(stream_a, stream_b)
            expected = 0.5 * (p_a + p_b)
        else:
            raise ValueError(f"Unknown operation: {operation}")
        
        # Measure result
        measured = np.sum(result) / length
        error = abs(measured - expected)
        errors.append(error)
    
    return {
        'mean_error': np.mean(errors),
        'std_error': np.std(errors),
        'max_error': np.max(errors),
        'min_error': np.min(errors),
        'median_error': np.median(errors)
    }


# =============================================================================
# Hypothesis Testing
# =============================================================================

@dataclass
class HypothesisResult:
    """Results for H₂ hypothesis test"""
    # Primary hypothesis (H₂)
    single_mean_error: float
    dual_mean_error: float
    error_reduction_pct: float
    error_pvalue: float
    error_cohens_d: float
    
    # Secondary hypothesis (H₂.₂ - autocorrelation)
    single_autocorr_peak: float
    dual_autocorr_peak: float
    autocorr_reduction_pct: float
    autocorr_pvalue: float
    
    # Test conditions
    length: int
    trials: int
    test_cases: List[Tuple[float, float]]
    
    # Detailed results
    detailed_results: Dict
    
    def hypothesis_accepted(self) -> bool:
        """Check if H₂ is accepted (10-30% error reduction, p<0.05)"""
        return (self.error_reduction_pct >= 10.0 and 
                self.error_pvalue < 0.05 and
                self.error_cohens_d >= 0.3)
    
    def secondary_accepted(self) -> bool:
        """Check if H₂.₂ is accepted (20% autocorr reduction, p<0.05)"""
        return (self.autocorr_reduction_pct >= 20.0 and
                self.autocorr_pvalue < 0.05)


def test_hypothesis_h2(length: int = 256, trials: int = 1000, 
                       test_values: List[Tuple[float, float]] = None) -> HypothesisResult:
    """
    Complete H₂ hypothesis test
    
    Tests:
    - H₂: 10-30% error reduction with dual-LFSR QBG
    - H₂.₂: 20% autocorrelation reduction
    
    Returns:
        HypothesisResult with full statistics
    """
    if test_values is None:
        # Default test cases (9 combinations)
        test_values = [(p_a, p_b) for p_a in [0.25, 0.5, 0.75] 
                                    for p_b in [0.25, 0.5, 0.75]]
    
    print(f"Testing H₂ with length={length}, trials={trials}")
    print(f"Test cases: {len(test_values)}")
    print("="*60)
    
    single_gen = SingleLFSR_SNG()
    dual_gen = DualLFSR_QBG(mixing_mode='average')
    
    detailed = {}
    single_errors_all = []
    dual_errors_all = []
    single_autocorrs = []
    dual_autocorrs = []
    
    for p_a, p_b in test_values:
        print(f"\nTesting P(A)={p_a:.2f}, P(B)={p_b:.2f} (multiply)")
        
        # Test multiplication
        single_result = measure_operation_error(single_gen, p_a, p_b, 
                                               'multiply', length, trials)
        dual_result = measure_operation_error(dual_gen, p_a, p_b, 
                                             'multiply', length, trials)
        
        improvement = (single_result['mean_error'] - dual_result['mean_error']) / \
                     single_result['mean_error'] * 100
        
        print(f"  Single LFSR: {single_result['mean_error']:.6f}")
        print(f"  Dual LFSR:   {dual_result['mean_error']:.6f}")
        print(f"  Improvement: {improvement:.1f}%")
        
        detailed[f"mult_{p_a}_{p_b}"] = {
            'single': single_result,
            'dual': dual_result,
            'improvement_pct': improvement
        }
        
        single_errors_all.extend([single_result['mean_error']] * trials)
        dual_errors_all.extend([dual_result['mean_error']] * trials)
    
    # Autocorrelation analysis (sample bitstreams)
    print("\n" + "="*60)
    print("Autocorrelation Analysis")
    print("="*60)
    
    for p in [0.25, 0.5, 0.75]:
        single_stream = single_gen.generate_bitstream(p, length=1000)
        dual_stream = dual_gen.generate_bitstream(p, length=1000)
        
        single_peak = compute_autocorr_peak(single_stream)
        dual_peak = compute_autocorr_peak(dual_stream)
        
        single_autocorrs.append(single_peak)
        dual_autocorrs.append(dual_peak)
        
        print(f"P={p:.2f}: Single peak={single_peak:.4f}, Dual peak={dual_peak:.4f}")
    
    # Statistical tests
    single_mean = np.mean(single_errors_all)
    dual_mean = np.mean(dual_errors_all)
    error_reduction = (single_mean - dual_mean) / single_mean * 100
    
    # T-test for error difference
    t_stat, p_value = stats.ttest_ind(single_errors_all, dual_errors_all, 
                                       alternative='greater')
    
    # Cohen's d effect size
    pooled_std = np.sqrt((np.std(single_errors_all)**2 + 
                          np.std(dual_errors_all)**2) / 2)
    cohens_d = (single_mean - dual_mean) / pooled_std
    
    # Autocorrelation statistics
    single_autocorr_mean = np.mean(single_autocorrs)
    dual_autocorr_mean = np.mean(dual_autocorrs)
    autocorr_reduction = (single_autocorr_mean - dual_autocorr_mean) / \
                        single_autocorr_mean * 100
    
    t_stat_ac, p_value_ac = stats.ttest_rel(single_autocorrs, dual_autocorrs,
                                             alternative='greater')
    
    # Summary
    print("\n" + "="*60)
    print("HYPOTHESIS TEST RESULTS")
    print("="*60)
    print(f"\nH₂: Error Reduction")
    print(f"  Single LFSR mean error:  {single_mean:.6f}")
    print(f"  Dual LFSR mean error:    {dual_mean:.6f}")
    print(f"  Reduction:               {error_reduction:.2f}%")
    print(f"  p-value:                 {p_value:.6f}")
    print(f"  Cohen's d:               {cohens_d:.3f}")
    print(f"  Status: {'✓ ACCEPTED' if error_reduction >= 10 and p_value < 0.05 else '✗ REJECTED'}")
    
    print(f"\nH₂.₂: Autocorrelation Reduction")
    print(f"  Single LFSR peak:        {single_autocorr_mean:.4f}")
    print(f"  Dual LFSR peak:          {dual_autocorr_mean:.4f}")
    print(f"  Reduction:               {autocorr_reduction:.2f}%")
    print(f"  p-value:                 {p_value_ac:.6f}")
    print(f"  Status: {'✓ ACCEPTED' if autocorr_reduction >= 20 and p_value_ac < 0.05 else '✗ REJECTED'}")
    
    return HypothesisResult(
        single_mean_error=single_mean,
        dual_mean_error=dual_mean,
        error_reduction_pct=error_reduction,
        error_pvalue=p_value,
        error_cohens_d=cohens_d,
        single_autocorr_peak=single_autocorr_mean,
        dual_autocorr_peak=dual_autocorr_mean,
        autocorr_reduction_pct=autocorr_reduction,
        autocorr_pvalue=p_value_ac,
        length=length,
        trials=trials,
        test_cases=test_values,
        detailed_results=detailed
    )


# =============================================================================
# Visualization
# =============================================================================

def plot_results(result: HypothesisResult, output_dir: Path):
    """Generate all plots for publication"""
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Plot 1: Error comparison bar chart
    fig, ax = plt.subplots(figsize=(10, 6))
    
    categories = list(result.detailed_results.keys())
    single_errors = [result.detailed_results[k]['single']['mean_error'] 
                    for k in categories]
    dual_errors = [result.detailed_results[k]['dual']['mean_error'] 
                  for k in categories]
    
    x = np.arange(len(categories))
    width = 0.35
    
    ax.bar(x - width/2, single_errors, width, label='Single LFSR', alpha=0.8)
    ax.bar(x + width/2, dual_errors, width, label='Dual LFSR QBG', alpha=0.8)
    
    ax.set_ylabel('Mean Absolute Error')
    ax.set_title('H₂: Error Comparison (Stochastic Multiplication)')
    ax.set_xticks(x)
    ax.set_xticklabels(categories, rotation=45, ha='right')
    ax.legend()
    ax.grid(axis='y', alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(output_dir / 'h2_error_comparison.png', dpi=300)
    plt.close()
    
    # Plot 2: Autocorrelation comparison
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    
    single_gen = SingleLFSR_SNG()
    dual_gen = DualLFSR_QBG()
    
    single_stream = single_gen.generate_bitstream(0.5, 1000)
    dual_stream = dual_gen.generate_bitstream(0.5, 1000)
    
    single_acf = compute_autocorrelation(single_stream, max_lag=50)
    dual_acf = compute_autocorrelation(dual_stream, max_lag=50)
    
    ax1.stem(range(len(single_acf)), single_acf, basefmt=' ')
    ax1.set_title('Single LFSR Autocorrelation')
    ax1.set_xlabel('Lag')
    ax1.set_ylabel('Autocorrelation')
    ax1.grid(alpha=0.3)
    ax1.axhline(y=0, color='k', linewidth=0.5)
    
    ax2.stem(range(len(dual_acf)), dual_acf, basefmt=' ')
    ax2.set_title('Dual LFSR QBG Autocorrelation')
    ax2.set_xlabel('Lag')
    ax2.set_ylabel('Autocorrelation')
    ax2.grid(alpha=0.3)
    ax2.axhline(y=0, color='k', linewidth=0.5)
    
    plt.tight_layout()
    plt.savefig(output_dir / 'h2_autocorrelation.png', dpi=300)
    plt.close()
    
    # Plot 3: Improvement percentages
    fig, ax = plt.subplots(figsize=(10, 6))
    
    improvements = [result.detailed_results[k]['improvement_pct'] 
                   for k in categories]
    
    colors = ['green' if imp >= 10 else 'orange' if imp >= 5 else 'red' 
              for imp in improvements]
    
    ax.bar(range(len(categories)), improvements, color=colors, alpha=0.7)
    ax.axhline(y=10, color='green', linestyle='--', label='10% threshold (H₂)')
    ax.axhline(y=0, color='black', linewidth=0.5)
    
    ax.set_ylabel('Error Reduction (%)')
    ax.set_title('H₂: Improvement by Test Case')
    ax.set_xticks(range(len(categories)))
    ax.set_xticklabels(categories, rotation=45, ha='right')
    ax.legend()
    ax.grid(axis='y', alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(output_dir / 'h2_improvements.png', dpi=300)
    plt.close()
    
    print(f"\nPlots saved to {output_dir}/")


# =============================================================================
# Main Execution
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description='QBG H₂ Hypothesis Testing')
    parser.add_argument('--trials', type=int, default=1000,
                       help='Number of trials per test case')
    parser.add_argument('--length', type=int, default=256,
                       help='Bitstream length')
    parser.add_argument('--mode', choices=['quick', 'full'], default='quick',
                       help='Testing mode')
    parser.add_argument('--output', type=str, default='results/python_validation',
                       help='Output directory for results')
    
    args = parser.parse_args()
    
    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Run hypothesis test
    start_time = time.time()
    result = test_hypothesis_h2(length=args.length, trials=args.trials)
    elapsed = time.time() - start_time
    
    print(f"\nCompleted in {elapsed:.1f} seconds")
    
    # Generate plots
    if args.mode == 'full':
        print("\nGenerating publication plots...")
        plot_results(result, output_dir)
    
    # Save results to JSON
    results_dict = {
        'hypothesis': 'H₂: Dual-LFSR QBG improves stochastic computing accuracy',
        'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
        'parameters': {
            'bitstream_length': args.length,
            'trials_per_case': args.trials,
            'test_cases': len(result.test_cases)
        },
        'results': {
            'single_lfsr_mean_error': result.single_mean_error,
            'dual_lfsr_mean_error': result.dual_mean_error,
            'error_reduction_percent': result.error_reduction_pct,
            'error_pvalue': result.error_pvalue,
            'cohens_d': result.error_cohens_d,
            'single_autocorr_peak': result.single_autocorr_peak,
            'dual_autocorr_peak': result.dual_autocorr_peak,
            'autocorr_reduction_percent': result.autocorr_reduction_pct,
            'autocorr_pvalue': result.autocorr_pvalue
        },
        'decision': {
            'h2_accepted': result.hypothesis_accepted(),
            'h2_2_accepted': result.secondary_accepted(),
            'recommendation': 'Proceed to hardware validation (Phase 2)' 
                            if result.hypothesis_accepted() 
                            else 'Hypothesis rejected - consider revisions'
        }
    }
    
    with open(output_dir / 'h2_results.json', 'w') as f:
        json.dump(results_dict, f, indent=2)
    
    print(f"\nResults saved to {output_dir}/h2_results.json")
    
    # Decision point
    print("\n" + "="*60)
    print("GO/NO-GO DECISION")
    print("="*60)
    if result.hypothesis_accepted():
        print("✓ H₂ ACCEPTED: Proceed to Phase 2 (FPGA implementation)")
        print(f"  Error reduction: {result.error_reduction_pct:.1f}% (target: ≥10%)")
        print(f"  Statistical significance: p={result.error_pvalue:.6f} (target: <0.05)")
        print(f"  Effect size: d={result.error_cohens_d:.3f} (target: ≥0.3)")
    else:
        print("✗ H₂ REJECTED: Do not proceed to hardware")
        print("  Recommendation: Publish negative result or revise approach")
        if result.error_reduction_pct < 5:
            print("  Reason: Effect size too small (<5%)")
        if result.error_pvalue >= 0.05:
            print("  Reason: Not statistically significant (p≥0.05)")
    
    return 0 if result.hypothesis_accepted() else 1


if __name__ == '__main__':
    exit(main())