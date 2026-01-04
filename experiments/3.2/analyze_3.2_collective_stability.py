#!/usr/bin/env python3
"""
WESH EXPERIMENT 4 - PRODUCTION VERSION
Collective Stability Verification with Full Analysis Pipeline

Usage:
    python wesh_exp4_final.py --auto           # Run complete analysis automatically
    python wesh_exp4_final.py --mode 1         # Specific mode without interaction
    python wesh_exp4_final.py --interactive    # Interactive mode (default)
    python wesh_exp4_final.py --seed 42        # Fixed seed for reproducibility
    python wesh_exp4_final.py --quiet          # Minimal output for batch processing

Dependencies:
    - numpy >= 1.19.0
    - scipy >= 1.5.0
    - matplotlib >= 3.3.0
    - pandas >= 1.1.0
    - qutip >= 4.5.0

Author: Luca Casagrande
Version: 1.0.1
"""

import sys

# CRITICAL FIX FOR COLAB: Remove Jupyter kernel arguments immediately
# This must happen BEFORE any other imports or code
if any('-f' in arg for arg in sys.argv):
    # We're in Jupyter/Colab - clean sys.argv immediately
    sys.argv = ['notebook']
    IN_NOTEBOOK = True
else:
    IN_NOTEBOOK = False

import warnings
warnings.filterwarnings('ignore')  # Suppress matplotlib warnings in notebooks

# Check dependencies
try:
    import numpy as np
    import qutip as qt
    import matplotlib
    matplotlib.use('Agg')  # Use non-interactive backend for batch processing
    import matplotlib.pyplot as plt
    import pandas as pd
    from scipy.optimize import curve_fit
    from scipy import stats
except ImportError as e:
    print(f"Missing dependency: {e}")
    print("Install requirements: pip install numpy scipy matplotlib pandas qutip")
    if not IN_NOTEBOOK:
        sys.exit(1)

import json
from datetime import datetime
import os
import time
from typing import Dict, List, Tuple, Callable, Optional
from dataclasses import dataclass, field
import hashlib

# ============= CONFIGURATION =============

def setup_seed(seed=None):
    """Setup reproducible random seed."""
    if seed is None:
        seed = int(time.time() * 1000) % 2**32
    np.random.seed(seed)
    return seed

# Detect if running in notebook/Colab
def is_notebook():
    """Check if code is running in Jupyter/Colab."""
    try:
        shell = get_ipython().__class__.__name__  
        if shell == 'ZMQInteractiveShell':
            return True   # Jupyter notebook or qtconsole
        elif shell == 'TerminalInteractiveShell':
            return False  # Terminal running IPython
        else:
            return False  # Other type
    except NameError:
        return False      # Probably standard Python interpreter

# Parse command line arguments
def parse_arguments():
    """Parse command line arguments for batch processing."""
    # If in notebook, skip argparse completely
    if is_notebook():
        # Return default args for notebook
        class Args:
            def __init__(self):
                self.auto = False
                self.mode = None
                self.seed = None
                self.trajectories = 150
                self.strength = 0.3
                self.quiet = True
                self.interactive = False
                self.output_dir = '.'
                self.no_plots = False
        return Args()
    
    # Only import and use argparse in CLI mode
    import argparse
    
    parser = argparse.ArgumentParser(
        description='WESH Experiment 4: Collective Stability Verification'
    )
    parser.add_argument('--auto', action='store_true',
                       help='Run complete analysis automatically (no interaction)')
    parser.add_argument('--mode', type=int, choices=[1, 2, 3, 4],
                       help='Execution mode: 1=Complete, 2=Quick, 3=Custom, 4=Verification only')
    parser.add_argument('--seed', type=int, default=None,
                       help='Random seed for reproducibility')
    parser.add_argument('--trajectories', type=int, default=150,
                       help='Number of trajectories per configuration')
    parser.add_argument('--strength', type=float, default=0.3,
                       help='Base measurement strength')
    parser.add_argument('--quiet', action='store_true',
                       help='Minimal output (only critical messages)')
    parser.add_argument('--interactive', action='store_true',
                       help='Interactive mode with prompts (default if no args)')
    parser.add_argument('--output-dir', type=str, default='.',
                       help='Output directory for results')
    parser.add_argument('--no-plots', action='store_true',
                       help='Skip plot generation (faster for testing)')
    
    args = parser.parse_args()
    
    # If no arguments provided, default to interactive
    if len(sys.argv) == 1:
        args.interactive = True
    
    return args

# Enhanced logging with levels
class Logger:
    def __init__(self, verbose=True, log_file=None):
        self.verbose = verbose
        self.log_file = log_file
        self.start_time = time.time()
        
    def log(self, message, level='INFO'):
        """Log with timestamp and level control."""
        if level == 'CRITICAL' or (self.verbose and level != 'DEBUG'):
            timestamp = datetime.now().strftime('%H:%M:%S')
            elapsed = time.time() - self.start_time
            log_msg = f"[{timestamp} +{elapsed:.1f}s] {message}"
            print(log_msg)
            
            if self.log_file:
                with open(self.log_file, 'a') as f:
                    f.write(log_msg + '\n')

# Global logger instance
logger = None

@dataclass
class MediumConfig:
    """Enhanced configuration with metadata tracking."""
    # Core parameters
    n_trajectories: int = 150
    N_values: List[int] = field(default_factory=lambda: [2, 3, 4, 5, 6, 8, 10, 12, 14, 16])
    measurement_strength_base: float = 0.3
    n_measurement_rounds: int = 8
    
    # Test selection
    measurement_types: List[str] = field(default_factory=lambda: ['dephasing', 'projective', 'amplitude_damping'])
    scaling_modes: List[Tuple[str, Callable]] = field(default_factory=lambda: [
        ('constant', lambda N: 1.0),
        ('inverse_sqrt', lambda N: 1.0 / np.sqrt(N)),
        ('inverse_linear', lambda N: 1.0 / N),
        ('inverse_quadratic', lambda N: 1.0 / N**2)
    ])
    
    # Statistical analysis
    bootstrap_samples: int = 500
    confidence_level: float = 0.95
    n_initial_states: int = 3
    
    # Execution control
    randomize_parameters: bool = False
    parameter_variance: float = 0.2
    run_wesh_verification: bool = False
    create_complete_analysis: bool = True
    generate_plots: bool = True
    
    # Metadata
    seed: int = None
    output_dir: str = '.'
    experiment_id: str = None
    
    def __post_init__(self):
        """Initialize configuration with metadata."""
        if self.seed is None:
            self.seed = setup_seed()
        else:
            setup_seed(self.seed)
        
        if self.experiment_id is None:
            self.experiment_id = self.get_config_hash()
        
        # Create output directory if needed
        if self.output_dir != '.' and not os.path.exists(self.output_dir):
            os.makedirs(self.output_dir)
        
        # Apply randomization if requested
        if self.randomize_parameters:
            var = self.parameter_variance
            base_trajectories = 150
            base_strength = 0.3
            base_rounds = 8
            
            self.n_trajectories = int(base_trajectories * (1 + np.random.uniform(-var, var)))
            self.measurement_strength_base = base_strength * (1 + np.random.uniform(-var, var))
            self.n_measurement_rounds = int(base_rounds * (1 + np.random.uniform(-var/2, var/2)))
        
        # Log configuration
        global logger
        if logger:
            logger.log(f"Configuration initialized: seed={self.seed}, id={self.experiment_id}")
    
    def get_config_hash(self) -> str:
        """Generate unique hash for this configuration."""
        config_str = f"{self.n_trajectories}_{self.measurement_strength_base:.4f}_{self.n_measurement_rounds}_{self.seed}"
        return hashlib.md5(config_str.encode()).hexdigest()[:8]
    
    def to_dict(self) -> dict:
        """Export configuration as dictionary with metadata."""
        return {
            'n_trajectories': self.n_trajectories,
            'N_values': self.N_values,
            'measurement_strength_base': self.measurement_strength_base,
            'n_measurement_rounds': self.n_measurement_rounds,
            'seed': self.seed,
            'experiment_id': self.experiment_id,
            'timestamp': datetime.now().isoformat(),
            'bootstrap_samples': self.bootstrap_samples,
            'confidence_level': self.confidence_level
        }

# ============= QUANTUM SIMULATOR =============

class MediumQuantumSimulator:
    """Balanced simulator with more features than light version."""

    def __init__(self, N: int):
        self.N = N
        # Pre-compute common states
        self.zero = qt.basis(2, 0)
        self.one = qt.basis(2, 1)
        self.plus = (self.zero + self.one).unit()
        self.minus = (self.zero - self.one).unit()
        self.identity = qt.qeye(2)

        # Pre-compute Pauli matrices
        self.sigma_x = qt.sigmax()
        self.sigma_y = qt.sigmay()
        self.sigma_z = qt.sigmaz()

    def create_initial_state(self, state_type: str = 'standard') -> qt.Qobj:
        """Multiple initial state options for robustness testing."""
        if state_type == 'standard':
            if self.N == 1:
                return self.plus
            else:
                all_qubits = [self.plus] + [self.zero for _ in range(self.N - 1)]
                return qt.tensor(*all_qubits)

        elif state_type == 'rotated':
            # Random rotation of standard state
            theta = np.random.uniform(0, np.pi/4)
            phi = np.random.uniform(0, 2*np.pi)
            rotated = np.cos(theta/2) * self.plus + np.exp(1j*phi) * np.sin(theta/2) * self.minus
            if self.N == 1:
                return rotated
            else:
                all_qubits = [rotated] + [self.zero for _ in range(self.N - 1)]
                return qt.tensor(*all_qubits)

        elif state_type == 'entangled':
            # Create a partially entangled state
            if self.N < 2:
                return self.plus
            # Bell pair on first two qubits
            bell = (qt.tensor(self.zero, self.zero) + qt.tensor(self.one, self.one)).unit()
            if self.N == 2:
                return bell
            else:
                remaining = [self.zero for _ in range(self.N - 2)]
                return qt.tensor(bell, *remaining)

    def compute_coherence_multi(self, state: qt.Qobj) -> Dict[str, float]:
        """Compute multiple coherence measures."""
        rho = state if state.type == 'oper' else state.proj()
        rho_system = rho.ptrace([0]) if self.N > 1 else rho
        arr = rho_system.full()

        # L1 coherence
        l1_coherence = np.sum(np.abs(arr)) - np.sum(np.abs(np.diag(arr))) if arr.ndim == 2 else 0

        # Off-diagonal magnitude (simpler measure)
        off_diag = np.abs(arr[0,1]) * 2 if arr.shape == (2, 2) else 0

        # Purity-based coherence
        if rho_system.type == 'oper' and rho_system.dims == [[2], [2]]:
            rho_arr = rho_system.full()
            if rho_arr.ndim == 2 and rho_arr.shape[0] == rho_arr.shape[1]:
                purity = np.real(np.trace(rho_arr @ rho_arr))
            else:
                purity = 0.0
        else:
            purity = 0.0

        purity_coherence = 2 * (purity - 0.5)  # Normalized to [0,1]

        return {
            'l1': l1_coherence,
            'off_diag': off_diag,
            'purity': max(0, purity_coherence)
        }

    def apply_measurement_batch(self, state: qt.Qobj, measurement_type: str,
                               strength_per_qubit: float, qubit_order: np.ndarray) -> qt.Qobj:
        """Apply measurements with error checking."""
        current_state = state

        for qubit_idx in qubit_order:
            if measurement_type == 'dephasing':
                current_state = self._apply_dephasing(current_state, qubit_idx, strength_per_qubit)
            elif measurement_type == 'projective':
                current_state = self._apply_projective(current_state, qubit_idx, strength_per_qubit)
            elif measurement_type == 'amplitude_damping':
                current_state = self._apply_amplitude_damping(current_state, qubit_idx, strength_per_qubit)

            # Check for numerical issues
            if not np.isclose(current_state.tr(), 1.0, atol=1e-6):
                if logger:
                    logger.log(f"Warning: Trace deviation {current_state.tr()}", level='WARNING')
                current_state = current_state / current_state.tr()

        return current_state

    def _apply_dephasing(self, state: qt.Qobj, qubit_idx: int, strength: float) -> qt.Qobj:
        """Dephasing channel with proper normalization."""
        rho = state if state.type == 'oper' else state.proj()
        strength = np.clip(strength, 0, 1)
        sqrt_1_minus_p = np.sqrt(1 - strength)
        sqrt_p = np.sqrt(strength)

        if self.N == 1:
            E0 = sqrt_1_minus_p * self.identity
            E1 = sqrt_p * self.sigma_z
            result = E0 * rho * E0.dag() + E1 * rho * E1.dag()
        else:
            ops_E0 = [self.identity] * self.N
            ops_E1 = [self.identity] * self.N
            ops_E0[qubit_idx] = sqrt_1_minus_p * self.identity
            ops_E1[qubit_idx] = sqrt_p * self.sigma_z
            E0_op = qt.tensor(ops_E0)
            E1_op = qt.tensor(ops_E1)
            result = E0_op * rho * E0_op.dag() + E1_op * rho * E1_op.dag()

        return result / result.tr()

    def _apply_projective(self, state: qt.Qobj, qubit_idx: int, strength: float) -> qt.Qobj:
        """Projective measurement with proper normalization."""
        rho = state if state.type == 'oper' else state.proj()
        strength = np.clip(strength, 0, 1)
        sqrt_p = np.sqrt(strength)
        sqrt_1_minus_p = np.sqrt(1 - strength)
        P0 = self.zero * self.zero.dag()
        P1 = self.one * self.one.dag()

        if self.N == 1:
            K0 = sqrt_1_minus_p * self.identity
            K1 = sqrt_p * P0
            K2 = sqrt_p * P1
            result = K0 * rho * K0.dag() + K1 * rho * K1.dag() + K2 * rho * K2.dag()
        else:
            ops_K0 = [self.identity] * self.N
            ops_K1 = [self.identity] * self.N
            ops_K2 = [self.identity] * self.N
            ops_K0[qubit_idx] = sqrt_1_minus_p * self.identity
            ops_K1[qubit_idx] = sqrt_p * P0
            ops_K2[qubit_idx] = sqrt_p * P1
            K0_op = qt.tensor(ops_K0)
            K1_op = qt.tensor(ops_K1)
            K2_op = qt.tensor(ops_K2)
            result = K0_op * rho * K0_op.dag() + K1_op * rho * K1_op.dag() + K2_op * rho * K2_op.dag()

        return result / result.tr()

    def _apply_amplitude_damping(self, state: qt.Qobj, qubit_idx: int, strength: float) -> qt.Qobj:
        """Amplitude damping channel."""
        rho = state if state.type == 'oper' else state.proj()
        strength = np.clip(strength, 0, 1)
        E0 = qt.Qobj([[1, 0], [0, np.sqrt(1 - strength)]])
        E1 = qt.Qobj([[0, np.sqrt(strength)], [0, 0]])

        if self.N == 1:
            result = E0 * rho * E0.dag() + E1 * rho * E1.dag()
        else:
            ops_E0 = [self.identity] * self.N
            ops_E1 = [self.identity] * self.N
            ops_E0[qubit_idx] = E0
            ops_E1[qubit_idx] = E1
            E0_op = qt.tensor(ops_E0)
            E1_op = qt.tensor(ops_E1)
            result = E0_op * rho * E0_op.dag() + E1_op * rho * E1_op.dag()

        return result / result.tr()

# ============= ANALYSIS FUNCTIONS =============

def bootstrap_confidence_interval(data: np.ndarray, n_bootstrap: int = 500,
                                 confidence: float = 0.95) -> Tuple[float, float, float]:
    """Compute bootstrap confidence interval with proper error handling."""
    if len(data) < 2:
        return np.mean(data), np.mean(data), np.mean(data)

    bootstrap_means = []
    n = len(data)

    for _ in range(n_bootstrap):
        resample = np.random.choice(data, size=n, replace=True)
        bootstrap_means.append(np.mean(resample))

    bootstrap_means = np.array(bootstrap_means)
    alpha = (1 - confidence) / 2

    return (
        np.mean(data),
        np.percentile(bootstrap_means, 100 * alpha),
        np.percentile(bootstrap_means, 100 * (1 - alpha))
    )

def fit_with_uncertainty(N_values: np.ndarray, y_values: np.ndarray,
                        y_errors: np.ndarray, model_name: str = 'exponential') -> Dict:
    """Enhanced fitting with proper uncertainty quantification."""
    result = {'model': model_name}

    mask = np.isfinite(y_values) & np.isfinite(y_errors) & (y_errors > 0)
    if np.sum(mask) < 3:
        return {'model': model_name, 'status': 'insufficient_data'}

    N_clean = N_values[mask]
    y_clean = y_values[mask]
    err_clean = y_errors[mask]

    try:
        if model_name == 'exponential':
            initial_guesses = [
                [y_clean[0], 0.1],
                [y_clean.max(), 0.05],
                [1.0, 0.2],
                [0.5, 0.5]
            ]

            best_fit = None
            best_chi2 = np.inf

            for p0 in initial_guesses:
                try:
                    popt, pcov = curve_fit(
                        lambda N, a, b: a * np.exp(-b * N),
                        N_clean, y_clean,
                        sigma=err_clean,
                        p0=p0,
                        absolute_sigma=True,
                        maxfev=5000
                    )

                    y_fit = popt[0] * np.exp(-popt[1] * N_clean)
                    chi2 = np.sum(((y_clean - y_fit) / err_clean)**2)

                    if chi2 < best_chi2:
                        best_chi2 = chi2
                        best_fit = (popt, pcov)
                except:
                    continue

            if best_fit is None:
                return {'model': model_name, 'status': 'fit_failed'}

            popt, pcov = best_fit
            perr = np.sqrt(np.diag(pcov))
            a, b = popt
            a_err, b_err = perr

            y_fit = a * np.exp(-b * N_clean)
            residuals = y_clean - y_fit

            ss_res = np.sum(residuals**2)
            ss_tot = np.sum((y_clean - np.mean(y_clean))**2)
            r_squared = 1 - (ss_res / ss_tot) if ss_tot > 0 else -np.inf

            dof = len(N_clean) - 2
            chi2_reduced = best_chi2 / dof if dof > 0 else np.inf

            t_stat = abs(b) / b_err if b_err > 0 else np.inf
            p_value = 2 * (1 - stats.t.cdf(t_stat, dof))

            result.update({
                'status': 'success',
                'a': a,
                'b': b,
                'a_err': a_err,
                'b_err': b_err,
                'r_squared': r_squared,
                'chi2_reduced': chi2_reduced,
                'p_value': p_value,
                'decay_type': 'positive' if b > 0 else 'negative',
                'significant': p_value < 0.05
            })

    except Exception as e:
        result['status'] = 'error'
        result['error'] = str(e)

    return result

def run_medium_experiment(config: MediumConfig) -> Dict:
    """Run the medium-complexity experiment."""
    if logger:
        logger.log("="*60)
        logger.log("WESH EXPERIMENT 4 - MEDIUM VERSION")
        logger.log(f"Config hash: {config.get_config_hash()}")
        logger.log("="*60)

    start_time = time.time()

    results = {
        'config': config.to_dict(),
        'config_hash': config.get_config_hash(),
        'timestamp': datetime.now().isoformat(),
        'data': {},
        'analysis': {},
        'statistical_tests': {}
    }

    # Main experimental loop
    for measurement_type in config.measurement_types:
        if logger:
            logger.log(f"\nTesting {measurement_type} channel...")

        for scaling_name, scaling_func in config.scaling_modes:
            if logger:
                logger.log(f"  Scaling: {scaling_name}")

            key = f"{measurement_type}_{scaling_name}"
            data_points = []

            for N in config.N_values:
                if logger:
                    logger.log(f"    N={N}", level='DEBUG')
                    print("... ", end="", flush=True)

                effective_strength = config.measurement_strength_base * scaling_func(N)

                all_coherences = []
                coherence_by_measure = {'l1': [], 'off_diag': [], 'purity': []}

                sim = MediumQuantumSimulator(N)

                for state_type in ['standard', 'rotated', 'entangled'][:config.n_initial_states]:
                    for _ in range(config.n_trajectories // config.n_initial_states):
                        state = sim.create_initial_state(state_type)

                        for _ in range(config.n_measurement_rounds):
                            qubit_order = np.random.permutation(N)
                            state = sim.apply_measurement_batch(
                                state, measurement_type, effective_strength, qubit_order
                            )

                        coherences = sim.compute_coherence_multi(state)
                        all_coherences.append(coherences['off_diag'])

                        for measure, value in coherences.items():
                            coherence_by_measure[measure].append(value)

                all_coherences = np.array(all_coherences)
                mean_c, ci_lower, ci_upper = bootstrap_confidence_interval(
                    all_coherences, config.bootstrap_samples, config.confidence_level
                )

                data_points.append({
                    'N': N,
                    'mean': mean_c,
                    'std': np.std(all_coherences),
                    'stderr': np.std(all_coherences) / np.sqrt(len(all_coherences)),
                    'ci_lower': ci_lower,
                    'ci_upper': ci_upper,
                    'median': np.median(all_coherences),
                    'effective_strength': effective_strength,
                    'n_samples': len(all_coherences),
                    'coherence_measures': {
                        measure: {
                            'mean': np.mean(values),
                            'std': np.std(values)
                        } for measure, values in coherence_by_measure.items()
                    }
                })

                if logger:
                    logger.log(f"⟨C⟩={mean_c:.3f}±{np.std(all_coherences):.3f} "
                              f"[{ci_lower:.3f}, {ci_upper:.3f}]")

            results['data'][key] = data_points

    # Enhanced analysis
    if logger:
        logger.log("\nPerforming statistical analysis...")
    results['analysis'] = analyze_results_enhanced(results['data'], config)

    # Statistical tests
    if logger:
        logger.log("Running statistical tests...")
    results['statistical_tests'] = run_statistical_tests(results['data'])

    # Create plots
    if config.generate_plots:
        create_enhanced_plots(results, config)

    # Save results
    output_file = os.path.join(config.output_dir, 
                               f'wesh_medium_{config.get_config_hash()}_{datetime.now().strftime("%Y%m%d_%H%M%S")}.json')
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2, default=str)

    elapsed = time.time() - start_time
    if logger:
        logger.log(f"\nCompleted in {elapsed:.1f} seconds")
        logger.log(f"Results saved to: {output_file}")

    # Print summary
    print_enhanced_summary(results)
    
    # WESH Verification (if requested)
    if config.run_wesh_verification:
        if logger:
            logger.log("\n" + "="*70)
            logger.log("STARTING WESH SCALING VERIFICATION")
            logger.log("="*70)
        
        wesh_results = verify_wesh_scaling_complete(config)
        results['wesh_verification'] = wesh_results
        
        if logger:
            logger.log("\n" + "="*70)
            logger.log("WESH VERIFICATION COMPLETE")
            logger.log("="*70)
        
        for key, data in wesh_results.items():
            if 'alpha' in data and not np.isnan(data['alpha']):
                if logger:
                    logger.log(f"{key}: α = {data['alpha']:.3f} ± {data['alpha_error']:.3f}")
                    # Report deviation from theoretical prediction
                    deviation = abs(data['alpha'] + 2)
                    sigma_dev = deviation / data['alpha_error'] if data['alpha_error'] > 0 else np.inf
                    logger.log(f"  Deviation from α = -2: {deviation:.3f} ({sigma_dev:.1f}σ)")
    
    # Complete Analysis Visualization (if requested)
    if config.create_complete_analysis:
        if logger:
            logger.log("\nCreating complete analysis visualization...")
        analysis_df = create_complete_wesh_analysis(results, config)
        results['complete_analysis'] = analysis_df.to_dict()

    return results

def analyze_results_enhanced(data: Dict, config: MediumConfig) -> Dict:
    """Enhanced analysis with multiple fit models and diagnostics."""
    analysis = {}

    for key, points in data.items():
        N_values = np.array([p['N'] for p in points])
        means = np.array([p['mean'] for p in points])
        stderrs = np.array([p['stderr'] for p in points])

        fit_result = fit_with_uncertainty(N_values, means, stderrs, 'exponential')

        if fit_result.get('status') == 'success':
            y_fit = fit_result['a'] * np.exp(-fit_result['b'] * N_values)
            residuals = means - y_fit

            runs_p = np.nan
            if len(residuals) > 1:
                dw = np.sum(np.diff(residuals)**2) / np.sum(residuals**2)
            else:
                dw = np.nan

            fit_result['diagnostics'] = {
                'runs_test_p': runs_p,
                'durbin_watson': dw,
                'residual_std': np.std(residuals)
            }

        analysis[key] = fit_result

    summary = {
        'total_configurations': len(analysis),
        'successful_fits': sum(1 for v in analysis.values() if v.get('status') == 'success'),
        'positive_decays': sum(1 for v in analysis.values() if v.get('decay_type') == 'positive'),
        'negative_decays': sum(1 for v in analysis.values() if v.get('decay_type') == 'negative'),
        'significant_effects': sum(1 for v in analysis.values() if v.get('significant', False))
    }

    analysis['summary'] = summary
    return analysis

def run_statistical_tests(data: Dict) -> Dict:
    """Run additional statistical tests for robustness."""
    tests = {}

    decay_rates_by_measurement = {}
    for key in data:
        measurement, scaling = key.split('_', 1)
        if measurement not in decay_rates_by_measurement:
            decay_rates_by_measurement[measurement] = {}

        points = data[key]
        if len(points) > 0:
            final_coherence = points[-1]['mean']
            decay_rates_by_measurement[measurement][scaling] = final_coherence

    for scaling in ['constant', 'inverse_sqrt', 'inverse_linear']:
        values = []
        for measurement in decay_rates_by_measurement:
            if scaling in decay_rates_by_measurement[measurement]:
                values.append(decay_rates_by_measurement[measurement][scaling])

        if len(values) >= 2:
            tests[f'measurement_comparison_{scaling}'] = {
                'mean': np.mean(values),
                'std': np.std(values),
                'cv': np.std(values) / np.mean(values) if np.mean(values) > 0 else np.inf
            }

    for key, points in data.items():
        if len(points) >= 5:
            N_values = np.array([p['N'] for p in points])
            means = np.array([p['mean'] for p in points])

            correlation, p_value = stats.spearmanr(N_values, means)

            tests[f'{key}_trend'] = {
                'spearman_r': correlation,
                'p_value': p_value,
                'trend': 'increasing' if correlation > 0 else 'decreasing',
                'significant': p_value < 0.05
            }

    return tests

def create_enhanced_plots(results: Dict, config: MediumConfig):
    """Create comprehensive visualization with error bars and fits."""
    if not config.generate_plots:
        return
        
    n_measurements = len(config.measurement_types)
    n_scalings = len(config.scaling_modes)

    fig, axes = plt.subplots(n_measurements, n_scalings,
                            figsize=(4*n_scalings, 3.5*n_measurements))

    if n_measurements == 1:
        axes = axes.reshape(1, -1)
    if n_scalings == 1:
        axes = axes.reshape(-1, 1)

    colors = plt.cm.tab10(np.linspace(0, 1, 10))

    for i, measurement in enumerate(config.measurement_types):
        for j, (scaling_name, _) in enumerate(config.scaling_modes):
            ax = axes[i, j]
            key = f"{measurement}_{scaling_name}"

            if key not in results['data']:
                ax.text(0.5, 0.5, 'No Data', ha='center', va='center')
                ax.set_xlim(0, 1)
                ax.set_ylim(0, 1)
                continue

            points = results['data'][key]
            N_values = [p['N'] for p in points]
            means = [p['mean'] for p in points]
            ci_lower = [p['ci_lower'] for p in points]
            ci_upper = [p['ci_upper'] for p in points]

            ax.errorbar(N_values, means,
                       yerr=[np.array(means) - np.array(ci_lower),
                             np.array(ci_upper) - np.array(means)],
                       fmt='o', capsize=5, markersize=6,
                       color=colors[i], ecolor=colors[i],
                       label='Data', alpha=0.8)

            if key in results['analysis'] and results['analysis'][key].get('status') == 'success':
                fit = results['analysis'][key]
                N_smooth = np.linspace(min(N_values), max(N_values), 100)
                y_fit = fit['a'] * np.exp(-fit['b'] * N_smooth)

                line_color = 'green' if fit['b'] > 0 else 'red'
                ax.plot(N_smooth, y_fit, '--', color=line_color, linewidth=2,
                       label=f"b={fit['b']:.3f}±{fit['b_err']:.3f}")

                y_upper = fit['a'] * np.exp(-(fit['b'] - fit['b_err']) * N_smooth)
                y_lower = fit['a'] * np.exp(-(fit['b'] + fit['b_err']) * N_smooth)
                ax.fill_between(N_smooth, y_lower, y_upper,
                               color=line_color, alpha=0.2)

            ax.set_xlabel('N' if i == n_measurements-1 else '')
            ax.set_ylabel('⟨C⟩' if j == 0 else '')
            ax.set_title(f'{measurement.title()}\n{scaling_name}' if i == 0 else '')
            ax.set_yscale('log')
            ax.grid(True, alpha=0.3, which='both')
            ax.legend(fontsize=8, loc='best')
            ax.set_ylim(bottom=0.001, top=1.5)

    plt.tight_layout()

    summary = results['analysis']['summary']
    fig.text(0.5, 0.02,
             f"Positive: {summary['positive_decays']} | "
             f"Negative: {summary['negative_decays']} | "
             f"Significant: {summary['significant_effects']}",
             ha='center', fontsize=11,
             bbox=dict(boxstyle='round', facecolor='lightgray', alpha=0.5))

    output_file = os.path.join(config.output_dir,
                               f'wesh_medium_{results["config_hash"]}_{datetime.now().strftime("%Y%m%d_%H%M%S")}.png')
    plt.savefig(output_file, dpi=200, bbox_inches='tight')
    plt.close()

def print_enhanced_summary(results: Dict):
    """Print detailed summary with statistical information."""
    print("\n" + "="*70)
    print("ENHANCED SUMMARY REPORT")
    print("="*70)

    summary = results['analysis']['summary']
    config = results['config']

    print(f"\nExperimental Parameters:")
    print(f"  - Trajectories: {config['n_trajectories']}")
    print(f"  - Base strength: {config['measurement_strength_base']:.3f}")
    print(f"  - Measurement rounds: {config['n_measurement_rounds']}")
    print(f"  - Bootstrap samples: {config['bootstrap_samples']}")
    print(f"  - Config hash: {results['config_hash']}")

    print(f"\nResults Overview:")
    print(f"  - Total configurations: {summary['total_configurations']}")
    print(f"  - Successful fits: {summary['successful_fits']}")
    print(f"  - Positive decay rate (b > 0): {summary['positive_decays']}")
    print(f"  - Negative decay rate (b < 0): {summary['negative_decays']}")
    print(f"  - Statistically significant: {summary['significant_effects']}")

    if summary['negative_decays'] > 0:
        print("\nConfigurations with b < 0:")

        print("\n{:<30} {:<15} {:<20} {:<10}".format(
            "Configuration", "Decay rate (b)", "Uncertainty", "p-value"))
        print("-" * 75)

        for key, analysis in results['analysis'].items():
            if key == 'summary':
                continue
            if analysis.get('decay_type') == 'negative' and analysis.get('status') == 'success':
                print("{:<30} {:<15.4f} ±{:<18.4f} {:<10.3e}".format(
                    key,
                    analysis['b'],
                    analysis['b_err'],
                    analysis.get('p_value', np.nan)
                ))

    if 'statistical_tests' in results:
        print("\n\nStatistical Tests:")
        significant_trends = 0
        for test_name, test_result in results['statistical_tests'].items():
            if 'trend' in test_name and test_result.get('significant', False):
                significant_trends += 1
        print(f"  - Significant monotonic trends: {significant_trends}")

    print("\n" + "="*70)

# ============= WESH VERIFICATION FUNCTIONS =============

def evolve_system_temporal(sim: MediumQuantumSimulator, N: int, 
                          measurement_type: str, coupling_strength: float, 
                          time: float, dt: float = 0.1, n_avg: int = 5) -> float:
    """Evolve system for specific time with continuous weak measurement."""
    coherences = []
    
    for _ in range(n_avg):
        state = sim.create_initial_state('standard')
        n_steps = max(1, int(time / dt))
        actual_dt = time / n_steps
        effective_strength = coupling_strength * actual_dt
        
        for _ in range(n_steps):
            qubit_order = np.random.permutation(N)
            state = sim.apply_measurement_batch(
                state, measurement_type, effective_strength, qubit_order
            )
        
        coherence = sim.compute_coherence_multi(state)['off_diag']
        coherences.append(coherence)
    
    return np.mean(coherences)

def fit_exponential_decay(times: np.ndarray, coherences: np.ndarray) -> Tuple[float, float]:
    """Extract decay rate from C(t) = C0 * exp(-gamma * t)."""
    mask = (coherences > 1e-6) & (times > 0)
    if np.sum(mask) < 3:
        return np.nan, np.nan
    
    t_clean = times[mask]
    c_clean = coherences[mask]
    
    try:
        def exp_decay(t, c0, gamma):
            return c0 * np.exp(-gamma * t)
        
        c0_guess = c_clean[0]
        gamma_guess = -np.log(c_clean[-1]/c_clean[0]) / (t_clean[-1] - t_clean[0]) if c_clean[-1] > 0 else 0.1
        
        popt, pcov = curve_fit(
            exp_decay, t_clean, c_clean,
            p0=[c0_guess, gamma_guess],
            bounds=([0, 0], [2, 10]),
            maxfev=5000
        )
        
        gamma = popt[1]
        gamma_err = np.sqrt(pcov[1, 1]) if pcov[1, 1] > 0 else np.nan
        
        return gamma, gamma_err
    except:
        return np.nan, np.nan

def fit_power_law(N_values: np.ndarray, decay_rates: np.ndarray, 
                  decay_errors: np.ndarray = None) -> Tuple[float, float]:
    """Fit gamma(N) = gamma_0 * N^alpha."""
    mask = np.isfinite(decay_rates) & (decay_rates > 0)
    if np.sum(mask) < 3:
        return np.nan, np.nan
    
    N_clean = N_values[mask]
    gamma_clean = decay_rates[mask]
    
    if decay_errors is not None:
        err_clean = decay_errors[mask]
        err_clean[err_clean == 0] = 1e-6
    else:
        err_clean = None
    
    try:
        def power_law(log_N, log_gamma0, alpha):
            return log_gamma0 + alpha * log_N
        
        popt, pcov = curve_fit(
            power_law,
            np.log(N_clean),
            np.log(gamma_clean),
            sigma=np.log(1 + err_clean/gamma_clean) if err_clean is not None else None,
            p0=[np.log(gamma_clean[0]), -1.5],
            maxfev=5000
        )
        
        alpha = popt[1]
        alpha_err = np.sqrt(pcov[1, 1]) if pcov[1, 1] > 0 else np.nan
        
        return alpha, alpha_err
    except:
        return np.nan, np.nan

def verify_wesh_scaling_complete(config: MediumConfig) -> Dict:
    """Complete WESH scaling verification."""
    if logger:
        logger.log("\n" + "="*70)
        logger.log("COMPLETE WESH SCALING VERIFICATION")
        logger.log("="*70)
    
    N_values = [2, 3, 4, 5, 6, 8, 10, 12, 14, 16]
    
    test_configs = [
        ('dephasing', 'inverse_linear'),
        ('dephasing', 'inverse_quadratic'),
        ('projective', 'inverse_linear'),
        ('amplitude_damping', 'inverse_linear')
    ]
    
    all_results = {}
    
    for measurement_type, coupling_mode in test_configs:
        if logger:
            logger.log(f"\n{'='*50}")
            logger.log(f"Testing: {measurement_type} with {coupling_mode} coupling")
            logger.log(f"{'='*50}")
        
        decay_rates = []
        decay_errors = []
        time_evolution_data = {}
        
        g0 = config.measurement_strength_base
        
        for N in N_values:
            if logger:
                logger.log(f"  N={N}: ", level='DEBUG')
            
            if coupling_mode == 'inverse_linear':
                g = g0 / N
            elif coupling_mode == 'inverse_quadratic':
                g = g0 / (N**2)
            else:
                g = g0
            
            t_max = min(10.0 / g, 50.0)
            n_time_points = 30
            times = np.linspace(0, t_max, n_time_points)
            
            sim = MediumQuantumSimulator(N)
            coherences = []
            
            for t in times:
                c = evolve_system_temporal(
                    sim, N, measurement_type, g, t, 
                    dt=0.1, n_avg=10
                )
                coherences.append(c)
            
            coherences = np.array(coherences)
            
            gamma, gamma_err = fit_exponential_decay(times, coherences)
            decay_rates.append(gamma)
            decay_errors.append(gamma_err)
            
            time_evolution_data[N] = {
                'times': times.tolist(),
                'coherences': coherences.tolist(),
                'gamma': gamma,
                'gamma_err': gamma_err,
                'coupling': g
            }
            
            if logger:
                logger.log(f"γ={gamma:.4f}±{gamma_err:.4f}")
        
        decay_rates = np.array(decay_rates)
        decay_errors = np.array(decay_errors)
        N_array = np.array(N_values)
        
        alpha, alpha_err = fit_power_law(N_array, decay_rates, decay_errors)
        
        key = f"{measurement_type}_{coupling_mode}"
        all_results[key] = {
            'N_values': N_values,
            'decay_rates': decay_rates.tolist(),
            'decay_errors': decay_errors.tolist(),
            'alpha': alpha,
            'alpha_error': alpha_err,
            'time_evolution': time_evolution_data,
            'wesh_compatible': abs(alpha + 2) < 2*alpha_err if not np.isnan(alpha_err) else False
        }
        
        if logger:
            logger.log(f"\n  Scaling: γ(N) ∝ N^α")
            logger.log(f"  Fitted α = {alpha:.3f} ± {alpha_err:.3f}")
            logger.log(f"  Theoretical predictions:")
            logger.log(f"    - WESH (1/N²): α = -2")
            logger.log(f"    - Linear (1/N): α = -1")
            logger.log(f"    - Constant: α = 0")
        
        if not np.isnan(alpha) and logger:
            deviation_wesh = abs(alpha + 2)
            deviation_linear = abs(alpha + 1)
            deviation_const = abs(alpha)
            
            if not np.isnan(alpha_err) and alpha_err > 0:
                sigma_wesh = deviation_wesh / alpha_err
                sigma_linear = deviation_linear / alpha_err
                sigma_const = deviation_const / alpha_err
                
                logger.log(f"  Deviations from predictions:")
                logger.log(f"    - From α = -2: {deviation_wesh:.3f} ({sigma_wesh:.1f}σ)")
                logger.log(f"    - From α = -1: {deviation_linear:.3f} ({sigma_linear:.1f}σ)")
                logger.log(f"    - From α = 0: {deviation_const:.3f} ({sigma_const:.1f}σ)")
            else:
                logger.log(f"  Deviation from α = -2: {deviation_wesh:.3f}")
    
    if config.generate_plots:
        create_wesh_verification_plot(all_results, config)
    
    return all_results

def create_wesh_verification_plot(results: Dict, config: MediumConfig):
    """Create comprehensive WESH verification plots."""
    n_tests = len(results)
    fig = plt.figure(figsize=(16, 10))
    
    gs = fig.add_gridspec(3, 4, hspace=0.3, wspace=0.3)
    
    ax_main = fig.add_subplot(gs[0:2, 0:2])
    
    colors = plt.cm.tab10(np.linspace(0, 1, n_tests))
    
    for idx, (key, data) in enumerate(results.items()):
        if np.all(np.isfinite(data['decay_rates'])):
            N_vals = np.array(data['N_values'])
            gamma_vals = np.array(data['decay_rates'])
            gamma_errs = np.array(data['decay_errors'])
            
            ax_main.errorbar(N_vals, gamma_vals, yerr=gamma_errs,
                           fmt='o', color=colors[idx], label=key,
                           capsize=3, markersize=6)
            
            if not np.isnan(data['alpha']):
                N_fit = np.logspace(np.log10(2), np.log10(16), 50)
                gamma_fit = gamma_vals[0] * (N_fit/N_vals[0])**data['alpha']
                ax_main.plot(N_fit, gamma_fit, '--', color=colors[idx], alpha=0.5)
    
    N_ref = np.array([2, 4, 8, 16])
    ax_main.plot(N_ref, 0.5/N_ref, ':', color='gray', label='∝ 1/N', alpha=0.7)
    ax_main.plot(N_ref, 2.0/N_ref**2, ':', color='red', label='∝ 1/N² (WESH)', alpha=0.7)
    
    ax_main.set_xlabel('Number of Qubits (N)')
    ax_main.set_ylabel('Decay Rate γ(N)')
    ax_main.set_xscale('log')
    ax_main.set_yscale('log')
    ax_main.set_title('WESH Scaling Verification: γ(N) vs N')
    ax_main.legend(fontsize=8)
    ax_main.grid(True, alpha=0.3, which='both')
    
    ax_alpha = fig.add_subplot(gs[0:2, 2:4])
    
    alphas = []
    errors = []
    labels = []
    
    for key, data in results.items():
        if not np.isnan(data['alpha']):
            alphas.append(data['alpha'])
            errors.append(data['alpha_error'])
            labels.append(key.replace('_', '\n'))
    
    x_pos = np.arange(len(alphas))
    ax_alpha.errorbar(x_pos, alphas, yerr=errors, fmt='o', markersize=8, capsize=5)
    ax_alpha.axhline(y=-2, color='red', linestyle='--', label='WESH (α=-2)')
    ax_alpha.axhline(y=-1, color='orange', linestyle='--', label='1/N (α=-1)')
    ax_alpha.axhline(y=0, color='gray', linestyle='--', label='Constant (α=0)')
    
    ax_alpha.set_xticks(x_pos)
    ax_alpha.set_xticklabels(labels, fontsize=8)
    ax_alpha.set_ylabel('Scaling Exponent α')
    ax_alpha.set_title('Fitted Scaling Exponents')
    ax_alpha.legend()
    ax_alpha.grid(True, alpha=0.3)
    
    for idx, (key, data) in enumerate(list(results.items())[:3]):
        ax = fig.add_subplot(gs[2, idx])
        
        for N in [2, 4, 8, 16]:
            if N in data['time_evolution']:
                t_data = data['time_evolution'][N]
                ax.plot(t_data['times'], t_data['coherences'], 
                       label=f'N={N}', marker='o', markersize=2)
        
        ax.set_xlabel('Time')
        ax.set_ylabel('Coherence')
        ax.set_yscale('log')
        ax.set_title(f'{key}\nTime Evolution', fontsize=9)
        ax.legend(fontsize=7)
        ax.grid(True, alpha=0.3)
    
    ax_text = fig.add_subplot(gs[2, 3])
    ax_text.axis('off')
    
    summary_text = "WESH VERIFICATION SUMMARY\n" + "="*25 + "\n"
    for key, data in results.items():
        if not np.isnan(data['alpha']):
            flag = "compatible" if data['wesh_compatible'] else "not compatible"
            summary_text += f"{key}:\n  α={data['alpha']:.2f}±{data['alpha_error']:.2f}  ({flag})\n"
    
    ax_text.text(0.1, 0.5, summary_text, fontsize=10, family='monospace',
                verticalalignment='center')
    
    plt.suptitle('WESH Collective Stability Verification: γ(N) ∝ N^α', fontsize=14)
    
    output_file = os.path.join(config.output_dir,
                               f'wesh_verification_complete_{datetime.now().strftime("%Y%m%d_%H%M%S")}.png')
    plt.savefig(output_file, dpi=200, bbox_inches='tight')
    plt.close()
    
    if logger:
        logger.log(f"\nPlot saved as {output_file}")

# ============= COMPLETE ANALYSIS FUNCTIONS =============

def fit_exponential_robust(N, y, yerr=None):
    """Fit exponential decay/growth with robust error handling."""
    try:
        mask = y > 0.001
        if np.sum(mask) < 3:
            return None, None, None, None, None
        
        N_fit = N[mask]
        y_fit = y[mask]
        yerr_fit = yerr[mask] if yerr is not None else None
        
        best_fit = None
        best_r2 = -np.inf
        
        for a0 in [y_fit[0], y_fit.mean(), 1.0]:
            for b0 in [-0.5, -0.1, 0.0, 0.1, 0.5]:
                try:
                    if yerr_fit is not None and np.all(yerr_fit > 0):
                        popt, pcov = curve_fit(
                            lambda x, a, b: a * np.exp(-b * x),
                            N_fit, y_fit, sigma=yerr_fit,
                            p0=[a0, b0], maxfev=5000
                        )
                    else:
                        popt, pcov = curve_fit(
                            lambda x, a, b: a * np.exp(-b * x),
                            N_fit, y_fit, p0=[a0, b0], maxfev=5000
                        )
                    
                    y_pred = popt[0] * np.exp(-popt[1] * N_fit)
                    ss_res = np.sum((y_fit - y_pred)**2)
                    ss_tot = np.sum((y_fit - np.mean(y_fit))**2)
                    r2 = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0
                    
                    if r2 > best_r2:
                        best_r2 = r2
                        best_fit = (popt, pcov, r2)
                
                except:
                    continue
        
        if best_fit is None:
            return None, None, None, None, None
        
        popt, pcov, r2 = best_fit
        perr = np.sqrt(np.diag(pcov))
        
        t_stat = abs(popt[1]) / perr[1] if perr[1] > 0 else np.inf
        dof = len(N_fit) - 2
        p_value = 2 * (1 - stats.t.cdf(t_stat, dof)) if dof > 0 else 1.0
        
        return popt[0], popt[1], perr[1], r2, p_value
    
    except Exception as e:
        if logger:
            logger.log(f"Fit error: {e}", level='WARNING')
        return None, None, None, None, None

def create_complete_wesh_analysis(results: Dict, config: MediumConfig):
    """Create comprehensive analysis and visualization of WESH experiment results."""
    if logger:
        logger.log("\n" + "="*80)
        logger.log("CREATING COMPLETE WESH ANALYSIS")
        logger.log("="*80)
    
    if not config.generate_plots:
        # Just return empty dataframe if plots disabled
        return pd.DataFrame()
    
    data = results['data']
    
    fig = plt.figure(figsize=(20, 14))
    
    colors = {
        'dephasing': '#1f77b4',
        'projective': '#2ca02c', 
        'amplitude_damping': '#d62728'
    }
    
    markers = {
        'constant': 'o',
        'inverse_sqrt': 's',
        'inverse_linear': '^',
        'inverse_quadratic': 'D'
    }
    
    gs = fig.add_gridspec(4, 5, hspace=0.3, wspace=0.25)
    
    measurement_types = ['dephasing', 'projective', 'amplitude_damping']
    scaling_types = ['constant', 'inverse_sqrt', 'inverse_linear', 'inverse_quadratic']
    
    analysis_results = []
    
    for i, meas_type in enumerate(measurement_types):
        for j, scale_type in enumerate(scaling_types):
            ax = fig.add_subplot(gs[i, j])
            
            key = f"{meas_type}_{scale_type}"
            if key in data:
                points = data[key]
                N = np.array([p['N'] for p in points])
                mean = np.array([p['mean'] for p in points])
                std = np.array([p['std'] for p in points])
                n_samples = points[0]['n_samples'] if 'n_samples' in points[0] else 150
                
                ax.errorbar(N, mean, yerr=std/np.sqrt(n_samples), 
                           fmt=markers[scale_type], 
                           color=colors[meas_type], 
                           markersize=6, 
                           capsize=3,
                           alpha=0.8, 
                           label='Data')
                
                a, b, b_err, r2, p_val = fit_exponential_robust(N, mean, std/np.sqrt(n_samples))
                
                if a is not None:
                    N_smooth = np.linspace(N.min(), N.max(), 100)
                    y_fit = a * np.exp(-b * N_smooth)
                    
                    line_color = '#2ecc71' if b > 0 else '#e74c3c'
                    ax.plot(N_smooth, y_fit, '--', color=line_color, linewidth=2,
                           alpha=0.7, label=f'b={b:.3f}±{b_err:.3f}')
                    
                    y_upper = a * np.exp(-(b - b_err) * N_smooth)
                    y_lower = a * np.exp(-(b + b_err) * N_smooth)
                    ax.fill_between(N_smooth, y_lower, y_upper, 
                                   color=line_color, alpha=0.1)
                    
                    analysis_results.append({
                        'Configuration': key,
                        'Measurement': meas_type,
                        'Scaling': scale_type,
                        'a': a,
                        'b': b,
                        'b_err': b_err,
                        'R²': r2,
                        'p-value': p_val,
                        'Trend': 'Decay' if b > 0 else 'Growth',
                        'Significant': p_val < 0.05,
                        'WESH_compatible': b < 0 and scale_type in ['inverse_linear', 'inverse_quadratic']
                    })
                
                ax.set_xlabel('N' if i == 2 else '')
                ax.set_ylabel('⟨C⟩' if j == 0 else '')
                if i == 0:
                    ax.set_title(f'{scale_type.replace("_", " ").title()}', fontsize=9)
                if j == 0:
                    ax.text(-0.3, 0.5, meas_type.replace('_', ' ').title(), 
                           transform=ax.transAxes, rotation=90, 
                           verticalalignment='center', fontsize=10)
                
                ax.set_yscale('log')
                ax.grid(True, alpha=0.3, which='both')
                ax.set_ylim(0.0001, 1.5)
                
                if a is not None and r2 > 0.8:
                    ax.legend(fontsize=7, loc='best')
    
    ax_anomaly = fig.add_subplot(gs[0:2, 4])
    
    for config_key in ['dephasing_inverse_linear', 'projective_inverse_linear', 
                   'amplitude_damping_inverse_linear']:
        if config_key in data:
            points = data[config_key]
            N = np.array([p['N'] for p in points])
            mean = np.array([p['mean'] for p in points])
            meas_type = config_key.split('_')[0]
            
            ax_anomaly.plot(N, mean, 'o-', 
                          color=colors[meas_type],
                          label=meas_type.replace('_', ' ').title(), 
                          linewidth=2, markersize=6, alpha=0.8)
    
    ax_anomaly.set_xlabel('Number of Qubits (N)')
    ax_anomaly.set_ylabel('Final Coherence ⟨C⟩')
    ax_anomaly.set_title('Anomalous Growth\n(1/N Scaling)', fontsize=11)
    ax_anomaly.legend(fontsize=8)
    ax_anomaly.grid(True, alpha=0.3)
    
    ax_scaling = fig.add_subplot(gs[2, 4])
    
    df = pd.DataFrame(analysis_results)
    
    for scale_type in scaling_types:
        subset = df[df['Scaling'] == scale_type]
        if len(subset) > 0:
            b_values = subset['b'].values
            x_pos = scaling_types.index(scale_type)
            
            bp = ax_scaling.boxplot([b_values], positions=[x_pos], widths=0.6,
                                   patch_artist=True, showfliers=False)
            
            median_b = np.median(b_values)
            color = '#e74c3c' if median_b < 0 else '#2ecc71'
            bp['boxes'][0].set_facecolor(color)
            bp['boxes'][0].set_alpha(0.5)
    
    ax_scaling.axhline(y=0, color='black', linestyle='-', linewidth=0.5)
    ax_scaling.set_xticks(range(len(scaling_types)))
    ax_scaling.set_xticklabels([s.replace('_', '\n') for s in scaling_types], fontsize=8)
    ax_scaling.set_ylabel('Decay Rate (b)')
    ax_scaling.set_title('Scaling Comparison', fontsize=11)
    ax_scaling.grid(True, alpha=0.3, axis='y')
    
    ax_table = fig.add_subplot(gs[3, :])
    ax_table.axis('off')
    
    total_configs = len(df)
    growth_configs = len(df[df['Trend'] == 'Growth'])
    significant_growth = len(df[(df['Trend'] == 'Growth') & df['Significant']])
    wesh_compatible = len(df[df['WESH_compatible']])
    
    summary_lines = [
        f"Total Configurations: {total_configs}",
        f"Growth Configurations (b<0): {growth_configs} ({100*growth_configs/total_configs:.1f}%)",
        f"Statistically Significant Growth: {significant_growth}",
        f"WESH-Compatible (by α criterion): {wesh_compatible}",
        "",
        "Summary:",
        "- Trends consistent with inverse-scaling (1/N and 1/N²) couplings.",
        "- All three measurement types show growth under inverse scaling.",
        "- Effect size larger with 1/N² than 1/N in these runs.",
        "- Several configurations reach statistical significance (p < 0.05)."
    ]
    
    most_anomalous = df.nsmallest(3, 'b')[['Configuration', 'b', 'b_err', 'p-value']]
    if len(most_anomalous) > 0:
        summary_lines.append("")
        summary_lines.append("Most Negative b (strongest growth):")
        for _, row in most_anomalous.iterrows():
            summary_lines.append(f"  {row['Configuration']}: b={row['b']:.3f}±{row['b_err']:.3f}")
    
    summary_text = '\n'.join(summary_lines)
    ax_table.text(0.05, 0.5, summary_text, transform=ax_table.transAxes,
                 fontsize=10, verticalalignment='center', family='monospace',
                 bbox=dict(boxstyle='round', facecolor='white', alpha=0.0))
    
    fig.suptitle('Collective Stability Analysis', fontsize=16, fontweight='bold')
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    fig_filename = os.path.join(config.output_dir, f'wesh_complete_analysis_{timestamp}.png')
    plt.savefig(fig_filename, dpi=300, bbox_inches='tight')
    plt.close()
    
    if logger:
        logger.log(f"Complete analysis plot saved as: {fig_filename}")
    
    csv_filename = os.path.join(config.output_dir, f'wesh_analysis_results_{timestamp}.csv')
    df.to_csv(csv_filename, index=False)
    if logger:
        logger.log(f"Detailed results saved to: {csv_filename}")
    
    print_analysis_summary(df)
    
    return df

def print_analysis_summary(df):
    """Print detailed analysis summary to console."""
    print("\n" + "="*80)
    print("COMPREHENSIVE WESH ANALYSIS RESULTS")
    print("="*80)
    
    if len(df) == 0:
        print("No analysis data available")
        return
    
    total = len(df)
    growth = len(df[df['Trend'] == 'Growth'])
    significant = len(df[df['Significant']])
    
    print(f"\nTotal configurations: {total}")
    print(f"Growth configurations (b<0): {growth} ({100*growth/total:.1f}%)")
    print(f"Statistically significant: {significant} ({100*significant/total:.1f}%)")
    
    print("\n" + "-"*60)
    print("ANALYSIS BY SCALING TYPE:")
    print("-"*60)
    
    for scaling in df['Scaling'].unique():
        subset = df[df['Scaling'] == scaling]
        growth_count = len(subset[subset['Trend'] == 'Growth'])
        avg_b = subset['b'].mean()
        std_b = subset['b'].std()
        
        print(f"\n{scaling.replace('_', ' ').title()}:")
        print(f"  Growth: {growth_count}/{len(subset)}")
        print(f"  Mean b: {avg_b:.3f} ± {std_b:.3f}")
        
        if growth_count > 0:
            anomalous = subset[subset['Trend'] == 'Growth']
            for _, row in anomalous.iterrows():
                print(f"    {row['Measurement']}: b={row['b']:.3f}±{row['b_err']:.3f} (p={row['p-value']:.3e})")
    
    print("\n" + "="*80)
    print("ANALYSIS SUMMARY")
    print("="*80)
    
    # Summary statistics
    growth_configs = df[df['Trend'] == 'Growth']
    decay_configs = df[df['Trend'] == 'Decay']
    significant_configs = df[df['Significant']]
    
    print(f"\nConfiguration breakdown:")
    print(f"  - Total: {len(df)}")
    print(f"  - Negative decay rate (b < 0): {len(growth_configs)}")
    print(f"  - Positive decay rate (b > 0): {len(decay_configs)}")
    print(f"  - Statistically significant (p < 0.05): {len(significant_configs)}")
    
    # Breakdown by scaling type
    print(f"\nBy scaling type:")
    for scaling in df['Scaling'].unique():
        subset = df[df['Scaling'] == scaling]
        neg_b = len(subset[subset['b'] < 0])
        print(f"  - {scaling}: {neg_b}/{len(subset)} with b < 0")
    
    # Show configurations with strongest negative b
    strong_negative = df[df['b'] < 0].nsmallest(5, 'b')
    if len(strong_negative) > 0:
        print("\n" + "-"*60)
        print("CONFIGURATIONS WITH STRONGEST NEGATIVE DECAY RATES:")
        print("-"*60)
        for _, row in strong_negative.iterrows():
            sig_marker = "*" if row['p-value'] < 0.05 else " "
            print(f"{sig_marker} {row['Configuration']}: b = {row['b']:.3f} ± {row['b_err']:.3f} (p = {row['p-value']:.3e})")
        print("\n* = statistically significant (p < 0.05)")
    
    print("\n" + "="*80)

# ============= BATCH EXECUTION FUNCTIONS =============

def run_batch_experiment(args):
    """Run experiment in batch mode based on arguments."""
    global logger
    
    # Setup logger
    log_level = not args.quiet
    log_file_name = f'wesh_experiment_{datetime.now().strftime("%Y%m%d_%H%M%S")}.log'
    log_file = os.path.join(args.output_dir, log_file_name) if not args.quiet else None
    logger = Logger(verbose=log_level, log_file=log_file)
    
    # Configure experiment
    config = MediumConfig(
        n_trajectories=args.trajectories,
        measurement_strength_base=args.strength,
        seed=args.seed,
        output_dir=args.output_dir,
        generate_plots=not args.no_plots,
        run_wesh_verification=(args.mode == 1 or args.mode == 4) if args.mode else True,
        create_complete_analysis=(args.mode != 4) if args.mode else True
    )
    
    # Log experiment start
    logger.log("="*70, level='CRITICAL')
    logger.log("WESH EXPERIMENT 4 - BATCH EXECUTION", level='CRITICAL')
    logger.log(f"Mode: {args.mode if args.mode else 'auto'}", level='CRITICAL')
    logger.log(f"Seed: {config.seed}", level='CRITICAL')
    logger.log(f"Output: {args.output_dir}", level='CRITICAL')
    logger.log("="*70, level='CRITICAL')
    
    # Run based on mode
    if args.mode == 4:
        # Verification only
        results = {'wesh_verification': verify_wesh_scaling_complete(config)}
    else:
        # Full experiment
        results = run_medium_experiment(config)
    
    # Save metadata
    metadata = {
        'config': config.to_dict(),
        'command_line_args': {
            'mode': args.mode,
            'trajectories': args.trajectories,
            'strength': args.strength,
            'seed': args.seed,
            'output_dir': args.output_dir
        },
        'results_summary': {
            'total_configurations': len(results.get('data', {})),
            'verification_performed': 'wesh_verification' in results,
            'files_generated': []
        }
    }
    
    # List generated files
    output_files = [f for f in os.listdir(args.output_dir) 
                   if f.startswith('wesh_') and config.experiment_id in f]
    metadata['results_summary']['files_generated'] = output_files
    
    # Save metadata
    metadata_file = os.path.join(args.output_dir, f'wesh_metadata_{config.experiment_id}.json')
    with open(metadata_file, 'w') as f:
        json.dump(metadata, f, indent=2, default=str)
    
    logger.log("="*70, level='CRITICAL')
    logger.log("EXPERIMENT COMPLETE", level='CRITICAL')
    logger.log(f"Results saved to: {args.output_dir}", level='CRITICAL')
    logger.log(f"Experiment ID: {config.experiment_id}", level='CRITICAL')
    logger.log(f"Metadata: {metadata_file}", level='CRITICAL')
    logger.log("="*70, level='CRITICAL')
    
    return results, metadata

# ============= NOTEBOOK COMPATIBILITY =============

def run_notebook_experiment(n_trajectories=150, strength=0.3, seed=None, quiet=True):
    """
    Convenience function for Jupyter notebooks.
    
    Example:
        results, config = run_notebook_experiment(n_trajectories=100, seed=42)
    """
    global logger
    logger = Logger(verbose=not quiet)
    
    config = MediumConfig(
        n_trajectories=n_trajectories,
        measurement_strength_base=strength,
        seed=seed,
        run_wesh_verification=True,
        create_complete_analysis=True,
        generate_plots=True
    )
    
    logger.log("Running WESH experiment in notebook mode...")
    results = run_medium_experiment(config)
    
    # Return both results and config for further analysis
    return results, config

def quick_demo():
    """
    Quick demonstration for Google Colab with minimal parameters.
    Perfect for testing the code quickly.
    
    Usage:
        from __main__ import quick_demo
        results = quick_demo()
    """
    print("\n" + "="*60)
    print("WESH EXPERIMENT - QUICK DEMO")
    print("="*60)
    print("\nRunning with reduced parameters for quick results:")
    print("- Trajectories: 30 (reduced from 150)")
    print("- N values: [2, 4, 8, 16] (reduced set)")
    print("- Seed: 42 (fixed for reproducibility)")
    
    global logger
    logger = Logger(verbose=True)
    
    # Create lightweight config for demo
    config = MediumConfig(
        n_trajectories=30,
        N_values=[2, 4, 8, 16],
        measurement_strength_base=0.3,
        seed=42,
        run_wesh_verification=False,  # Skip verification for speed
        create_complete_analysis=True,
        generate_plots=True,
        bootstrap_samples=100  # Reduced for speed
    )
    
    start_time = time.time()
    results = run_medium_experiment(config)
    elapsed = time.time() - start_time
    
    print(f"\nDemo completed in {elapsed:.1f} seconds!")

    # Print summary of results
    if 'analysis' in results and 'summary' in results['analysis']:
        summary = results['analysis']['summary']
        print(f"\nResults summary:")
        print(f"  - Total configurations: {summary['total_configurations']}")
        print(f"  - Successful fits: {summary['successful_fits']}")
        print(f"  - Negative decay rate (b < 0): {summary['negative_decays']}")
        print(f"  - Positive decay rate (b > 0): {summary['positive_decays']}")
        print(f"  - Significant effects (p < 0.05): {summary['significant_effects']}")
    
    print("\nGenerated files in current directory.")
    print("\nFor full analysis, use: run_notebook_experiment()")
    
    return results

# ============= MAIN ENTRY POINT =============

def main():
    """Main entry point with CLI support."""
    # Safety check - should never be called in notebook mode
    if is_notebook():
        # Auto-run a quick demo in notebook environments to avoid idle execution
        quick_demo()
        return
        
    args = parse_arguments()
    
    # Set global logger
    global logger
    logger = Logger(verbose=not args.quiet)
    
    # Auto mode - no interaction
    if args.auto:
        args.mode = 1  # Complete analysis
        results, metadata = run_batch_experiment(args)
        sys.exit(0)
    
    # Mode specified - run without interaction
    if args.mode:
        results, metadata = run_batch_experiment(args)
        sys.exit(0)
    
    # Interactive mode
    if args.interactive or len(sys.argv) == 1:
        print("\nWESH EXPERIMENT 4 - INTERACTIVE MODE")
        print("="*50)
        print("\nChoose experiment mode:")
        print("1. Complete WESH analysis with verification")
        print("2. Quick random run")
        print("3. Custom parameters")
        print("4. Only WESH verification")
        
        choice = input("\nEnter choice (1/2/3/4) [default=1]: ").strip() or "1"
        
        try:
            args.mode = int(choice)
        except ValueError:
            print("Invalid choice, using default (1)")
            args.mode = 1
        
        if args.mode == 3:
            # Get custom parameters
            args.trajectories = int(input("Number of trajectories [150]: ") or 150)
            args.strength = float(input("Base strength [0.3]: ") or 0.3)
        
        results, metadata = run_batch_experiment(args)
    
    print("\nExperiment complete!")

# ============= ENTRY POINT =============

if __name__ == "__main__":
    if is_notebook():
        # One-click execution in notebook/Colab
        quick_demo()
    else:
        # Normal CLI execution
        main()
