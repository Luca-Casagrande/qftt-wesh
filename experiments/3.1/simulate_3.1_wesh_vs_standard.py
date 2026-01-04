# Simulation: WESH vs. Standard Decoherence vs. Pure WDW - Stability Analysis
# Metrics: Purity, Coherence
# Date: 2025-11-09

import numpy as np
import matplotlib.pyplot as plt
from scipy.linalg import expm
from scipy import stats
import time
from dataclasses import dataclass, field
import warnings
import pandas as pd
from datetime import datetime
import os

# Ignore non-critical warnings
warnings.filterwarnings('ignore', category=RuntimeWarning)

# --- SUPPORT CLASSES ---

@dataclass
class SimulationResult:
    """Container for simulation scenario results."""
    name: str
    N_values: np.ndarray
    final_variances: np.ndarray
    final_purities: np.ndarray
    final_coherences: np.ndarray
    computation_times: np.ndarray
    scaling_exponent: float = np.nan
    purity_scaling_exponent: float = np.nan
    coherence_scaling_exponent: float = np.nan
    variances_vs_time: dict = field(default_factory=dict)
    purities_vs_time: dict = field(default_factory=dict)
    coherences_vs_time: dict = field(default_factory=dict)

class WESHOptimizedTest:
    """
    Performs comparative stability simulations.
    Calculates Purity, Coherence, and Variance (for scaling summary).
    """
    def __init__(self, N_values, time_steps, dt, memory_limit_gb=None, verbose=False):
        """
        Initialize test suite.

        Args:
            N_values (list): List of system sizes N.
            time_steps (int): Number of steps in time evolution.
            dt (float): Time step size.
            memory_limit_gb (float, optional): Memory guardrail.
            verbose (bool, optional): Print simulation progress.
        """
        self.N_values = sorted(N_values)
        self.time_steps = time_steps
        self.dt = dt
        self.verbose = verbose

        self.timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.output_dir = f"wesh_results_{self.timestamp}"
        os.makedirs(self.output_dir, exist_ok=True)

        # Memory management and data type
        self._dtype = np.complex128
        if memory_limit_gb is not None:
            limit_bytes = memory_limit_gb * (1024**3) * 0.9
            allowed_N = []
            for N in self.N_values:
                dim = 2 ** N
                bytes_per_element = 16
                estimated_bytes = (dim**2) * bytes_per_element * 3 # Heuristic

                if estimated_bytes > limit_bytes:
                    if self._dtype is np.complex128:
                        self._dtype = np.complex64
                        bytes_per_element = 8
                        estimated_bytes = (dim**2) * bytes_per_element * 3
                        if estimated_bytes <= limit_bytes:
                            if verbose:
                                print(f"[Memory] Switching to 32-bit floats for N >= {N}")
                            allowed_N.append(N)
                            continue
                    if verbose:
                        print(f"[Memory] N={N} removed from tests (exceeds memory limit)")
                    break
                allowed_N.append(N)
            self.N_values = allowed_N

        # Pauli matrices
        self.sx = np.array([[0, 1], [1, 0]], dtype=self._dtype)
        self.sy = np.array([[0, -1j], [1j, 0]], dtype=self._dtype)
        self.sz = np.array([[1, 0], [0, -1]], dtype=self._dtype)
        self.si = np.eye(2, dtype=self._dtype)

        # Operator cache
        self._operators_cache = {}
        if verbose:
            print(f"Initialized: N={self.N_values}, steps={time_steps}, dt={dt}")
            print(f"Output directory: {self.output_dir}")

    def _tensor_product(self, ops):
        """Calculate Kronecker product of operators."""
        result = ops[0]
        for op in ops[1:]:
            result = np.kron(result, op)
        return result

    def _build_operators(self, N):
        """Build collective time operator T and Hamiltonian H."""
        if N in self._operators_cache:
            return self._operators_cache[N]

        dim = 2 ** N
        T_op = np.zeros((dim, dim), dtype=self._dtype)
        H_matter = np.zeros((dim, dim), dtype=self._dtype)

        j_coupling = -1.0
        h_field = -0.5

        for i in range(N):
            ops_t = [self.si] * N
            ops_t[i] = self.sx
            T_op += self._tensor_product(ops_t)

            ops_h = [self.si] * N
            ops_h[i] = self.sx
            H_matter += h_field * self._tensor_product(ops_h)

            ops_j = [self.si] * N
            ops_j[i] = self.sz
            ops_j[(i + 1) % N] = self.sz
            H_matter += j_coupling * self._tensor_product(ops_j)

        T_op /= np.sqrt(N)
        self._operators_cache[N] = (T_op, H_matter)
        return T_op, H_matter

    def _initial_state_ghz(self, N):
        """Prepare standard GHZ initial state."""
        dim = 2 ** N
        psi = np.zeros(dim, dtype=self._dtype)
        psi[0] = 1 / np.sqrt(2)
        psi[-1] = 1 / np.sqrt(2)
        return psi

    def _calculate_variance(self, rho, op):
        """Calculate expectation value ⟨(ΔOp)²⟩ = ⟨Op²⟩ - ⟨Op⟩²."""
        if np.any(np.isnan(rho)) or np.any(np.isinf(rho)): return np.nan
        exp_val = np.real(np.trace(rho @ op))
        exp_val_sq = np.real(np.trace(rho @ op @ op))
        return max(exp_val_sq - exp_val**2, 0.0)

    def _calculate_purity(self, rho):
        """Calculate density matrix purity Tr(ρ²)."""
        if np.any(np.isnan(rho)) or np.any(np.isinf(rho)): return np.nan
        return np.real(np.trace(rho @ rho))

    def _calculate_coherence(self, rho):
        """Calculate L1-norm of coherence (sum of off-diagonal magnitudes)."""
        if np.any(np.isnan(rho)) or np.any(np.isinf(rho)): return np.nan
        return np.sum(np.abs(rho - np.diag(np.diag(rho))))

    def _run_simulation(self, N, H_total, L_ops=None):
        """
        Generic helper to run time evolution (Unitary + Lindblad).

        Returns:
            (np.ndarray): variances_over_time
            (np.ndarray): purities_over_time
            (np.ndarray): coherences_over_time
            (np.ndarray): final_density_matrix
        """
        psi0 = self._initial_state_ghz(N)
        rho = np.outer(psi0, psi0.conj())

        variances = np.zeros(self.time_steps)
        purities = np.zeros(self.time_steps)
        coherences = np.zeros(self.time_steps)

        U = expm(-1j * self.dt * H_total)
        L_dagL_terms = [L.conj().T @ L for L in L_ops] if L_ops is not None else []

        for t in range(self.time_steps):
            # Unitary evolution
            rho = U @ rho @ U.conj().T

            # Dissipative evolution
            if L_ops is not None:
                dissipative_change = np.zeros_like(rho)
                for i in range(len(L_ops)):
                    L = L_ops[i]
                    L_dagL = L_dagL_terms[i]
                    dissipative_change += L @ rho @ L.conj().T - 0.5 * (L_dagL @ rho + rho @ L_dagL)
                rho += self.dt * dissipative_change

            # Renormalization
            trace_rho = np.trace(rho)
            if abs(trace_rho) < 1e-15 or np.isnan(trace_rho) or np.isinf(trace_rho):
                variances[t:], purities[t:], coherences[t:] = np.nan, np.nan, np.nan
                rho = None
                break
            rho /= trace_rho

            # Calculate metrics
            variances[t] = self._calculate_variance(rho, self._operators_cache[N][0])
            purities[t] = self._calculate_purity(rho)
            coherences[t] = self._calculate_coherence(rho)

            if np.isnan(variances[t]):
                rho = None
                break

        return variances, purities, coherences, rho

    def run_pure_wdw(self, N, coupling):
        """Run simulation for Pure WDW model."""
        T_op, H_matter = self._build_operators(N)
        H_total = H_matter + coupling * T_op
        return self._run_simulation(N, H_total)

    def run_wesh(self, N, coupling, nu_base):
        """Run simulation for WESH model (collective decoherence)."""
        T_op, H_matter = self._build_operators(N)
        H_total = H_matter + coupling * T_op
        nu_eff = nu_base / (N ** 2)
        L = np.sqrt(nu_eff) * T_op
        return self._run_simulation(N, H_total, L_ops=[L])

    def run_standard_decoherence(self, N, coupling, nu_base):
        """Run simulation for Standard Decoherence (local decoherence)."""
        T_op, H_matter = self._build_operators(N)
        H_total = H_matter + coupling * T_op

        lindblad_ops = []
        for i in range(N):
            ops = [self.si] * N
            ops[i] = self.sx
            L_i = np.sqrt(nu_base) * self._tensor_product(ops)
            lindblad_ops.append(L_i)

        return self._run_simulation(N, H_total, L_ops=lindblad_ops)

    def run_comparative_analysis(self, coupling, nu_base_wesh, nu_base_std, plot_results=True):
        """
        Run all simulation models and store results.

        Returns:
            dict: A dictionary of SimulationResult objects.
        """
        models_to_run = {
            "wesh": ("WESH (1/N² stability)", self.run_wesh, {"nu_base": nu_base_wesh}),
            "standard": ("Standard Decoherence (∝ N)", self.run_standard_decoherence, {"nu_base": nu_base_std}),
            "wdw": ("Pure WDW (Unstable)", self.run_pure_wdw, {})
        }

        results = {}
        for key, (name, func, params) in models_to_run.items():
            if self.verbose: print(f"\n--- Running {name} ---")
            final_vars, final_purs, final_cohs, times = [], [], [], []
            variances_vs_time, purities_vs_time, coherences_vs_time = {}, {}, {}

            for N in self.N_values:
                start = time.time()
                vars_time, purs_time, cohs_time, final_rho = func(N, coupling=coupling, **params)
                duration = time.time() - start

                final_vars.append(vars_time[-1])
                final_purs.append(purs_time[-1])
                final_cohs.append(cohs_time[-1])
                times.append(duration)
                variances_vs_time[N] = vars_time
                purities_vs_time[N] = purs_time
                coherences_vs_time[N] = cohs_time

                if self.verbose:
                    print(f"N={N}: Final Purity={final_purs[-1]:.4g}, Final Coherence={final_cohs[-1]:.4g}, Time={duration:.2f}s")

            results[key] = SimulationResult(
                name=name,
                N_values=np.array(self.N_values),
                final_variances=np.array(final_vars),
                final_purities=np.array(final_purs),
                final_coherences=np.array(final_cohs),
                computation_times=np.array(times),
                variances_vs_time=variances_vs_time,
                purities_vs_time=purities_vs_time,
                coherences_vs_time=coherences_vs_time
            )

        # Calculate scaling exponents
        for res in results.values():
            for metric in ['variances', 'purities', 'coherences']:
                data = getattr(res, f'final_{metric}')
                mask = ~np.isnan(data) & (data > 1e-12)
                if mask.sum() >= 2:
                    try:
                        exp = np.polyfit(np.log(res.N_values[mask]), np.log(data[mask]), 1)[0]
                        if metric == 'variances': res.scaling_exponent = exp
                        elif metric == 'purities': res.purity_scaling_exponent = exp
                        elif metric == 'coherences': res.coherence_scaling_exponent = exp
                    except np.linalg.LinAlgError:
                        pass

        if plot_results: self.plot_results(results)
        self.print_summary(results)
        return results

    def plot_results(self, results):
        """
        Plot key results: Purity, Coherence, Exponents, and Time.
        (Variance plots removed as requested).
        """
        fig, axes = plt.subplots(3, 2, figsize=(16, 18))
        fig.suptitle("WESH vs Standard Decoherence - Purity & Coherence Analysis", fontsize=16)
        colors = {'wesh': 'blue', 'standard': 'red', 'wdw': 'gray'}

        largest_N = max(self.N_values)
        t_axis = np.arange(self.time_steps) * self.dt

        # --- Row 1: Purity ---
        ax = axes[0, 0]
        for key, res in results.items():
            if largest_N in res.purities_vs_time:
                ax.plot(t_axis, res.purities_vs_time[largest_N], label=res.name, color=colors[key])
        ax.set_title(f"Purity Evolution (N={largest_N})"); ax.set_xlabel("Time"); ax.set_ylabel("Purity Tr(ρ²)"); ax.legend(); ax.grid(True, alpha=0.3)

        ax = axes[0, 1]
        for key, res in results.items():
            mask = ~np.isnan(res.final_purities) & (res.final_purities > 1e-12)
            label = f"{res.name} (α={res.purity_scaling_exponent:.2f})" if not np.isnan(res.purity_scaling_exponent) else res.name
            ax.loglog(res.N_values[mask], res.final_purities[mask], 'o-', label=label, color=colors[key])
        ax.set_title("Final Purity Scaling"); ax.set_xlabel("N"); ax.set_ylabel("Final Purity"); ax.legend(); ax.grid(True, which="both", alpha=0.3)

        # --- Row 2: Coherence ---
        ax = axes[1, 0]
        for key, res in results.items():
            if largest_N in res.coherences_vs_time:
                ax.plot(t_axis, res.coherences_vs_time[largest_N], label=res.name, color=colors[key])
        ax.set_title(f"Coherence Evolution (N={largest_N})"); ax.set_xlabel("Time"); ax.set_ylabel("Coherence"); ax.legend(); ax.grid(True, alpha=0.3)

        ax = axes[1, 1]
        for key, res in results.items():
            mask = ~np.isnan(res.final_coherences) & (res.final_coherences > 1e-12)
            label = f"{res.name} (α={res.coherence_scaling_exponent:.2f})" if not np.isnan(res.coherence_scaling_exponent) else res.name
            ax.loglog(res.N_values[mask], res.final_coherences[mask], 'o-', label=label, color=colors[key])
        ax.set_title("Final Coherence Scaling"); ax.set_xlabel("N"); ax.set_ylabel("Final Coherence"); ax.legend(); ax.grid(True, which="both", alpha=0.3)

        # --- Row 3: Exponents and Time ---
        ax = axes[2, 0]
        all_exponents = {
            'Purity': {res.name: res.purity_scaling_exponent for res in results.values()},
            'Coherence': {res.name: res.coherence_scaling_exponent for res in results.values()}
        }
        bar_width = 0.35
        labels = ["WESH", "Standard Decoherence"]
        r = np.arange(len(labels))

        pos1 = r - bar_width/2
        pos2 = r + bar_width/2

        values_purity = [
            all_exponents['Purity'].get("WESH (1/N² stability)", np.nan),
            all_exponents['Purity'].get("Standard Decoherence (∝ N)", np.nan)
        ]
        values_coherence = [
            all_exponents['Coherence'].get("WESH (1/N² stability)", np.nan),
            all_exponents['Coherence'].get("Standard Decoherence (∝ N)", np.nan)
        ]

        ax.bar(pos1, values_purity, width=bar_width, label='Purity')
        ax.bar(pos2, values_coherence, width=bar_width, label='Coherence')

        ax.set_xticks(r)
        ax.set_xticklabels(labels)
        ax.set_title("Fitted Scaling Exponents"); ax.set_ylabel("Exponent α"); ax.legend(); ax.grid(True, alpha=0.3)

        ax = axes[2, 1]
        for key, res in results.items():
            ax.semilogy(res.N_values, res.computation_times, 'o-', label=res.name, color=colors[key])
        ax.set_title("Computation Time"); ax.set_xlabel("N"); ax.set_ylabel("Time (s)"); ax.legend(); ax.grid(True, alpha=0.3)

        plt.tight_layout(rect=[0, 0, 1, 0.96])

        plot_file = os.path.join(self.output_dir, f"simulation_results_PurityCoherence_{self.timestamp}.png")
        plt.savefig(plot_file, dpi=300, bbox_inches='tight')
        print(f"\n Focused Purity/Coherence plot saved: {plot_file}")

        try:
            plt.show()
        except Exception as e:
            if self.verbose:
                print(f"[Plotting] Could not display plot: {e}")

    def print_summary(self, results):
        """Prints a rigorous numerical summary to the console."""
        print("\n" + "="*70)
        print("DETAILED NUMERICAL SUMMARY")
        print("="*70)

        header = f"{'Model':<30} | {'N':>3} | {'Final Var.':>15} | {'Final Purity':>15} | {'Final Coh.':>15}"
        print(header)
        print("-" * (len(header) + 2))

        for key, res in results.items():
            if "WDW" in res.name: continue
            for i, N in enumerate(res.N_values):
                var = res.final_variances[i]
                pur = res.final_purities[i]
                coh = res.final_coherences[i]
                print(f"{res.name:<30} | {N:>3} | {var:>15.4g} | {pur:>15.4g} | {coh:>15.4g}")
            print("-" * (len(header) + 2))

        print("\n" + "="*70)
        print("SCALING EXPONENT ANALYSIS (α)")
        print("="*70)
        for res in results.values():
            if "WDW" in res.name: continue
            print(f"\nModel: {res.name}")
            print(f"  Variance Exponent α = {res.scaling_exponent:.3f}")
            print(f"  Purity Exponent α   = {res.purity_scaling_exponent:.3f}")
            print(f"  Coherence Exponent α = {res.coherence_scaling_exponent:.3f}")
        print("\n" + "="*70)


# === MAIN EXECUTION BLOCK ===
if __name__ == '__main__':

    print("\n" + "="*70)
    print("WESH COLLECTIVE STABILITY ANALYSIS")
    print("="*70)

    # Initialize simulation
    wesh_test = WESHOptimizedTest(
        N_values=list(range(3, 10)),  # N=3 through N=9
        time_steps=2500,
        dt=0.01,
        verbose=True,
        memory_limit_gb=12            # Standard memory guardrail
    )

    # Run comparative analysis
    print("\n" + "="*70)
    print("RUNNING SIMULATIONS...")
    print("="*70)

    results = wesh_test.run_comparative_analysis(
        coupling=0.01,
        nu_base_wesh=100.0,
        nu_base_std=0.1,
        plot_results=True  # This will now generate the focused Purity/Coherence plot
    )

    print("\n" + "="*70)
    print("ANALYSIS COMPLETE")
    print("="*70)
    print(f"\n All results saved to folder: {wesh_test.output_dir}/")
    print("   - Numerical summary printed to console.")
    print(f"   - Main plot saved as: simulation_results_PurityCoherence_{wesh_test.timestamp}.png")

    print("\n" + "="*70)
