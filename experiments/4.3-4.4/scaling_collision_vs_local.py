#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
WESH Scaling — Pre‑Asymptotic Collision Model (agnostic, end‑to‑end)

Methodological note
-------------------
This script quantifies γ(N) and its scaling α using a *pre‑asymptotic
collision model* with Yukawa‑weighted system–environment micro‑collisions.
It does *not* implement the full causal‑kernel master equation nor the
explicit WESH‑Noether pre‑geometric constraint; it tests the *collective
stability prediction* via second‑order (quadratic‑in‑amplitude) effects.
An explicit first‑order local benchmark is included for comparison. 

Usage
-----
python wesh_scaling.py --mode both --nmin 2 --nmax 24 --beta 1 \
    --lambdaR 3.0 --norm l2 --dt 0.01 --t0 3.0 --boots 300
"""

from __future__ import annotations
import argparse, os, json, math, time, csv
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# --------------------------- Linear algebra ----------------------------------
SIGMA_Z = np.array([[1.0, 0.0],[0.0,-1.0]], dtype=complex)
SIGMA_X = np.array([[0.0, 1.0],[1.0, 0.0]], dtype=complex)
I2 = np.eye(2, dtype=complex)
GZX = np.kron(SIGMA_Z, SIGMA_X)  # generator for exp(-i θ σz⊗σx)

def partial_trace_env(rho_se: np.ndarray) -> np.ndarray:
    rho = rho_se.reshape(2,2,2,2)
    return rho[:, :, 0, 0] + rho[:, :, 1, 1]

def l1_coherence_qubit(rho: np.ndarray) -> float:
    return float(abs(rho[0,1]) + abs(rho[1,0]))

# ------------------------------ Fitting --------------------------------------
def fit_exponential_decay(t: np.ndarray, C: np.ndarray, tail: float=0.2) -> dict:
    """Fit C(t) ~ C0 exp(-γ t) on the late-time tail (ignore first 'tail' fraction)."""
    T = t[-1]
    mask = t >= (1.0 - tail) * T
    tt = t[mask]
    CC = np.array(C)[mask]
    eps = 1e-15
    y = np.log(np.clip(CC, eps, None))
    A = np.vstack([np.ones_like(tt), -tt]).T
    sol, _, _, _ = np.linalg.lstsq(A, y, rcond=None)
    lnC0, gamma = sol[0], sol[1]
    gamma = max(0.0, float(gamma))  # enforce γ ≥ 0
    yhat = A @ np.array([lnC0, gamma])
    ss_res = np.sum((y - yhat)**2); ss_tot = np.sum((y - np.mean(y))**2) + 1e-30
    R2 = 1.0 - ss_res/ss_tot
    return {"gamma": float(gamma), "C0": float(np.exp(lnC0)), "R2": float(R2)}

def fit_power_law(Ns, gammas):
    Ns = np.asarray(Ns, dtype=float); gs = np.asarray(gammas, dtype=float)
    mask = (Ns > 0) & (gs > 0)
    x = np.log(Ns[mask]); y = np.log(gs[mask])
    A = np.vstack([np.ones_like(x), x]).T
    sol, _, _, _ = np.linalg.lstsq(A, y, rcond=None)
    lnA, alpha = sol[0], sol[1]
    yhat = A @ sol
    ss_res = np.sum((y - yhat)**2); ss_tot = np.sum((y - np.mean(y))**2) + 1e-30
    R2 = 1.0 - ss_res/ss_tot
    return {"alpha": float(alpha), "A": float(np.exp(lnA)), "R2": float(R2)}

def bootstrap_alpha(Ns, gammas, B=300, seed=0):
    rng = np.random.default_rng(seed)
    Ns = np.asarray(Ns); gs = np.asarray(gammas)
    mask = (Ns > 0) & (gs > 0)
    Ns = Ns[mask]; gs = gs[mask]
    alphas = []
    for _ in range(B):
        idx = rng.integers(0, len(Ns), size=len(Ns))
        alphas.append(fit_power_law(Ns[idx], gs[idx])["alpha"])
    alphas = np.array(alphas)
    lo, hi = np.percentile(alphas, [16, 84])
    return {"alpha_lo": float(lo), "alpha_hi": float(hi), "alpha_med": float(np.median(alphas))}

# ------------------------- Geometry & Yukawa weights -------------------------
def yukawa_weights_1d(N: int, lambdaR: float, spacing: float=1.0, eps: float=1e-9,
                      norm: str="l2") -> np.ndarray:
    """
    Environment sites at r_i = i*spacing (i=1..N). Raw Yukawa weights:
       u_i = exp(-r_i/λ) / (r_i + eps).
    norm ∈ {"none","l1","l2"}.
    """
    i = np.arange(1, N+1, dtype=float)
    r = i * spacing
    u = np.exp(-r/lambdaR) / (r + eps)
    if norm == "none":
        w = u
    elif norm == "l1":
        s = np.sum(np.abs(u)) + eps; w = u / s
    else:  # l2
        s2 = np.sqrt(np.sum(u**2)) + eps; w = u / s2
    return w

# ------------------------------- Models --------------------------------------
def model_first_order_local(N:int, g0:float, beta:float, dt:float, tmax:float) -> dict:
    """Benchmark: off-diagonals decay linearly in g per dt → γ ∝ g(N)."""
    gN = g0 / (N**beta)
    psi_plus = (1/np.sqrt(2.0)) * np.array([1.0, 1.0], dtype=complex)
    rho = np.outer(psi_plus, psi_plus.conj())
    t_vals = [0.0]; C_vals = [l1_coherence_qubit(rho)]
    steps = int(np.round(tmax/dt))
    for _ in range(steps):
        rho[0,1] *= (1.0 - gN * dt); rho[1,0] = rho[0,1].conj()
        t_vals.append(t_vals[-1] + dt); C_vals.append(l1_coherence_qubit(rho))
    fit = fit_exponential_decay(np.array(t_vals), np.array(C_vals), tail=0.5)
    return {"t": t_vals, "C": C_vals, "fit": fit, "gN": gN}

def model_collision_preasym(N:int, kappa:float, beta:float, lambdaR:float,
                            norm:str, dt:float, tmax:float, spacing:float=1.0,
                            noether_check: bool=False) -> dict:
    """
    Pre‑asymptotic collision model: sequential S–E collisions with Yukawa weights.
    Each dt: collide S with all N ancillae using angles θ_i = √(κ dt) * A_N * w_i,
    A_N = N^{-β}. Tracing out ancillae yields dephasing ∝ A_N^2 Σ_i w_i^2.
    """
    w = yukawa_weights_1d(N, lambdaR=lambdaR, spacing=spacing, norm=norm)
    A_N = N**(-beta)
    # Initial |+> state for S
    psi_plus = (1/np.sqrt(2.0)) * np.array([1.0, 1.0], dtype=complex)
    rho_S = np.outer(psi_plus, psi_plus.conj())
    # Default ancilla |0>
    rho_E0 = np.array([[1.0, 0.0],[0.0, 0.0]], dtype=complex)

    noether = None
    if noether_check:
        # Single-collision diagnostic with ancilla |+x> to probe ⟨G⟩ invariance in closed S⊗E
        ket_plusx = (1/np.sqrt(2.0)) * np.array([[1.0],[1.0]], dtype=complex)
        rho_E_plusx = ket_plusx @ ket_plusx.conj().T
        theta_chk = math.sqrt(max(kappa, 0.0) * dt) * A_N * (w[0] if len(w)>0 else 1.0)
        c, s = math.cos(theta_chk), math.sin(theta_chk)
        U = c * np.kron(I2, I2) - 1j * s * GZX
        rho_SE = np.kron(rho_S, rho_E_plusx)
        G = GZX
        expG_before = float(np.real(np.trace(G @ rho_SE)))
        rho_SE_after = U @ rho_SE @ U.conj().T
        expG_after  = float(np.real(np.trace(G @ rho_SE_after)))
        noether = {"theta_check": float(theta_chk), "expG_before": expG_before, "expG_after": expG_after}

    t_vals = [0.0]; C_vals = [l1_coherence_qubit(rho_S)]
    steps = int(np.round(tmax/dt))
    for _ in range(steps):
        for wi in w:
            theta = math.sqrt(max(kappa, 0.0) * dt) * A_N * wi
            c, s = math.cos(theta), math.sin(theta)
            U = c * np.kron(I2, I2) - 1j * s * GZX
            rho_SE = np.kron(rho_S, rho_E0)
            rho_SE = U @ rho_SE @ U.conj().T
            rho_S = partial_trace_env(rho_SE)
        t_vals.append(t_vals[-1] + dt); C_vals.append(l1_coherence_qubit(rho_S))

    fit = fit_exponential_decay(np.array(t_vals), np.array(C_vals), tail=0.5)
    return {"t": t_vals, "C": C_vals, "fit": fit, "noether": noether}

# ----------------------------- Experiment core -------------------------------
def estimate_gamma_vs_N(mode:str, N_list, params:dict, prog:bool=True):
    gammas, r2s, series = [], [], {}
    for N in N_list:
        if prog: print(f"N={N}...", flush=True)
        if mode == "local":
            r = model_first_order_local(N=N, g0=params["g0"], beta=params["beta"],
                                        dt=params["dt"], tmax=params["tmax"](N))
        else:
            r = model_collision_preasym(N=N, kappa=params["kappa"], beta=params["beta"],
                                        lambdaR=params["lambdaR"], norm=params["norm"],
                                        dt=params["dt"], tmax=params["tmax"](N),
                                        noether_check=params.get("noether_check", False))
        gammas.append(r["fit"]["gamma"]); r2s.append(r["fit"]["R2"]); series[N]=r
    return np.array(gammas), np.array(r2s), series

def default_tmax_factory(model:str, kappa:float, beta:float):
    """Choose tmax(N) scale to observe O(1) decay across N without biasing α."""
    c = 6.0
    return (lambda N: c * (N**beta)) if model=="local" else (lambda N: c * (N**(2*beta)) / max(kappa,1e-9))

# ---------------------------------- Main -------------------------------------
def main():
    ap = argparse.ArgumentParser(description="QFTT–WESH scaling (pre‑asymptotic collision model)")
    ap.add_argument("--mode", choices=["local","collision","ham","both"], default="both",
                    help="Select 'local' (first‑order), 'collision' (pre‑asymptotic), or 'both'")
    ap.add_argument("--nmin", type=int, default=2)
    ap.add_argument("--nmax", type=int, default=16)
    ap.add_argument("--lambdaR", type=float, default=3.0, help="Yukawa screening length λ")
    ap.add_argument("--beta", type=float, default=1.0, help="Amplitude exponent A_N=1/N^β")
    ap.add_argument("--norm", choices=["none","l1","l2"], default="l2", help="Weight normalization")
    ap.add_argument("--g0", type=float, default=0.3, help="Local model base coupling")
    ap.add_argument("--kappa", type=float, default=0.3, help="Second‑order strength (collision model)")
    ap.add_argument("--dt", type=float, default=0.02)
    ap.add_argument("--t0", type=float, default=6.0, help="Time scale factor multiplying default tmax(N)")
    ap.add_argument("--boots", type=int, default=300, help="Bootstrap resamples for α CI")
    ap.add_argument("--seed", type=int, default=3536062330)
    ap.add_argument("--out", type=str, default=None)
    ap.add_argument("--noether-check", action="store_true", help="Single micro‑collision invariance diagnostic (closed S⊗E)")
    args = ap.parse_args()

    np.random.seed(args.seed)
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    outdir = args.out or f"./wesh_scaling_out_{timestamp}"
    os.makedirs(outdir, exist_ok=True)

    # Build N list and tmax functions (agnostic, scale-aware)
    N_list = list(range(args.nmin, args.nmax+1))
    tmax_local = (lambda f: (lambda N: args.t0 * f(N)))(default_tmax_factory("local", kappa=args.kappa, beta=args.beta))
    tmax_coll  = (lambda f: (lambda N: args.t0 * f(N)))(default_tmax_factory("ham",   kappa=args.kappa, beta=args.beta))

    results = {}

    # Local (first-order) branch
    if args.mode in ("local","both"):
        params_local = dict(g0=args.g0, beta=args.beta, dt=args.dt, tmax=tmax_local)
        g_local, r2_local, series_local = estimate_gamma_vs_N("local", N_list, params_local)
        fit_local = fit_power_law(N_list, g_local)
        ci_local  = bootstrap_alpha(N_list, g_local, B=args.boots, seed=args.seed)
        results["local"] = dict(N=N_list, gamma=g_local.tolist(), R2=r2_local.tolist(),
                                alpha=fit_local["alpha"], A=fit_local["A"], R2fit=fit_local["R2"],
                                alpha_CI=[ci_local["alpha_lo"], ci_local["alpha_hi"]])
        # CSV
        with open(os.path.join(outdir, "gamma_local.csv"), "w", newline="") as f:
            w = csv.writer(f); w.writerow(["N","gamma","R2"])
            [w.writerow([N,g,r]) for N,g,r in zip(N_list, g_local, r2_local)]
        # Plot
        plt.figure(figsize=(6,4), dpi=160)
        mask = g_local>0; x = np.array(N_list)[mask]; y = g_local[mask]
        xx = np.linspace(x.min(), x.max(), 200)
        yy = fit_local["A"] * xx**fit_local["alpha"]
        plt.loglog(x, y, "o", label="data")
        plt.loglog(xx, yy, "--", label=f"fit α={fit_local['alpha']:.3f}  [{ci_local['alpha_lo']:.3f},{ci_local['alpha_hi']:.3f}]")
        plt.xlabel("N"); plt.ylabel("γ(N)"); plt.title(f"Local first‑order (β={args.beta})")
        plt.legend(); plt.tight_layout(); plt.savefig(os.path.join(outdir, "gamma_local.png")); plt.close()

    # Pre‑asymptotic collision (second‑order) branch
    if args.mode in ("collision","ham","both"):
        params_coll = dict(kappa=args.kappa, beta=args.beta, lambdaR=args.lambdaR,
                           norm=args.norm, dt=args.dt, tmax=tmax_coll,
                           noether_check=args.noether_check)
        g_coll, r2_coll, series_coll = estimate_gamma_vs_N("collision", N_list, params_coll)
        fit_coll = fit_power_law(N_list, g_coll)
        ci_coll  = bootstrap_alpha(N_list, g_coll, B=args.boots, seed=args.seed+1)
        results["collision"] = dict(N=N_list, gamma=g_coll.tolist(), R2=r2_coll.tolist(),
                                    alpha=fit_coll["alpha"], A=fit_coll["A"], R2fit=fit_coll["R2"],
                                    alpha_CI=[ci_coll["alpha_lo"], ci_coll["alpha_hi"]],
                                    lambdaR=args.lambdaR, norm=args.norm, beta=args.beta)
        # CSV
        with open(os.path.join(outdir, "gamma_collision.csv"), "w", newline="") as f:
            w = csv.writer(f); w.writerow(["N","gamma","R2"])
            [w.writerow([N,g,r]) for N,g,r in zip(N_list, g_coll, r2_coll)]
        # Plot γ(N)
        plt.figure(figsize=(6,4), dpi=160)
        mask = g_coll>0; x = np.array(N_list)[mask]; y = g_coll[mask]
        xx = np.linspace(x.min(), x.max(), 200)
        yy = fit_coll["A"] * xx**fit_coll["alpha"]
        plt.loglog(x, y, "o", label="data")
        plt.loglog(xx, yy, "--", label=f"fit α={fit_coll['alpha']:.3f}  [{ci_coll['alpha_lo']:.3f},{ci_coll['alpha_hi']:.3f}]")
        plt.xlabel("N"); plt.ylabel("γ(N)"); plt.title(f"Pre‑asymptotic collision (β={args.beta}, norm={args.norm})")
        plt.legend(); plt.tight_layout(); plt.savefig(os.path.join(outdir, "gamma_collision.png")); plt.close()

        # Time series for sample Ns
        Ns_show = [args.nmin, (args.nmin+args.nmax)//2, args.nmax]
        plt.figure(figsize=(6,4), dpi=160)
        for N in Ns_show:
            r = series_coll[N]; t = np.array(r["t"]); C = np.array(r["C"])
            plt.semilogy(t, C, label=f"N={N}")
        plt.xlabel("t"); plt.ylabel("C(t)"); plt.title("Pre‑asymptotic collision: coherence vs time")
        plt.legend(); plt.tight_layout(); plt.savefig(os.path.join(outdir, "timeseries_collision.png")); plt.close()

        # Noether‑style diagnostic (optional)
        noether_log = None
        for N in Ns_show:
            if series_coll[N]["noether"] is not None:
                noether_log = series_coll[N]["noether"]; break
        if noether_log is not None:
            results["noether_check"] = noether_log

    # Save JSON summary
    with open(os.path.join(outdir, "summary.json"), "w") as f:
        json.dump(results, f, indent=2)

    # Console summary (agnostic, comparative)
    print("Output directory:", outdir)
    if "local" in results:
        aL = results['local']['alpha']; loL, hiL = results['local']['alpha_CI']
        print(f"[LOCAL]     α={aL:.3f}  CI{(loL,hiL)}  R²={results['local']['R2fit']:.3f}")
    if "collision" in results:
        aC = results['collision']['alpha']; loC, hiC = results['collision']['alpha_CI']
        print(f"[COLLISION] α={aC:.3f}  CI{(loC,hiC)}  R²={results['collision']['R2fit']:.3f}")
        # Comparative deviations (neutral reporting)
        comps = [(-2.0, "α=-2 (quadratic)"), (-1.0, "α=-1 (linear)"), (0.0, "α=0 (constant)")]
        for ref, label in comps:
            dev = abs(aC - ref)
            # Use half‑width of CI as rough σ if available
            sigma = max(1e-12, 0.5*(hiC - loC))
            z = dev/sigma if sigma>0 else float("inf")
            print(f"  deviation from {label}: Δ={dev:.3f}  ~{z:.2f}σ")

if __name__ == "__main__":
    main()
