# ===========================
# WESH — Experiment 7+ (Extended)
# Angular modulation (more points) + N-scaling + W-state control
# Two independent runs per batch to estimate uncertainties
# Backend access: QiskitRuntimeService + SamplerV2(mode=backend) [NO session]
# ===========================

import numpy as np, pandas as pd, matplotlib.pyplot as plt
from datetime import datetime
from scipy.optimize import curve_fit
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2 as Sampler
import warnings; warnings.filterwarnings("ignore")

stamp = datetime.now().strftime("%Y%m%d_%H%M%S")

# ---------------- User knobs ----------------
THETAS_DEG = [21, 27, 30, 33, 36, 39, 42, 45]  # angular sweep
N_LIST_ANG  = [3, 4]                            # angular experiment (two batches)
N_LIST_SCAL = [3, 4, 5, 6]                      # scaling at theta=30°
NCPMG_ANG   = [3, 5, 7]                         # echo orders for angular
NCPMG_SCAL  = [5]
SHOTS       = 2048
RUNS_PER_BATCH = 2                              # two independent runs
OPT_LEVEL   = 1

# ---------------- Helpers ----------------
def us_to_dt(us, dt):
    return max(1, int(round((us*1e-6)/dt)))

def build_cpmg(qc, N, n, seg_dt):
    # Hahn echo generalized (CPMG-like): [delay, X]^n [delay]
    for _ in range(n):
        for q in range(N): qc.delay(seg_dt, q, unit='dt')
        for q in range(N): qc.x(q)
        for q in range(N): qc.delay(seg_dt, q, unit='dt')

def prep_GHZ(qc, N, theta):  # |GHZ(θ)>=cosθ|0..0> + sinθ|1..1>
    qc.ry(2*theta, 0)
    for j in range(1, N): qc.cx(0, j)

def prep_PRODUCT(qc, N, theta):  # ⊗ Ry(2θ)|0>
    for j in range(N): qc.ry(2*theta, j)

def prep_W(qc, N):
    """
    Lightweight ladder construction of |W_N> (single-excitation uniform superposition)
    Ref: iterative Ry + CX chain (amplitude-splitting). Keeps 2-qubit depth modest.
    """
    # angles chosen so that after each CX the single excitation is split uniformly
    for k in range(N-1):
        theta = 2*np.arccos(np.sqrt((N-1-k)/(N-k)))
        qc.ry(theta, k)
        qc.cx(k, k+1)

def build_circuit(N, state, theta, T_us, n, dt):
    qc = QuantumCircuit(N, N)
    if state == "GHZ":
        prep_GHZ(qc, N, theta)
    elif state == "PRODUCT":
        prep_PRODUCT(qc, N, theta)
    elif state == "W":
        prep_W(qc, N)
    else:
        raise ValueError("state must be GHZ/PRODUCT/W")

    seg_us = T_us / (2.0*n)
    seg_dt = us_to_dt(seg_us, dt)
    build_cpmg(qc, N, n, seg_dt)

    for q in range(N): qc.h(q)
    qc.measure(range(N), range(N))
    return qc

def extract_parity(pubresult):
    """
    SamplerV2 result → |<X>| parity = sum_b (-1)^{#1(b)} p(b), absolute value
    This accessor is robust across runtime versions by scanning for get_counts()
    """
    try:
        data = getattr(pubresult, 'data', None)
        if data is None: return np.nan
        counts = None
        for attr in dir(data):
            if attr.startswith('_'): continue
            obj = getattr(data, attr)
            if hasattr(obj, 'get_counts'):
                counts = obj.get_counts()
                break
        if counts is None or len(counts)==0: return np.nan
        tot = sum(counts.values())
        acc = 0
        for b, c in counts.items():
            ones = b.count('1') if isinstance(b, str) else bin(b).count('1')
            acc += ((-1)**ones) * c
        return abs(acc/tot)
    except Exception:
        return np.nan

def cos2_model(theta, b0, b1):
    return b0 + b1*np.cos(theta)**2

# ---------------- Connect backend (NO session) ----------------
print("Connecting to IBM Quantum Runtime...")
service = QiskitRuntimeService()  # assumes you already saved your account
cands = []
for name in ["ibm_brisbane", "ibm_torino", "ibm_fez", "ibm_osaka"]:
    try:
        bk = service.backend(name)
        if bk.status().operational:
            cands.append(bk)
            print(f"  {name}: pending={bk.status().pending_jobs}")
    except: pass
if not cands: raise RuntimeError("No operational backend found.")
backend = min(cands, key=lambda b: b.status().pending_jobs)
dt = backend.configuration().dt
print(f"Using backend: {backend.name}, dt={dt*1e9:.3f} ns")

# ---------------- Build experiment definitions ----------------
def circuits_for_angular(N, thetas_deg, nlist, states=("GHZ","PRODUCT","W"), T_us=3.0):
    circs, meta = [], []
    for th in thetas_deg:
        theta = np.deg2rad(th)
        for n in nlist:
            for st in states:
                qc = build_circuit(N, st, theta, T_us, n, dt)
                qc.name = f"{st}_N{N}_th{th}_n{n}"
                circs.append(qc)
                meta.append(dict(kind="angular", N=N, theta_deg=th, theta=theta, n=n, state=st))
    return circs, meta

def circuits_for_scaling(N_list, theta_deg=30.0, n=5, states=("GHZ","PRODUCT"), T_us=3.0, include_W=False):
    circs, meta = [], []
    theta = np.deg2rad(theta_deg)
    for N in N_list:
        for st in states:
            qc = build_circuit(N, st, theta, T_us, n, dt)
            qc.name = f"{st}_N{N}_th{theta_deg}_n{n}"
            circs.append(qc)
            meta.append(dict(kind="scaling", N=N, theta_deg=theta_deg, theta=theta, n=n, state=st))
        if include_W:
            qc = build_circuit(N, "W", theta, T_us, n, dt)
            qc.name = f"W_N{N}_th{theta_deg}_n{n}"
            circs.append(qc)
            meta.append(dict(kind="scaling", N=N, theta_deg=theta_deg, theta=theta, n=n, state="W"))
    return circs, meta

def run_sampler_batches(circs, meta, n_runs=2, shots=2048):
    # transpile once per run (keeps randomization by layout variations)
    all_runs = []
    for r in range(n_runs):
        print(f"  Run {r+1}/{n_runs} … (transpile+execute)")
        tcircs = transpile(circs, backend=backend, optimization_level=OPT_LEVEL, scheduling_method="alap")
        sampler = Sampler(mode=backend)
        job = sampler.run(tcircs, shots=shots)
        print(f"    Job ID: {job.job_id()}  … awaiting result")
        res = job.result()
        parities = [extract_parity(res[i]) for i in range(len(tcircs))]
        df = pd.DataFrame(meta).copy()
        df["parity_abs"] = parities
        df["run_idx"] = r
        all_runs.append(df)
    out = pd.concat(all_runs, ignore_index=True)
    return out

def summarize_runs(df):
    grp = df.groupby(list(set(df.columns)-{"parity_abs","run_idx"}), dropna=False)["parity_abs"]
    dfm = grp.agg(['mean','std','count']).reset_index()
    dfm.rename(columns={'mean':'parity_mean','std':'parity_std','count':'n_runs'}, inplace=True)
    dfm["parity_sem"] = dfm["parity_std"]/np.sqrt(dfm["n_runs"].clip(lower=1))
    return dfm

# ---------------- ANGULAR: N=3 and N=4 (two batches, 2 runs each) ----------------
ANG_results = []
for N in N_LIST_ANG:
    print(f"\n=== Angular batch, N={N} ===")
    circs, meta = circuits_for_angular(N, THETAS_DEG, NCPMG_ANG, states=("GHZ","PRODUCT","W"), T_us=3.0)
    df_runs = run_sampler_batches(circs, meta, n_runs=RUNS_PER_BATCH, shots=SHOTS)
    ANG_results.append(df_runs)

df_ang_all = pd.concat(ANG_results, ignore_index=True)
df_ang = summarize_runs(df_ang_all)

csv_ang = f"wesh7plus_angular_{stamp}.csv"
df_ang.to_csv(csv_ang, index=False)
print(f"\nSaved: {csv_ang}  (rows={len(df_ang)})")

# ---------------- SCALING: θ=30°, N={3,4,5,6}, states GHZ/PRODUCT (+W optional) ----------------
print(f"\n=== Scaling batch, N={N_LIST_SCAL}, θ=30°, n=5 ===")
circs_s, meta_s = circuits_for_scaling(N_LIST_SCAL, theta_deg=30.0, n=5, states=("GHZ","PRODUCT"), T_us=3.0, include_W=True)
df_scal_runs = run_sampler_batches(circs_s, meta_s, n_runs=RUNS_PER_BATCH, shots=SHOTS)
df_scal = summarize_runs(df_scal_runs)

csv_scal = f"wesh7plus_scaling_{stamp}.csv"
df_scal.to_csv(csv_scal, index=False)
print(f"Saved: {csv_scal}  (rows={len(df_scal)})")

# ---------------- ANALYSIS & PLOTS ----------------
def make_delta_by_theta(df, N, state_pair=("GHZ","PRODUCT")):
    sub = df[(df.kind=="angular") & (df.N==N)]
    ths = sorted(sub.theta_deg.unique())
    rows=[]
    for th in ths:
        for n in sorted(sub.n.unique()):
            a = sub[(sub.theta_deg==th)&(sub.n==n)]
            a1 = a[a.state==state_pair[0]]
            a2 = a[a.state==state_pair[1]]
            if len(a1)==1 and len(a2)==1:
                d  = a1.parity_mean.values[0] - a2.parity_mean.values[0]
                se = np.hypot(a1.parity_sem.values[0], a2.parity_sem.values[0])
                rows.append(dict(theta_deg=th, n=n, delta=d, delta_sem=se))
    return pd.DataFrame(rows)

# 1) Angular: Δ(θ) = |X|_GHZ - |X|_PRODUCT  (N=3) with cos²θ fit
dN3 = make_delta_by_theta(df_ang, 3)
# average over n (pooled SEM)
dN3g = dN3.groupby("theta_deg").apply(
    lambda g: pd.Series(dict(delta=np.average(g.delta, weights=1/np.maximum(g.delta_sem,1e-6)**2),
                             delta_sem=np.sqrt(1/np.sum(1/np.maximum(g.delta_sem,1e-6)**2)))))
dN3g = dN3g.reset_index()
theta_rad = np.deg2rad(dN3g.theta_deg.values)
popt, pcov = curve_fit(lambda t, b0,b1: cos2_model(t,b0,b1), theta_rad, dN3g.delta.values, sigma=np.maximum(dN3g.delta_sem.values,1e-6), absolute_sigma=True, maxfev=10000)
b0,b1 = popt; r2 = 1 - np.sum((dN3g.delta - cos2_model(theta_rad, *popt))**2)/np.sum((dN3g.delta - np.mean(dN3g.delta))**2)

# 2) Scaling: Δ(N) at θ=30°, n=5
def delta_scaling(df_scal, theta_deg=30.0):
    out=[]
    for N in sorted(df_scal.N.unique()):
        g = df_scal[(df_scal.kind=="scaling")&(df_scal.N==N)&(df_scal.theta_deg==theta_deg)]
        g1 = g[g.state=="GHZ"]; g2 = g[g.state=="PRODUCT"]
        if len(g1)==1 and len(g2)==1:
            d  = g1.parity_mean.values[0] - g2.parity_mean.values[0]
            se = np.hypot(g1.parity_sem.values[0], g2.parity_sem.values[0])
            out.append((N,d,se))
    return np.array(out)

Dsc = delta_scaling(df_scal, theta_deg=30.0)

# 3) W-control: compare W vs PRODUCT across angles (N=3,4)
def w_delta_by_theta(df, N):
    sub = df[(df.kind=="angular") & (df.N==N)]
    rows=[]
    for th in sorted(sub.theta_deg.unique()):
        for n in sorted(sub.n.unique()):
            a = sub[(sub.theta_deg==th)&(sub.n==n)]
            w = a[a.state=="W"]; p = a[a.state=="PRODUCT"]
            if len(w)==1 and len(p)==1:
                d  = w.parity_mean.values[0] - p.parity_mean.values[0]
                se = np.hypot(w.parity_sem.values[0], p.parity_sem.values[0])
                rows.append((th, n, d, se))
    dfw = pd.DataFrame(rows, columns=["theta_deg","n","delta_WminusP","sem"])
    # average over n
    agg = dfw.groupby("theta_deg").apply(lambda g: pd.Series(dict(delta=np.average(g.delta_WminusP, weights=1/np.maximum(g.sem,1e-6)**2),
                                                                 sem=np.sqrt(1/np.sum(1/np.maximum(g.sem,1e-6)**2)))))
    return agg.reset_index()

dW3 = w_delta_by_theta(df_ang, 3)
dW4 = w_delta_by_theta(df_ang, 4)

# ---------------- PLOTS ----------------
plt.figure(figsize=(12,4.2))
# (a) Angular fit
ax1 = plt.subplot(1,3,1)
ax1.errorbar(dN3g.theta_deg, dN3g.delta, yerr=dN3g.delta_sem, fmt='o', capsize=3, label='N=3 data')
thf = np.linspace(min(THETAS_DEG), max(THETAS_DEG), 200)
ax1.plot(thf, cos2_model(np.deg2rad(thf), *popt), 'r-', label=f'Fit cos²θ (R²={r2:.3f})')
ax1.set_xlabel('θ (deg)'); ax1.set_ylabel('Δ Parity (GHZ − PRODUCT)'); ax1.set_title('Angular Modulation')
ax1.grid(alpha=0.3); ax1.legend()

# (b) Scaling
ax2 = plt.subplot(1,3,2)
if len(Dsc)>0:
    ax2.errorbar(Dsc[:,0], Dsc[:,1], yerr=Dsc[:,2], fmt='s--', capsize=3, label='Δ(N) at θ=30°')
    ax2.set_xticks([3,4,5,6])
ax2.set_xlabel('N'); ax2.set_ylabel('Δ Parity'); ax2.set_title('Mini-scaling (GHZ−PRODUCT)')
ax2.grid(alpha=0.3); ax2.legend()

# (c) W control (angle-averaged over n)
ax3 = plt.subplot(1,3,3)
ax3.errorbar(dW3.theta_deg, dW3.delta, yerr=dW3.sem, fmt='o', capsize=3, label='N=3: W−PRODUCT')
ax3.errorbar(dW4.theta_deg, dW4.delta, yerr=dW4.sem, fmt='s', capsize=3, label='N=4: W−PRODUCT')
ax3.axhline(0, color='k', lw=0.8)
ax3.set_xlabel('θ (deg)'); ax3.set_ylabel('Parity (W − PRODUCT)'); ax3.set_title('W-state control')
ax3.grid(alpha=0.3); ax3.legend()

plt.tight_layout()
png_name = f"wesh7plus_plots_{stamp}.png"
plt.savefig(png_name, dpi=150); plt.show()
print(f"Saved figure: {png_name}")

# ---------------- Print quick stats ----------------
print("\n=== Quick stats ===")
print(f"Angular fit (N=3): Δ(θ)=β0+β1 cos²θ → β0={b0:.4f}, β1={b1:.4f}, R²={r2:.3f}")
if len(Dsc)>0:
    for N, d, se in Dsc:
        print(f"Δ(N={int(N)} @ θ=30°) = {d:+.3f} ± {se:.3f} (SEM)")

print("\nFiles saved:")
print(f"  {csv_ang}")
print(f"  {csv_scal}")
print(f"  {png_name}")
