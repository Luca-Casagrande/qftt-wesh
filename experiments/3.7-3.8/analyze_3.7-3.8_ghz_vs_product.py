# ==== IBM Q FTNS • GHZ vs PRODUCT (Open Plan) ====
# Compatibile con Qiskit Runtime Open Plan - testato e funzionante
# Estrazione risultati ROBUSTA con multiple vie di fallback

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import warnings
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2 as Sampler, Options

warnings.filterwarnings("ignore")

# -------------------------- CONFIG --------------------------
NQ           = 3                    # n. qubit (GHZ-3 vs prodotto-3)
THETAS       = [np.pi/6, np.pi/4]   # 30°, 45°
T_LIST_US    = [2.5, 3.5, 4.5]      # μs
N_LIST       = [1,2,3,4,5,6,8,10]
SHOTS        = 2048
OPT_LEVEL    = 1
BATCH_SIZE   = 18                   # batch piccoli = più robusti
CSV_NAME     = "state_dep_alpha_dataset.csv"

# ---------------------- UTILS: circuits ---------------------
def us_to_dt(us, dt):
    """Converti microsecondi in unità dt del backend."""
    return max(1, int(round((us * 1e-6) / dt)))

def prep_GHZ(qc, N, theta):
    """Prepara stato GHZ(θ): cos(θ)|000> + sin(θ)|111>"""
    qc.ry(2*theta, 0)
    for j in range(1, N):
        qc.cx(0, j)

def prep_PRODUCT(qc, N, theta):
    """Prepara stato prodotto con stessa popolazione."""
    for j in range(N):
        qc.ry(2*theta, j)

def cpmg_parity_circ(N, theta, state, T_us, n, dt):
    """Costruisce circuito completo: prep -> CPMG -> misura parità."""
    qc = QuantumCircuit(N, N)
    
    # Preparazione stato
    if state == "GHZ":
        prep_GHZ(qc, N, theta)
    else:
        prep_PRODUCT(qc, N, theta)
    
    # Sequenza CPMG
    seg_us = T_us / (2.0 * n)
    dseg = us_to_dt(seg_us, dt)
    
    for _ in range(n):
        for q in range(N):
            qc.delay(dseg, q, unit='dt')
        for q in range(N):
            qc.x(q)
        for q in range(N):
            qc.delay(dseg, q, unit='dt')
    
    # Misura parità in base X
    for q in range(N):
        qc.h(q)
    qc.measure(range(N), range(N))
    
    qc.name = f"{state}_N{N}_th{theta:.3f}_T{T_us:.2f}_n{n}"
    return qc

# ------------------- UTILS: parity extraction ----------------
def parity_from_counts(counts, n_qubits):
    """Calcola parità da dizionario counts."""
    tot = sum(counts.values())
    if tot == 0:
        return None
    
    s = 0
    for bitstr, cnt in counts.items():
        # Gestisci sia string che int
        if isinstance(bitstr, int):
            bitstr = format(bitstr, f"0{n_qubits}b")
        ones = bitstr.count("1")
        s += cnt * ((-1)**ones)
    
    return abs(s/tot)

def parity_from_array(arr):
    """Calcola parità da array di bit."""
    if arr is None:
        return None
    
    if hasattr(arr, "to_numpy"):
        arr = arr.to_numpy()
    
    a = np.asarray(arr)
    if a.ndim != 2:
        return None
    
    ones = a.sum(axis=1)
    return float(np.abs(np.mean((-1)**ones)))

def extract_parity_pub(pub, n_qubits, shots, verbose=False):
    """
    Estrazione robusta per SamplerV2 - prova multiple vie.
    Restituisce (parity, path_string).
    """
    # Via 1: pub.data.* con get_counts()
    if hasattr(pub, "data"):
        dobj = pub.data
        
        # Scansiona tutti gli attributi pubblici
        for name in [a for a in dir(dobj) if not a.startswith("_")]:
            node = getattr(dobj, name)
            
            # Prova get_counts()
            if hasattr(node, "get_counts"):
                try:
                    cnt = node.get_counts()
                    p = parity_from_counts(cnt, n_qubits)
                    if p is not None:
                        if verbose:
                            print(f"    ✓ Estratto via .data.{name}.get_counts()")
                        return p, f".data.{name}.get_counts()"
                except:
                    pass
            
            # Prova get_int_counts()
            if hasattr(node, "get_int_counts"):
                try:
                    icnt = node.get_int_counts()
                    cnt = {format(k, f"0{n_qubits}b"): v for k, v in icnt.items()}
                    p = parity_from_counts(cnt, n_qubits)
                    if p is not None:
                        if verbose:
                            print(f"    ✓ Estratto via .data.{name}.get_int_counts()")
                        return p, f".data.{name}.get_int_counts()"
                except:
                    pass
            
            # Prova array di bit
            if hasattr(node, "array"):
                try:
                    arr = node.array
                    p = parity_from_array(arr)
                    if p is not None:
                        if verbose:
                            print(f"    ✓ Estratto via .data.{name}.array")
                        return p, f".data.{name}.array"
                except:
                    pass
    
    # Via 2: Vecchio stile quasi_dists (se presente)
    for attr in ("quasi_dist", "quasi_dist_bin", "quasi_dists"):
        if hasattr(pub, attr):
            q = getattr(pub, attr)
            try:
                q0 = q if isinstance(q, dict) else (q[0] if len(q) > 0 else None)
                if q0:
                    counts = {k: int(round(v * shots)) for k, v in q0.items()}
                    p = parity_from_counts(counts, n_qubits)
                    if p is not None:
                        return p, f".{attr}"
            except:
                pass
    
    # Fallback
    return None, "(fallback)"

# ----------------------- BACKEND & dt -----------------------
print("Connettendo a IBM Quantum...")
service = QiskitRuntimeService()

# Trova backend operativi
cands = []
for b in service.backends():
    try:
        if (b.status().operational and 
            not b.configuration().simulator and 
            getattr(b.configuration(), 'dt', None)):
            cands.append(b)
            print(f"  {b.name}: operational, pending={b.status().pending_jobs}")
    except Exception as e:
        pass

if not cands:
    raise RuntimeError("Nessun backend hardware operativo con dt disponibile.")

# Scegli il meno in coda
backend = min(cands, key=lambda b: getattr(b.status(), "pending_jobs", 999999))
cfg = backend.configuration()
dt = float(getattr(cfg, "dt", 5e-10))  # fallback 0.5 ns

print(f"\nBackend selezionato: {backend.name}")
print(f"  pending_jobs={backend.status().pending_jobs}")
print(f"  dt={dt*1e9:.3f} ns")

# ------------------ COSTRUZIONE CIRCUITI --------------------
circs, meta = [], []

for th in THETAS:
    for T in T_LIST_US:
        for n in N_LIST:
            # Evita delay < 1 dt
            if us_to_dt(T/(2*n), dt) < 1:
                print(f"  Skip: T={T}μs, n={n} (delay < 1 dt)")
                continue
            
            for state in ("GHZ", "PRODUCT"):
                q = cpmg_parity_circ(NQ, th, state, T, n, dt)
                circs.append(q)
                meta.append({
                    "state": state,
                    "theta": th,
                    "T_us": T,
                    "n": n
                })

print(f"\nTotale circuiti generati: {len(circs)}")

if not circs:
    raise RuntimeError("Nessun circuito valido: dt troppo grande per i delay richiesti.")

# --------------------- ESECUZIONE A BATCH -------------------
rows = []
paths_used = []
nb = (len(circs) + BATCH_SIZE - 1) // BATCH_SIZE

print(f"\nEsecuzione in {nb} batch di max {BATCH_SIZE} circuiti\n")

for bi in range(nb):
    i0 = bi * BATCH_SIZE
    i1 = min(len(circs), (bi + 1) * BATCH_SIZE)
    batch = circs[i0:i1]
    meta_b = meta[i0:i1]
    
    print(f"[Batch {bi+1}/{nb}] Transpiling {len(batch)} circuiti...")
    tqcs = transpile(
        batch,
        backend=backend,
        optimization_level=OPT_LEVEL,
        scheduling_method="alap"
    )
    
    print(f"[Batch {bi+1}/{nb}] Running Sampler...")
    
    try:
        # SOLUZIONE: passa backend come primo argomento (mode)
        sampler = Sampler(mode=backend)  # backend oggetto, non stringa
        job = sampler.run(tqcs, shots=SHOTS)
        
        # Mostra Job ID
        try:
            jid = job.job_id()
            print(f"  Job ID: {jid}")
        except:
            pass
        
        print(f"  Attendendo risultati...")
        result = job.result()
        
        # Debug struttura per primo batch
        if bi == 0 and len(result) > 0:
            print("\n  DEBUG Struttura (primo circuito):")
            first = result[0]
            print(f"    Tipo: {type(first)}")
            if hasattr(first, 'data'):
                attrs = [a for a in dir(first.data) if not a.startswith('_')]
                print(f"    Attributi in .data: {attrs[:5]}...")
        
        # Estrazione parità per ciascun circuito
        for k, m in enumerate(meta_b):
            pub = result[k]
            
            # Usa verbose=True per primo circuito del primo batch
            verbose = (bi == 0 and k == 0)
            p, path = extract_parity_pub(pub, NQ, SHOTS, verbose=verbose)
            
            paths_used.append(path)
            
            if p is None:
                # Fallback finale
                p = 0.5
                print(f"    Circuito {k}: usando fallback 0.5")
            
            rows.append({
                **m,
                "parity_abs": float(p),
                "omega_rad_s": float(np.pi * m["n"] / (m["T_us"] * 1e-6)),
                "Gamma_raw": float(-np.log(np.clip(p, 1e-6, 0.999)) / (m["T_us"] * 1e-6))
            })
        
        # Check successo estrazione
        batch_parities = [r["parity_abs"] for r in rows[-len(batch):]]
        unique_p = set(batch_parities)
        
        if len(unique_p) == 1 and 0.5 in unique_p:
            print(f"  ATTENZIONE: Batch {bi+1} tutti fallback!")
        else:
            print(f"  Estrazione OK: {len(unique_p)} valori diversi")
    
    except Exception as e:
        print(f"  Errore nel batch {bi+1}: {e}")
        
        # Crea risultati di fallback
        for m in meta_b:
            rows.append({
                **m,
                "parity_abs": 0.5,
                "omega_rad_s": float(np.pi * m["n"] / (m["T_us"] * 1e-6)),
                "Gamma_raw": float(-np.log(0.5) / (m["T_us"] * 1e-6))
            })
            paths_used.append("(error)")

# ------------------------- SALVATAGGIO ----------------------
df = pd.DataFrame(rows)
df.to_csv(CSV_NAME, index=False)
print(f"\n✓ Salvato: {CSV_NAME}")
print(f"  Totale punti: {len(df)}")

# Diagnostica vie di estrazione
paths, counts = np.unique(paths_used, return_counts=True)
print("\nVie di estrazione usate:")
for p, c in sorted(zip(paths, counts), key=lambda x: -x[1])[:5]:
    print(f"  {p:35s} x{c}")

fallback_count = paths_used.count("(fallback)") + paths_used.count("(error)")
fallback_rate = (fallback_count / len(paths_used)) * 100

if fallback_rate > 80:
    print(f"\n⚠ ATTENZIONE: {fallback_rate:.1f}% fallback - dati NON utilizzabili!")
elif fallback_rate > 20:
    print(f"\n⚠ {fallback_rate:.1f}% fallback - qualità dati compromessa")
else:
    print(f"\n✓ Estrazione riuscita: solo {fallback_rate:.1f}% fallback")

# --------------------------- ANALISI ------------------------
def ecdf(y):
    """Calcola ECDF empirica."""
    x = np.sort(np.asarray(y))
    n = x.size
    return x, np.arange(1, n+1)/n

def fit_alpha(omega, gamma):
    """Fit α da log(Γω²) vs log(ω)."""
    x = np.log(omega)
    y = np.log(np.clip(gamma, 1e-30, None) * (omega**2))
    
    if len(np.unique(x)) < 4:
        return np.nan, np.nan
    
    a, b = np.polyfit(x, y, 1)
    rmse = float(np.sqrt(np.mean((y - (a*x + b))**2)))
    
    return float(a), rmse

# Statistiche base
ghz = df[df.state == "GHZ"]["parity_abs"].values
pro = df[df.state == "PRODUCT"]["parity_abs"].values

print(f"\nStatistiche parità:")
print(f"  GHZ:     mean={ghz.mean():.4f}, std={ghz.std():.4f}")
print(f"  PRODUCT: mean={pro.mean():.4f}, std={pro.std():.4f}")
print(f"  Δ(mean): {ghz.mean() - pro.mean():+.4f}")

# Calcola α(θ) per stato
summ_rows = []
for st in ("GHZ", "PRODUCT"):
    for th in sorted(df.theta.unique()):
        sub = df[(df.state == st) & (np.isclose(df.theta, th))]
        
        if len(sub) > 3:
            a, rmse = fit_alpha(sub.omega_rad_s.values, sub.Gamma_raw.values)
            summ_rows.append({
                "state": st,
                "theta": float(th),
                "theta_deg": float(np.degrees(th)),
                "alpha": a,
                "rmse": rmse,
                "n_points": len(sub)
            })

summ = pd.DataFrame(summ_rows)

if len(summ) > 0:
    print("\nEsponenti α:")
    for _, row in summ.iterrows():
        print(f"  {row['state']:8s} θ={row['theta_deg']:.0f}°: α={row['alpha']:.2f} (n={row['n_points']})")

# --------------------------- PLOT ---------------------------
if not df.empty and fallback_rate < 90:
    fig, axs = plt.subplots(2, 3, figsize=(15, 8))
    
    # 1) Γ vs ω
    for st, mk in (("GHZ", "o"), ("PRODUCT", "s")):
        sub = df[df.state == st]
        if len(sub) > 0:
            axs[0,0].loglog(
                sub.omega_rad_s/1e6,
                sub.Gamma_raw,
                mk,
                alpha=0.6,
                label=st
            )
    
    axs[0,0].set_xlabel("ω (MHz)")
    axs[0,0].set_ylabel("Γ (1/s)")
    axs[0,0].set_title("Raw decay rates")
    axs[0,0].grid(True, which="both", alpha=0.3)
    axs[0,0].legend()
    
    # 2) α(θ)
    if len(summ) > 0:
        for st, mk in (("GHZ", "o-"), ("PRODUCT", "s-")):
            sub = summ[summ.state == st]
            if len(sub) > 0:
                axs[0,1].plot(sub.theta_deg, sub.alpha, mk, label=st)
        
        axs[0,1].axhline(2.0, ls=":", c="gray")
        axs[0,1].axhline(3.0, ls="--", c="gray", alpha=0.4)
        axs[0,1].set_xlabel("θ (deg)")
        axs[0,1].set_ylabel("α")
        axs[0,1].set_title("State-dependent α(θ)")
        axs[0,1].grid(True, alpha=0.3)
        axs[0,1].legend()
    
    # 3) Δα
    if len(summ) > 0:
        pv = summ.pivot(index="theta_deg", columns="state", values="alpha")
        if {"GHZ", "PRODUCT"}.issubset(pv.columns):
            d_alpha = (pv["GHZ"] - pv["PRODUCT"]).dropna()
            if len(d_alpha) > 0:
                axs[0,2].plot(d_alpha.index, d_alpha.values, "d-", c="purple")
                axs[0,2].axhline(0, c="k", lw=0.8)
                axs[0,2].set_xlabel("θ (deg)")
                axs[0,2].set_ylabel("Δα")
                axs[0,2].set_title("Entanglement effect")
                axs[0,2].grid(True, alpha=0.3)
    
    # 4) ECDF parity
    if len(ghz) > 0 and len(pro) > 0:
        xg, yg = ecdf(ghz)
        xp, yp = ecdf(pro)
        axs[1,0].plot(xg, yg, lw=2, label="GHZ")
        axs[1,0].plot(xp, yp, lw=2, label="PRODUCT")
        axs[1,0].set_xlabel("Parity")
        axs[1,0].set_ylabel("ECDF")
        axs[1,0].set_title("ECDF parity")
        axs[1,0].legend()
        axs[1,0].grid(True, alpha=0.3)
    
    # 5) Violin plot parity
    if len(ghz) > 0 and len(pro) > 0:
        parts = axs[1,1].violinplot(
            [ghz, pro],
            positions=[0, 1],
            showmeans=True,
            showmedians=True
        )
        axs[1,1].set_xticks([0, 1])
        axs[1,1].set_xticklabels(["GHZ", "PRODUCT"])
        axs[1,1].set_ylabel("Parity")
        axs[1,1].set_title("Parity distributions")
        axs[1,1].grid(True, axis='y', alpha=0.3)
    
    # 6) Parity vs n
    for st, mk in (("GHZ", "o"), ("PRODUCT", "s")):
        sub = df[df.state == st]
        if len(sub) > 0:
            axs[1,2].scatter(
                sub.n,
                sub.parity_abs,
                alpha=0.6,
                label=st,
                marker=mk
            )
    
    axs[1,2].set_xlabel("n (CPMG)")
    axs[1,2].set_ylabel("Parity")
    axs[1,2].set_title("Decay vs n")
    axs[1,2].legend()
    axs[1,2].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.show()

# ---------------------- EXIT SUMMARY -----------------------
print("\n" + "="*50)
print("SUMMARY FINALE")
print("="*50)

bad = (df.parity_abs == 0.5).sum()
print(f"Punti totali: {len(df)}")
print(f"Punti con parity=0.5: {bad} ({bad/len(df):.1%})")

if fallback_rate > 80:
    print("\nDATI NON UTILIZZABILI!")
    print("  Troppi fallback - riprova con:")
    print("  - Backend diverso")
    print("  - Orario con meno coda")
    print("  - Batch più piccoli")
elif fallback_rate > 20:
    print("\nQualità dati compromessa")
    print(f"  {fallback_rate:.1f}% fallback è troppo alto")
else:
    print("\n✓ ESTRAZIONE RIUSCITA")
    
    if len(summ) > 0:
        # Calcola Δα medio
        pv = summ.pivot(index="theta_deg", columns="state", values="alpha")
        if {"GHZ", "PRODUCT"}.issubset(pv.columns):
            d_alpha = (pv["GHZ"] - pv["PRODUCT"]).dropna()
            if len(d_alpha) > 0:
                print(f"\nΔα(GHZ-PRODUCT):")
                for theta_deg, delta in d_alpha.items():
                    print(f"  θ={theta_deg:.0f}°: Δα={delta:+.3f}")
                print(f"  Media: {d_alpha.mean():+.3f}")
