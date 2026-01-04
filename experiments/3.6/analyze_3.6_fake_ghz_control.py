# ==== CONTROLLO FAKE-GHZ: Test per isolare effetto gate vs entanglement ====
# Verifica se il fattore 2.6× è dovuto ai CNOT extra o all'entanglement
# Compatible con Qiskit Runtime Open Plan - IBM Brisbane

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import warnings
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2 as Sampler
from datetime import datetime

warnings.filterwarnings("ignore")

# ===================== CONFIGURAZIONE =====================
# Test 1: Condizioni di massimo effetto (dove abbiamo visto 2.6×)
CONTROL_CONFIG = {
    'N': 3,
    'theta_deg': 30.0,  # dove l'effetto era massimo
    'T_us': 3.0,
    'n_list': [5],      # il punto specifico del rapporto 2.6×
    'shots': 4096,      # aumentato per maggiore precisione
    'states': ['FAKE_GHZ', 'PRODUCT', 'GHZ']  # tutti e tre per confronto
}

# Test 2: Sweep angolare (dopo validazione del controllo base)
ANGULAR_CONFIG = {
    'N': 3,
    'theta_deg_list': [27.0, 30.0, 33.0, 36.0, 39.0],
    'T_us': 3.0,
    'n_list': [3, 5, 7],
    'shots': 2048,
    'states': ['FAKE_GHZ', 'PRODUCT']
}

# Parametri generali
BATCH_SIZE = 15
OPT_LEVEL = 0  # CRITICO: NO ottimizzazione per preservare i CNOT
USE_BARRIERS = True  # Assicura che i CNOT non vengano cancellati
INTERLEAVE = True  # Mescola circuiti per ridurre drift
FIXED_SEED = 42  # Transpile seed fisso per consistenza

timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
CSV_NAME = f"fake_ghz_control_{timestamp}.csv"

print("="*60)
print("ESPERIMENTO DI CONTROLLO: FAKE-GHZ")
print("="*60)
print("Obiettivo: Isolare effetto gate CNOT vs entanglement")
print("Metodo: Fake-GHZ usa 2 CNOT ma produce stato separabile")
print("="*60)

# ===================== FUNZIONI CIRCUITI =====================
def us_to_dt(us, dt):
    """Converti microsecondi in unità dt."""
    return max(1, int(round((us * 1e-6) / dt)))

def prep_GHZ(qc, N, theta):
    """GHZ standard: cos(θ)|000> + sin(θ)|111>"""
    qc.ry(2*theta, 0)
    for j in range(1, N):
        qc.cx(0, j)

def prep_PRODUCT(qc, N, theta):
    """Stato prodotto: cos(θ)|000> + sin(θ)|100>"""
    qc.ry(2*theta, 0)
    # Altri qubit restano in |0>

def prep_FAKE_GHZ(qc, N, theta):
    """
    FAKE GHZ: Usa 2 CNOT come GHZ ma produce stato separabile
    Applica CNOT poi li annulla, lasciando stato prodotto
    MA con stesso overhead di gate del GHZ vero
    """
    # Step 1: Stessa rotazione iniziale
    qc.ry(2*theta, 0)
    
    # Step 2: Applica CNOT come nel GHZ
    qc.cx(0, 1)
    
    if USE_BARRIERS:
        qc.barrier()  # CRITICO: previene cancellazione
    
    # Step 3: Annulla il CNOT (stesso gate = inverso)
    qc.cx(0, 1)
    
    # Per N=3, aggiungiamo anche il secondo CNOT annullato
    if N >= 3:
        qc.cx(0, 2)
        if USE_BARRIERS:
            qc.barrier()
        qc.cx(0, 2)
    
    # Risultato: stato |ψ> = cos(θ)|000> + sin(θ)|100>
    # MA ha subito 2 CNOT fisici (4 se N=3 con entrambe le coppie)

def build_circuit(N, theta, state, T_us, n, dt):
    """Costruisce circuito completo con CPMG"""
    qc = QuantumCircuit(N, N)
    
    # Preparazione stato
    if state == "GHZ":
        prep_GHZ(qc, N, theta)
    elif state == "PRODUCT":
        prep_PRODUCT(qc, N, theta)
    elif state == "FAKE_GHZ":
        prep_FAKE_GHZ(qc, N, theta)
    else:
        raise ValueError(f"Stato non riconosciuto: {state}")
    
    # CPMG sequence
    seg_us = T_us / (2.0 * n)
    dseg = us_to_dt(seg_us, dt)
    
    for _ in range(n):
        for q in range(N):
            qc.delay(dseg, q, unit='dt')
        for q in range(N):
            qc.x(q)
        for q in range(N):
            qc.delay(dseg, q, unit='dt')
    
    # Misura parità X
    for q in range(N):
        qc.h(q)
    qc.measure(range(N), range(N))
    
    theta_deg = np.degrees(theta) if isinstance(theta, (int, float)) else theta
    qc.name = f"{state}_N{N}_th{theta_deg:.1f}_T{T_us}_n{n}"
    return qc

# ===================== ESTRAZIONE PARITÀ =====================
def extract_parity_robust(pub, n_qubits):
    """Estrazione robusta parità da SamplerV2"""
    if hasattr(pub, 'data'):
        for attr_name in dir(pub.data):
            if attr_name.startswith('_'):
                continue
            attr = getattr(pub.data, attr_name)
            
            if hasattr(attr, 'get_counts'):
                counts = attr.get_counts()
                if counts:
                    total = sum(counts.values())
                    if total == 0:
                        return 0.5
                    s = 0
                    for bitstr, cnt in counts.items():
                        if isinstance(bitstr, int):
                            bitstr = format(bitstr, f"0{n_qubits}b")
                        ones = bitstr.count("1")
                        s += cnt * ((-1)**ones)
                    return abs(s/total)
    return 0.5

# ===================== BACKEND CONNECTION =====================
print("\nConnessione IBM Quantum...")
service = QiskitRuntimeService()

# Priorità Brisbane (dove sono stati fatti esperimenti originali)
backend = None
for name in ["ibm_brisbane", "ibm_torino", "ibm_sherbrooke"]:
    try:
        b = service.backend(name)
        if b.status().operational:
            backend = b
            print(f"Backend selezionato: {name}")
            print(f"  Pending jobs: {b.status().pending_jobs}")
            break
    except:
        pass

if not backend:
    raise RuntimeError("Nessun backend disponibile")

dt = backend.configuration().dt
print(f"  dt = {dt*1e9:.3f} ns")

# ===================== TEST 1: CONTROLLO BASE =====================
print("\n" + "="*40)
print("TEST 1: Controllo θ=30°, n=5")
print("Confronto: FAKE_GHZ vs PRODUCT vs GHZ")
print("="*40)

circuits_test1 = []
metadata_test1 = []

theta_rad = np.radians(CONTROL_CONFIG['theta_deg'])
for n in CONTROL_CONFIG['n_list']:
    for state in CONTROL_CONFIG['states']:
        qc = build_circuit(
            CONTROL_CONFIG['N'], 
            theta_rad, 
            state, 
            CONTROL_CONFIG['T_us'], 
            n, 
            dt
        )
        circuits_test1.append(qc)
        metadata_test1.append({
            'test': 'control',
            'N': CONTROL_CONFIG['N'],
            'theta_deg': CONTROL_CONFIG['theta_deg'],
            'state': state,
            'n': n,
            'T_us': CONTROL_CONFIG['T_us']
        })

# Interleaving per ridurre drift
if INTERLEAVE:
    import random
    random.seed(FIXED_SEED)
    indices = list(range(len(circuits_test1)))
    random.shuffle(indices)
    circuits_test1 = [circuits_test1[i] for i in indices]
    metadata_test1 = [metadata_test1[i] for i in indices]

print(f"Circuiti Test 1: {len(circuits_test1)}")

# ===================== TEST 2: SWEEP ANGOLARE =====================
print("\n" + "="*40)
print("TEST 2: Sweep angolare")
print(f"θ = {ANGULAR_CONFIG['theta_deg_list']}°")
print(f"n = {ANGULAR_CONFIG['n_list']}")
print("="*40)

circuits_test2 = []
metadata_test2 = []

for theta_deg in ANGULAR_CONFIG['theta_deg_list']:
    theta_rad = np.radians(theta_deg)
    for n in ANGULAR_CONFIG['n_list']:
        for state in ANGULAR_CONFIG['states']:
            qc = build_circuit(
                ANGULAR_CONFIG['N'],
                theta_rad,
                state,
                ANGULAR_CONFIG['T_us'],
                n,
                dt
            )
            circuits_test2.append(qc)
            metadata_test2.append({
                'test': 'angular',
                'N': ANGULAR_CONFIG['N'],
                'theta_deg': theta_deg,
                'state': state,
                'n': n,
                'T_us': ANGULAR_CONFIG['T_us']
            })

if INTERLEAVE:
    indices = list(range(len(circuits_test2)))
    random.shuffle(indices)
    circuits_test2 = [circuits_test2[i] for i in indices]
    metadata_test2 = [metadata_test2[i] for i in indices]

print(f"Circuiti Test 2: {len(circuits_test2)}")

# ===================== ESECUZIONE BATCH =====================
all_circuits = circuits_test1 + circuits_test2
all_metadata = metadata_test1 + metadata_test2

print(f"\nTotale circuiti: {len(all_circuits)}")
print(f"Batch necessari: {(len(all_circuits) + BATCH_SIZE - 1) // BATCH_SIZE}")

results = []
for i in range(0, len(all_circuits), BATCH_SIZE):
    batch = all_circuits[i:i+BATCH_SIZE]
    meta_batch = all_metadata[i:i+BATCH_SIZE]
    
    print(f"\n[Batch {i//BATCH_SIZE + 1}] Transpiling {len(batch)} circuiti...")
    print(f"  Optimization level: {OPT_LEVEL}")
    print(f"  Seed: {FIXED_SEED}")
    
    transpiled = transpile(
        batch,
        backend=backend,
        optimization_level=OPT_LEVEL,
        seed_transpiler=FIXED_SEED,
        scheduling_method="alap"
    )
    
    # Verifica che i CNOT siano preservati
    for t_qc in transpiled[:1]:  # Check primo circuito
        cx_count = sum(1 for inst in t_qc.data if inst.operation.name == 'cx')
        print(f"  CNOT count nel circuito transpilato: {cx_count}")
    
    print(f"[Batch {i//BATCH_SIZE + 1}] Submitting...")
    sampler = Sampler(mode=backend)
    
    # Determina shots
    shots = CONTROL_CONFIG['shots'] if meta_batch[0]['test'] == 'control' else ANGULAR_CONFIG['shots']
    
    job = sampler.run(transpiled, shots=shots)
    print(f"  Job ID: {job.job_id()}")
    print("  Waiting...")
    
    result = job.result()
    
    for idx, meta in enumerate(meta_batch):
        parity = extract_parity_robust(result[idx], meta['N'])
        results.append({
            **meta,
            'parity_abs': parity,
            'omega_rad_s': np.pi * meta['n'] / (meta['T_us'] * 1e-6),
            'Gamma_raw': -np.log(np.clip(parity, 1e-6, 0.999)) / (meta['T_us'] * 1e-6)
        })
    
    print("  ✓ Batch completato")

# ===================== SALVATAGGIO =====================
df = pd.DataFrame(results)
df.to_csv(CSV_NAME, index=False)
print(f"\n✓ Salvato: {CSV_NAME}")

# ===================== ANALISI IMMEDIATA =====================
print("\n" + "="*60)
print("RISULTATI CONTROLLO FAKE-GHZ")
print("="*60)

# Test 1: Controllo base
df_control = df[df['test'] == 'control']
if len(df_control) > 0:
    print("\n--- TEST 1: θ=30°, n=5 ---")
    for state in ['PRODUCT', 'FAKE_GHZ', 'GHZ']:
        data = df_control[df_control['state'] == state]
        if len(data) > 0:
            parity = data['parity_abs'].mean()
            gamma = data['Gamma_raw'].mean()
            print(f"{state:10s}: Parity={parity:.3f}, Γ={gamma:.1f} s⁻¹")
    
    # Calcola rapporti
    prod_gamma = df_control[df_control['state'] == 'PRODUCT']['Gamma_raw'].mean()
    fake_gamma = df_control[df_control['state'] == 'FAKE_GHZ']['Gamma_raw'].mean()
    ghz_gamma = df_control[df_control['state'] == 'GHZ']['Gamma_raw'].mean()
    
    if prod_gamma > 0:
        print(f"\nRapporti decay rate:")
        print(f"  Γ_fake/Γ_prod = {fake_gamma/prod_gamma:.2f}")
        print(f"  Γ_GHZ/Γ_prod  = {ghz_gamma/prod_gamma:.2f}")
        
        # CRITERIO DECISIONALE
        ratio_fake = fake_gamma/prod_gamma
        if ratio_fake < 1.3:  # Fake ≈ Product
            print("\nFAKE_GHZ ≈ PRODUCT")
            print(" Interpretazione: contributo dei CNOT non dominante rispetto al gap GHZ/PRODUCT.")
        elif ratio_fake > 2.0:  # Fake ≈ GHZ
            print("\nFAKE_GHZ ≈ GHZ")
            print("  Interpretazione: il gap può includere una componente legata ai CNOT.")
        else:
            print("\nRegime intermedio (effetto misto)")
            print(f"  Stima componente CNOT (relativa): ~{(ratio_fake-1)/(ghz_gamma/prod_gamma-1)*100:.0f}%")

# Test 2: Modulazione angolare
df_angular = df[df['test'] == 'angular']
if len(df_angular) > 0:
    print("\n--- TEST 2: Modulazione angolare ---")
    for theta_deg in sorted(df_angular['theta_deg'].unique()):
        fake = df_angular[(df_angular['state'] == 'FAKE_GHZ') & 
                         (df_angular['theta_deg'] == theta_deg)]['parity_abs'].mean()
        prod = df_angular[(df_angular['state'] == 'PRODUCT') & 
                         (df_angular['theta_deg'] == theta_deg)]['parity_abs'].mean()
        delta = fake - prod
        print(f"θ={theta_deg:5.1f}°: Δ(FAKE-PROD)={delta:+.4f}")
    
    # Se tutti i Δ ≈ 0, la modulazione cos²θ non è dovuta ai gate
    deltas = []
    for theta_deg in sorted(df_angular['theta_deg'].unique()):
        fake = df_angular[(df_angular['state'] == 'FAKE_GHZ') & 
                         (df_angular['theta_deg'] == theta_deg)]['parity_abs'].mean()
        prod = df_angular[(df_angular['state'] == 'PRODUCT') & 
                         (df_angular['theta_deg'] == theta_deg)]['parity_abs'].mean()
        deltas.append(abs(fake - prod))
    
    mean_delta = np.mean(deltas)
    if mean_delta < 0.02:
        print(f"\n✓ Δ medio = {mean_delta:.4f} ≈ 0")
        print("  La modulazione cos²θ NON è dovuta ai CNOT")

# ===================== PLOT =====================
if len(df_control) > 0:
    fig, ax = plt.subplots(1, 1, figsize=(8, 6))
    
    states = ['PRODUCT', 'FAKE_GHZ', 'GHZ']
    parities = []
    errors = []
    
    for state in states:
        data = df_control[df_control['state'] == state]['parity_abs']
        parities.append(data.mean() if len(data) > 0 else 0)
        errors.append(data.std() if len(data) > 1 else 0)
    
    x = np.arange(len(states))
    ax.bar(x, parities, yerr=errors, capsize=5, 
           color=['blue', 'orange', 'green'], alpha=0.7)
    ax.set_xticks(x)
    ax.set_xticklabels(states)
    ax.set_ylabel('Parity')
    ax.set_title('Control Test: FAKE_GHZ vs PRODUCT vs GHZ (θ=30°, n=5)')
    ax.grid(True, alpha=0.3)
    
    # Aggiungi linee di riferimento
    ax.axhline(parities[0], color='blue', linestyle='--', alpha=0.5, label='PRODUCT level')
    if len(parities) > 2:
        ax.axhline(parities[2], color='green', linestyle='--', alpha=0.5, label='GHZ level')
    
    ax.legend()
    
    plt.tight_layout()
    plt.savefig(f'fake_ghz_control_plot_{timestamp}.png', dpi=150)
    plt.show()

print("\n" + "="*60)
print("ESPERIMENTO COMPLETATO")
print("="*60)
print(f"File salvato: {CSV_NAME}")
