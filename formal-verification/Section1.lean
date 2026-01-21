/-
QFTT-WESH Section 1: Unified Formal Verification

Structure follows Section 1 of the manuscript:

PART I:    Foundations — Spacetime structures, Minkowski causality
PART II:   WESH-Noether conservation — Appendix G formalism (Matrix-based)
PART III:  Constraint-driven selection — CPT symmetry, quadratic dissipator
PART IV:   The WESH master equation — Generator, causal kernel, Rényi-2, No-signaling
PART V:    Bootstrap and Eigentimes — Time-production functional Γ, monotonicity
PART VI:   Foundational consistency — α=2 selection, N² scaling, G→0 decoupling

Lean 4.24.0 / Mathlib f897ebcf
-/

/-
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

set_option linter.mathlibStandardSet false
open scoped BigOperators Real Nat Classical Pointwise
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-!
## PART I: Foundations — Spacetime structures, Minkowski causality

The QFTT-WESH framework begins with spacetime as the arena for the time field T(x).
We define Minkowski causality and the bilocal causal kernel γ(x,y) that enforces
locality of the collapse dynamics.
-/

/-- Spacetime points as 4 real coordinates (t,x,y,z). -/
structure WESH_SpacetimePoint where
  coords : Fin 4 → ℝ

/-- Minkowski causal condition: Δt² - Δx² - Δy² - Δz² ≥ 0. -/
def WESH_is_causal (x y : WESH_SpacetimePoint) : Prop :=
  let t1 := x.coords 0; let x1 := x.coords 1; let y1 := x.coords 2; let z1 := x.coords 3
  let t2 := y.coords 0; let x2 := y.coords 1; let y2 := y.coords 2; let z2 := y.coords 3
  (t2 - t1) ^ 2 - (x2 - x1) ^ 2 - (y2 - y1) ^ 2 - (z2 - z1) ^ 2 ≥ 0

/-- Causal Heaviside indicator Θ(x,y). -/
def WESH_causal_theta (x y : WESH_SpacetimePoint) : ℝ :=
  if WESH_is_causal x y then 1 else 0

/-- Euclidean distance in R⁴ for the exponential profile (placeholder). -/
noncomputable def WESH_spacetime_dist (x y : WESH_SpacetimePoint) : ℝ :=
  let t1 := x.coords 0; let x1 := x.coords 1; let y1 := x.coords 2; let z1 := x.coords 3
  let t2 := y.coords 0; let x2 := y.coords 1; let y2 := y.coords 2; let z2 := y.coords 3
  Real.sqrt ((t1 - t2) ^ 2 + (x1 - x2) ^ 2 + (y1 - y2) ^ 2 + (z1 - z2) ^ 2)

/-- Minkowski squared interval: Δt² - Δx² - Δy² - Δz². -/
def WESH_minkowski_sq (x y : WESH_SpacetimePoint) : ℝ :=
  let dt := y.coords 0 - x.coords 0
  let dx := y.coords 1 - x.coords 1
  let dy := y.coords 2 - x.coords 2
  let dz := y.coords 3 - x.coords 3
  dt^2 - dx^2 - dy^2 - dz^2

/-- Timelike distance: √(max(0, s²)) where s² is Minkowski interval.
    Zero outside the light cone, proper time inside. -/
noncomputable def WESH_timelike_dist (x y : WESH_SpacetimePoint) : ℝ :=
  Real.sqrt (max 0 (WESH_minkowski_sq x y))

/-- Exponential profile using timelike separation (Lorentz-invariant). -/
noncomputable def WESH_K_xi_timelike (xi : ℝ) (x y : WESH_SpacetimePoint) : ℝ :=
  Real.exp (-WESH_timelike_dist x y / xi)

/-- Timelike distance is non-negative. -/
theorem WESH_timelike_dist_nonneg (x y : WESH_SpacetimePoint) :
    0 ≤ WESH_timelike_dist x y := by
  unfold WESH_timelike_dist
  exact Real.sqrt_nonneg _

/-- Exponential spatial profile K_ξ(x,y) = exp(-|x-y|/ξ).
    
    NOTE: The derivation of the correlation scale ξ and rate γ₀ from Planck units,
    including the proof that V_ξ = 8πξ⁴, is developed in AppendixA.lean. -/
noncomputable def WESH_K_xi (xi : ℝ) (x y : WESH_SpacetimePoint) : ℝ :=
  Real.exp (-WESH_spacetime_dist x y / xi)

/-- Bilocal causal rate kernel γ(x,y) = γ₀ K_ξ Θ / N². -/
noncomputable def WESH_gamma_kernel (gamma_0 N xi : ℝ) (x y : WESH_SpacetimePoint) : ℝ :=
  gamma_0 * WESH_K_xi xi x y * WESH_causal_theta x y / (N ^ 2)

/-- Spacelike pairs have vanishing kernel (causality enforcement). -/
theorem WESH_gamma_spacelike_vanishing (gamma_0 N xi : ℝ) (x y : WESH_SpacetimePoint)
    (h_spacelike : ¬ WESH_is_causal x y) : WESH_gamma_kernel gamma_0 N xi x y = 0 := by
  unfold WESH_gamma_kernel WESH_causal_theta
  have hθ : (if WESH_is_causal x y then 1 else 0) = (0 : ℝ) := if_neg h_spacelike
  rw [hθ]; ring

/-- The causal kernel is non-negative under physical assumptions. -/
theorem WESH_gamma_kernel_nonneg (gamma_0 N xi : ℝ) (x y : WESH_SpacetimePoint)
    (hγ0 : 0 ≤ gamma_0) (hN : 0 < N) (_hxi : 0 < xi) :
    0 ≤ WESH_gamma_kernel gamma_0 N xi x y := by
  unfold WESH_gamma_kernel WESH_K_xi WESH_causal_theta
  by_cases h : WESH_is_causal x y
  · -- Causal case: θ = 1
    simp only [if_pos h]
    have hexp : 0 < Real.exp (-WESH_spacetime_dist x y / xi) := Real.exp_pos _
    have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
    positivity
  · -- Spacelike case: θ = 0, result is 0
    simp only [if_neg h, mul_zero, zero_div, le_refl]

/-!
### Future-directed (retarded) causal kernel

The physical kernel should be future-directed: Δt ≥ 0 in addition to being causal.
This excludes retrocausal contributions and matches the retarded propagator structure.
-/

/-- Future-directed causal relation: Δt ≥ 0 AND (timelike or lightlike). -/
def WESH_is_future_causal (x y : WESH_SpacetimePoint) : Prop :=
  let dt := y.coords 0 - x.coords 0
  dt ≥ 0 ∧ WESH_is_causal x y

/-- Heaviside indicator for future-directed causal pairs. -/
def WESH_theta_future (x y : WESH_SpacetimePoint) : ℝ :=
  if WESH_is_future_causal x y then 1 else 0

/-- Retarded exponential profile: exp(-Δt/ξ) with Δt = t_y - t_x. -/
noncomputable def WESH_K_xi_retarded (xi : ℝ) (x y : WESH_SpacetimePoint) : ℝ :=
  let dt := y.coords 0 - x.coords 0
  Real.exp (-dt / xi)

/-- Retarded causal kernel: γ₀ K_ξ^ret Θ_future / N². -/
noncomputable def WESH_gamma_kernel_retarded (gamma_0 N xi : ℝ) (x y : WESH_SpacetimePoint) : ℝ :=
  gamma_0 * WESH_K_xi_retarded xi x y * WESH_theta_future x y / (N ^ 2)

/-- Future-directed theta is non-negative. -/
theorem WESH_theta_future_nonneg (x y : WESH_SpacetimePoint) :
    0 ≤ WESH_theta_future x y := by
  unfold WESH_theta_future
  by_cases h : WESH_is_future_causal x y <;> simp [h]

/-- Retarded kernel vanishes for non-future-causal pairs. -/
theorem WESH_gamma_retarded_nonfuture_vanishing (gamma_0 N xi : ℝ) (x y : WESH_SpacetimePoint)
    (h_nonfuture : ¬ WESH_is_future_causal x y) : WESH_gamma_kernel_retarded gamma_0 N xi x y = 0 := by
  unfold WESH_gamma_kernel_retarded WESH_theta_future
  have hθ : (if WESH_is_future_causal x y then 1 else 0) = (0 : ℝ) := if_neg h_nonfuture
  rw [hθ]; ring

/-!
## PART II: WESH-Noether Conservation — Appendix G formalism (Matrix-based)

The WESH-Noether theorem establishes that conserved charges Q satisfy L†[Q] = 0
if and only if Q commutes with H and all active Lindblad operators L_k.
This is the pre-geometric path independence that underlies the s/t distinction.
-/

/-- Lindblad dissipator adjoint D†_L[A] = LAL - ½(L²A + AL²). -/
def lindbladAdjoint {n : Type} [Fintype n] [DecidableEq n] (L : Matrix n n ℂ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  L * A * L - (1 / 2 : ℂ) • (L ^ 2 * A + A * L ^ 2)

/-- WESH generator adjoint L†[A] = -i[H, A] + ∑_k γ_k D†_{L_k}[A]. -/
def weshGeneratorAdjoint {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I) • (H * A - A * H) +
  L_gamma.foldl (fun acc p => acc + (p.2 : ℂ) • lindbladAdjoint p.1 A) 0

/-- Pre-geometric WESH-Noether condition: L†[Q] = 0.
    
    NOTE: The complete WESH-Noether theorem structure is developed in:
    - AppendixG.lean: Matrix formalism, Prop G.2 (Noether ⟺ commutation), 
      Cor G.1.1 (path independence), generator duality
    - AppendixC.lean: T-neutrality, GKSL identity, no-s-footprint theorem -/
def weshNoether {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q : Matrix n n ℂ) : Prop :=
  weshGeneratorAdjoint H L_gamma Q = 0

/-- Trace of B[A,B] vanishes. -/
lemma trace_commutator_self {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) : Matrix.trace (B * (A * B - B * A)) = 0 := by
  simp [mul_sub, Matrix.trace_mul_comm B]; norm_num [Matrix.mul_assoc, Matrix.trace_mul_comm B]

/-- Trace of Q D†_L[Q] = -½ Tr([L,Q]†[L,Q]). -/
lemma trace_lindblad_adjoint_self {n : Type} [Fintype n] [DecidableEq n] (L Q : Matrix n n ℂ) (hL : L.IsHermitian) (hQ : Q.IsHermitian) :
  Matrix.trace (Q * lindbladAdjoint L Q) = - (1 / 2 : ℂ) * Matrix.trace (Matrix.conjTranspose (L * Q - Q * L) * (L * Q - Q * L)) := by
    unfold lindbladAdjoint
    simp +decide [mul_sub, mul_add, mul_assoc, Matrix.sub_mul, Matrix.trace_mul_comm L, hL.eq, hQ.eq]; ring_nf
    norm_num [sq, Matrix.mul_assoc]

/-- Trace of A†A has non-negative real part. -/
lemma trace_conj_mul_self_nonneg {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : 0 ≤ (Matrix.trace (Matrix.conjTranspose A * A)).re := by
  norm_num [Matrix.trace, Matrix.mul_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- Trace of A†A = 0 iff A = 0. -/
lemma trace_conj_mul_self_eq_zero_iff {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Matrix.trace (Matrix.conjTranspose A * A) = 0 ↔ A = 0 := by
  have h_trace : (Matrix.trace (Matrix.conjTranspose A * A)).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    simp +decide [Matrix.trace, Matrix.mul_apply, Complex.normSq, Complex.sq_norm]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  constructor <;> intro h <;> simp_all +decide [Complex.ext_iff]
  have h_zero : ∀ i j, ‖A i j‖^2 = 0 := fun i j => by
    rw [eq_comm] at h_trace
    exact le_antisymm (h_trace ▸ Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (‖A i j‖)) (Finset.mem_univ i) |> le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (‖A i j‖)) (Finset.mem_univ j))) (sq_nonneg _)
  exact Matrix.ext fun i j => norm_eq_zero.mp <| sq_eq_zero_iff.mp <| h_zero i j

/-- The trace of Q L†[Q] equals the sum over dissipators. -/
lemma trace_wesh_generator_adjoint_eq_sum {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q : Matrix n n ℂ) :
  Matrix.trace (Q * weshGeneratorAdjoint H L_gamma Q) =
  (L_gamma.map (fun p => (p.2 : ℂ) * Matrix.trace (Q * lindbladAdjoint p.1 Q))).sum := by
    unfold weshGeneratorAdjoint
    induction' L_gamma using List.reverseRecOn with p L_gamma ih
    · simp +decide [Matrix.mul_sub, mul_assoc, Matrix.trace_mul_comm (Q : Matrix n n ℂ)]
    · simp_all +decide [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, List.foldl_append]
      linear_combination' ih

/-- If WESH-Noether holds, all active Lindblad operators commute with Q. -/
lemma wesh_noether_implies_lindblad_commute {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q : Matrix n n ℂ)
  (_hH : H.IsHermitian) (hQ : Q.IsHermitian)
  (hL : ∀ p ∈ L_gamma, p.1.IsHermitian)
  (h_gamma : ∀ p ∈ L_gamma, 0 ≤ p.2)
  (h_noether : weshNoether H L_gamma Q) :
  ∀ p ∈ L_gamma, p.2 > 0 → Commute p.1 Q := by
    have h_trace_zero : Matrix.trace (Q * weshGeneratorAdjoint H L_gamma Q) = 0 := by
      unfold weshNoether at h_noether; aesop
    have h_lindblad_trace_zero : (L_gamma.map (fun p => (p.2 : ℂ) * Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)))).sum = 0 := by
      have h_lindblad_trace_zero : Matrix.trace (Q * weshGeneratorAdjoint H L_gamma Q) = - (1 / 2 : ℂ) * (L_gamma.map (fun p => (p.2 : ℂ) * Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)))).sum := by
        rw [trace_wesh_generator_adjoint_eq_sum]
        have h_lindblad_trace_zero : ∀ p ∈ L_gamma, Matrix.trace (Q * lindbladAdjoint p.1 Q) = - (1 / 2 : ℂ) * Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)) := fun p a => trace_lindblad_adjoint_self p.1 Q (hL p a) hQ
        rw [← List.sum_map_mul_left]
        exact congr_arg _ (List.map_congr_left fun p hp => by rw [h_lindblad_trace_zero p hp]; ring)
      grind
    have h_each_term_zero : ∀ p ∈ L_gamma, (p.2 : ℂ) * Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)) = 0 := by
      have h_each_term_zero : ∀ p ∈ L_gamma, 0 ≤ (p.2 : ℝ) * (Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1))).re := fun p hp => mul_nonneg (h_gamma p hp) (trace_conj_mul_self_nonneg _)
      have h_each_term_zero : ∀ p ∈ L_gamma, (p.2 : ℝ) * (Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1))).re = 0 := by
        have h_each_term_zero : ∀ {l : List ℝ}, (∀ x ∈ l, 0 ≤ x) → List.sum l = 0 → ∀ x ∈ l, x = 0 := fun {l} a a_1 x a_2 => List.all_zero_of_le_zero_le_of_sum_eq_zero a a_1 a_2
        intros p hp
        have h_sum_zero : List.sum (List.map (fun p => (p.2 : ℝ) * (Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1))).re) L_gamma) = 0 := by
          convert congr_arg Complex.re h_lindblad_trace_zero using 1
          induction' L_gamma with p L_gamma ih
          · contradiction
          · induction' (p :: L_gamma) with p L_gamma ih <;> norm_num [Complex.ext_iff] at *; linarith
        exact h_each_term_zero (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact ‹∀ p ∈ L_gamma, 0 ≤ p.2 * ((p.1 * Q - Q * p.1).conjTranspose * (p.1 * Q - Q * p.1)).trace.re› p hp) h_sum_zero _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
      intro p hp; specialize h_each_term_zero p hp; simp_all +decide [Complex.ext_iff]
      have h_trace_imag_zero : ∀ A : Matrix n n ℂ, (Matrix.trace (Matrix.conjTranspose A * A)).im = 0 := by
        simp +decide [Matrix.trace, Matrix.mul_apply]
        exact fun A => Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => by ring
      specialize h_trace_imag_zero (p.1 * Q - Q * p.1); simp_all +decide [Matrix.conjTranspose_mul]
    intro p hp hp_pos; specialize h_each_term_zero p hp; simp_all +decide
    have h_comm : p.1 * Q - Q * p.1 = 0 := by
      have h_comm : Matrix.trace (Matrix.conjTranspose (p.1 * Q - Q * p.1) * (p.1 * Q - Q * p.1)) = 0 := by
        convert h_each_term_zero.resolve_left hp_pos.ne' using 1; simp +decide [Matrix.conjTranspose_mul]
      exact (trace_conj_mul_self_eq_zero_iff (p.1 * Q - Q * p.1)).mp h_comm
    exact sub_eq_zero.mp h_comm

/-- If L and Q commute, then D†_L[Q] = 0. -/
lemma commute_implies_lindblad_adjoint_zero {n : Type} [Fintype n] [DecidableEq n]
  (L Q : Matrix n n ℂ) (h : Commute L Q) : lindbladAdjoint L Q = 0 := by
    ext i j; unfold lindbladAdjoint
    simp +decide [sq, mul_assoc, h.eq]
    simp +decide [← mul_assoc, h.eq]; ring

/-- Proposition G.2: WESH-Noether ⟺ [H,Q]=0 ∧ ∀k, γ_k>0 → [L_k,Q]=0. -/
theorem wesh_noether_iff_commute {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q : Matrix n n ℂ)
  (hH : H.IsHermitian) (hQ : Q.IsHermitian)
  (hL : ∀ p ∈ L_gamma, p.1.IsHermitian)
  (h_gamma : ∀ p ∈ L_gamma, 0 ≤ p.2) :
  weshNoether H L_gamma Q ↔ Commute H Q ∧ (∀ p ∈ L_gamma, p.2 > 0 → Commute p.1 Q) := by
    -- Save references before simp_all transforms them
    have hL_saved := hL
    have h_gamma_saved := h_gamma
    constructor <;> intros h'
    · -- Forward direction
      have h_commute : ∀ p ∈ L_gamma, p.2 > 0 → Commute p.1 Q := by
        exact wesh_noether_implies_lindblad_commute H L_gamma Q hH hQ hL_saved h_gamma_saved h'
      have h_hamiltonian : (-Complex.I) • (H * Q - Q * H) = 0 := by
        unfold weshNoether at h'
        have h_ham : (-Complex.I) • (H * Q - Q * H) = - (L_gamma.foldl (fun acc p => acc + (p.2 : ℂ) • lindbladAdjoint p.1 Q) 0) := eq_neg_of_add_eq_zero_left h'
        have h_lindblad_zero : ∀ p ∈ L_gamma, (p.2 : ℂ) • lindbladAdjoint p.1 Q = 0 := by
          intro p hp
          have h_gam := h_gamma_saved p hp
          specialize h_commute p hp; by_cases hpos : p.2 > 0 <;> simp_all +decide [lindbladAdjoint]
          · simp_all +decide [sq, mul_assoc, Commute.eq]; exact Or.inr (by ext i j; norm_num; ring)
          · exact Or.inl (le_antisymm hpos h_gam)
        have h_foldl_zero : ∀ {L : List (Matrix n n ℂ × ℝ)}, (∀ q ∈ L, (q.2 : ℂ) • lindbladAdjoint q.1 Q = 0) → List.foldl (fun acc q => acc + (q.2 : ℂ) • lindbladAdjoint q.1 Q) 0 L = 0 := by
          intros L hL'; induction' L using List.reverseRecOn with q L ih <;> aesop
        rw [h_ham, h_foldl_zero h_lindblad_zero, neg_zero]
      simp_all +decide [Commute, sub_eq_zero]
      exact ⟨by simp_all +decide [SemiconjBy], h_commute⟩
    · -- Backward direction
      unfold weshNoether weshGeneratorAdjoint
      have h_zero_terms : ∀ p ∈ L_gamma, p.2 > 0 → lindbladAdjoint p.1 Q = 0 := fun p hp hp_pos => commute_implies_lindblad_adjoint_zero p.1 Q (h'.2 p hp hp_pos)
      have h_sum_zero : List.foldl (fun (acc : Matrix n n ℂ) (p : Matrix n n ℂ × ℝ) => acc + (p.2 : ℂ) • lindbladAdjoint p.1 Q) 0 L_gamma = 0 := by
        have h_sum_zero' : ∀ p ∈ L_gamma, (p.2 : ℂ) • lindbladAdjoint p.1 Q = 0 := by
          intro p hp
          have h_gam := h_gamma_saved p hp
          specialize h_zero_terms p hp; cases lt_or_eq_of_le h_gam <;> aesop
        have h_foldl : ∀ {l : List (Matrix n n ℂ × ℝ)}, (∀ q ∈ l, (q.2 : ℂ) • lindbladAdjoint q.1 Q = 0) → List.foldl (fun (acc : Matrix n n ℂ) (q : Matrix n n ℂ × ℝ) => acc + (q.2 : ℂ) • lindbladAdjoint q.1 Q) 0 l = 0 := by
          intros l hl; induction' l using List.reverseRecOn with q l ih <;> aesop
        exact h_foldl h_sum_zero'
      simp_all +decide [← h'.1.eq]

/-- WESH generator (primal): L[ρ] = i[H, ρ] + ∑_k γ_k D_{L_k}[ρ]. -/
def weshGenerator {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (rho : Matrix n n ℂ) : Matrix n n ℂ :=
  (Complex.I) • (H * rho - rho * H) +
  L_gamma.foldl (fun acc p => acc + (p.2 : ℂ) • lindbladAdjoint p.1 rho) 0

/-- Duality: Tr(Q L[ρ]) = Tr(L†[Q] ρ). -/
lemma wesh_generator_duality {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q rho : Matrix n n ℂ)
  (hL : ∀ p ∈ L_gamma, p.1.IsHermitian) :
  Matrix.trace (Q * weshGenerator H L_gamma rho) = Matrix.trace (weshGeneratorAdjoint H L_gamma Q * rho) := by
    unfold weshGenerator weshGeneratorAdjoint
    induction' L_gamma using List.reverseRecOn with p L_gamma ih
    · simp +decide [mul_assoc, mul_sub, sub_mul, Matrix.trace_mul_comm Q]
      rw [← Matrix.trace_mul_comm, Matrix.mul_assoc]
    · have h_trace : Matrix.trace (Q * lindbladAdjoint L_gamma.1 rho) = Matrix.trace (lindbladAdjoint L_gamma.1 Q * rho) := by
        unfold lindbladAdjoint
        simp +decide [sq, mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.trace_mul_comm L_gamma.1]; ring
      simp_all +decide [Matrix.mul_add, Matrix.add_mul]
      linear_combination' ih

/-- Corollary G.1.1: Path independence — d/ds⟨Q⟩ = 0. -/
theorem wesh_path_independence {n : Type} [Fintype n] [DecidableEq n]
  (H : Matrix n n ℂ) (L_gamma : List (Matrix n n ℂ × ℝ)) (Q rho : Matrix n n ℂ)
  (hL : ∀ p ∈ L_gamma, p.1.IsHermitian)
  (h_noether : weshNoether H L_gamma Q) :
  Matrix.trace (Q * weshGenerator H L_gamma rho) = 0 := by
    have h_dual : Matrix.trace (Q * weshGenerator H L_gamma rho) = Matrix.trace (weshGeneratorAdjoint H L_gamma Q * rho) := wesh_generator_duality H L_gamma Q rho hL
    unfold weshNoether at h_noether; aesop

/-- Pre-geometric WESH-Noether structure (Appendix G). -/
structure PreGeometricWESH (n : Type) [Fintype n] [DecidableEq n] where
  H : Matrix n n ℂ
  L_gamma : List (Matrix n n ℂ × ℝ)
  Q : Matrix n n ℂ
  hH : H.IsHermitian
  hQ : Q.IsHermitian
  hL : ∀ p ∈ L_gamma, p.1.IsHermitian
  h_gamma : ∀ p ∈ L_gamma, 0 ≤ p.2

def PreGeometricWESH.noetherCondition {n : Type} [Fintype n] [DecidableEq n] (W : PreGeometricWESH n) : Prop :=
  weshNoether W.H W.L_gamma W.Q

theorem PreGeometricWESH.noether_iff_commute {n : Type} [Fintype n] [DecidableEq n] (W : PreGeometricWESH n) :
    W.noetherCondition ↔ Commute W.H W.Q ∧ (∀ p ∈ W.L_gamma, p.2 > 0 → Commute p.1 W.Q) :=
  wesh_noether_iff_commute W.H W.L_gamma W.Q W.hH W.hQ W.hL W.h_gamma

theorem PreGeometricWESH.path_independence {n : Type} [Fintype n] [DecidableEq n]
    (W : PreGeometricWESH n) (rho : Matrix n n ℂ) (h : W.noetherCondition) :
    Matrix.trace (W.Q * weshGenerator W.H W.L_gamma rho) = 0 :=
  wesh_path_independence W.H W.L_gamma W.Q rho W.hL h

/-!
## PART III: Constraint-driven selection — CPT symmetry, quadratic dissipator

CPT symmetry requires even powers in the dissipator. Combined with collective
coherence scaling (N² stability), this uniquely selects the quadratic form L = T².

Notation convention:
- Dissipator degree = 2n (even for CPT)
- Coherence time τ_coh ∝ N^{2n}
- Stability requires 2n = 2, hence n = 1
- Therefore L = T^{2n} = T² (quadratic)
-/

section QuadraticSelection

/-- The index n in the even-power dissipator T^{2n}. Must satisfy n ≥ 1. -/
structure DissipatorIndex where
  n : ℕ
  hn : 1 ≤ n

/-- Dissipator degree = 2n (even for CPT symmetry). -/
def dissipator_degree (idx : DissipatorIndex) : ℕ := 2 * idx.n

/-- CPT-evenness: the degree 2n is automatically even. -/
theorem dissipator_degree_even (idx : DissipatorIndex) : Even (dissipator_degree idx) := by
  unfold dissipator_degree
  exact even_two_mul idx.n

/-- Coherence time exponent: τ_coh ∝ N^{2n}. -/
def coherence_exponent (idx : DissipatorIndex) : ℕ := 2 * idx.n

/-- Collective stability requires exponent = 2 (N² scaling). -/
def stability_exponent_nat : ℕ := 2

/-- Selection theorem: 2n = 2 implies n = 1, hence quadratic dissipator T². -/
theorem quadratic_selection (idx : DissipatorIndex)
    (h_stable : coherence_exponent idx = stability_exponent_nat) : idx.n = 1 := by
  unfold coherence_exponent stability_exponent_nat at h_stable
  omega

/-- The unique stable dissipator has degree 2. -/
theorem stable_dissipator_is_quadratic (idx : DissipatorIndex)
    (h_stable : coherence_exponent idx = stability_exponent_nat) :
    dissipator_degree idx = 2 := by
  unfold dissipator_degree
  rw [quadratic_selection idx h_stable]

/-- Alternative formulation: stability exponent as ℝ for comparison. -/
def stability_exponent_real : ℝ := 2

/-- Coherence exponent as ℝ. -/
def coherence_exponent_real (idx : DissipatorIndex) : ℝ := 2 * idx.n

/-- Real-valued selection: 2n = 2 implies n = 1. -/
theorem quadratic_selection_real (idx : DissipatorIndex)
    (h_stable : coherence_exponent_real idx = stability_exponent_real) : idx.n = 1 := by
  unfold coherence_exponent_real stability_exponent_real at h_stable
  have h : (2 : ℝ) * idx.n = 2 := h_stable
  have h2 : (idx.n : ℝ) = 1 := by linarith
  norm_cast at h2

end QuadraticSelection

/-!
## PART IV: The WESH master equation — Generator, causal kernel, Rényi-2, No-signaling

The WESH master equation governs evolution in the ordering parameter s.
It includes local dissipators D[T²], bilocal terms weighted by the causal kernel
γ(x,y) and the Rényi-2 correlator C(x,y), and enforces no-signaling via causality.
-/

section GenericOperatorAlgebra
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- Commutator [X, Y] = XY - YX. -/
def WESH_commutator (X Y : A) : A := X * Y - Y * X

/-- Anticommutator {X, Y} = XY + YX. -/
def WESH_anticommutator (X Y : A) : A := X * Y + Y * X

/-- Lindblad dissipator (Schrödinger picture). -/
def WESH_Lindblad (L ρ : A) : A :=
  L * ρ * star L - ((1 / 2 : ℂ) • WESH_anticommutator (star L * L) ρ)

/-- Lindblad adjoint (Heisenberg picture). -/
def WESH_Lindblad_Adjoint (L O : A) : A :=
  star L * O * L - ((1 / 2 : ℂ) • WESH_anticommutator (star L * L) O)

omit [StarRing A] in
lemma half_smul_add_self (a : A) : ((1 / 2 : ℂ) • (a + a)) = a := by
  rw [← two_smul ℂ a, smul_smul]
  have h : ((1 / 2 : ℂ) * (2 : ℂ)) = 1 := by norm_num
  rw [h, one_smul]

/-- If L is self-adjoint and commutes with O, then D†[L](O) = 0. -/
lemma WESH_Lindblad_Adjoint_eq_zero_of_selfAdjoint_of_comm
    (L O : A) (h_self : star L = L) (h_comm : L * O = O * L) :
    WESH_Lindblad_Adjoint L O = 0 := by
  unfold WESH_Lindblad_Adjoint WESH_anticommutator
  rw [h_self]
  have h1 : L * O * L = O * L * L := by rw [h_comm]
  have h2 : L * L * O = O * L * L := by calc L * L * O = L * (L * O) := by rw [mul_assoc]
    _ = L * (O * L) := by rw [h_comm]
    _ = (L * O) * L := by rw [mul_assoc]
    _ = (O * L) * L := by rw [h_comm]
    _ = O * L * L := rfl
  have h3 : O * (L * L) = O * L * L := (mul_assoc O L L).symm
  rw [h1, h2, h3]
  have : (1 / 2 : ℂ) • (O * L * L + O * L * L) = O * L * L := by
    rw [← two_smul ℂ (O * L * L), smul_smul]; norm_num
  rw [this, sub_self]

end GenericOperatorAlgebra

section Renyi2

/-- Normalized Rényi-2 correlator C(Ψ; x,y), with guard at P_x P_y = 1. -/
noncomputable def WESH_Renyi2_Correlator (P_xy P_x P_y : ℝ) : ℝ :=
  if P_x * P_y = 1 then 0 else max 0 (P_xy - P_x * P_y) / (1 - P_x * P_y)

/-- Rényi-2 deficit term. -/
noncomputable def WESH_Renyi2_Deficit (P_xy P_x P_y : ℝ) : ℝ :=
  (1 - P_xy) / (1 - P_x * P_y)

/-- Bounds 0 ≤ C ≤ 1 under purity constraints P ∈ [0,1]. -/
theorem WESH_Renyi2_Correlator_bounds (P_xy P_x P_y : ℝ)
    (_h_Pxy_nonneg : 0 ≤ P_xy) (h_Pxy : P_xy ≤ 1)
    (h_Px_nonneg : 0 ≤ P_x) (h_Px : P_x ≤ 1)
    (_h_Py_nonneg : 0 ≤ P_y) (h_Py : P_y ≤ 1) :
    0 ≤ WESH_Renyi2_Correlator P_xy P_x P_y ∧ WESH_Renyi2_Correlator P_xy P_x P_y ≤ 1 := by
  unfold WESH_Renyi2_Correlator
  by_cases hprod : P_x * P_y = 1
  · rw [if_pos hprod]; constructor <;> norm_num
  · rw [if_neg hprod]
    have hprod_le_Px : P_x * P_y ≤ P_x := by
      have h1 : P_x * P_y ≤ P_x * 1 := mul_le_mul_of_nonneg_left h_Py h_Px_nonneg
      calc P_x * P_y ≤ P_x * 1 := h1
        _ = P_x := by rw [mul_one]
    have hprod_le : P_x * P_y ≤ 1 := le_trans hprod_le_Px h_Px
    have hprod_lt : P_x * P_y < 1 := lt_of_le_of_ne hprod_le hprod
    have hden_pos : 0 < 1 - P_x * P_y := sub_pos.mpr hprod_lt
    have hden_nonneg : 0 ≤ 1 - P_x * P_y := le_of_lt hden_pos
    have hnum_nonneg : 0 ≤ max 0 (P_xy - P_x * P_y) := le_max_left 0 (P_xy - P_x * P_y)
    have hsub_le : P_xy - P_x * P_y ≤ 1 - P_x * P_y := sub_le_sub_right h_Pxy (P_x * P_y)
    have hnum_le : max 0 (P_xy - P_x * P_y) ≤ 1 - P_x * P_y := by apply max_le <;> [exact hden_nonneg; exact hsub_le]
    constructor
    · exact div_nonneg hnum_nonneg hden_nonneg
    · have h' : max 0 (P_xy - P_x * P_y) ≤ 1 * (1 - P_x * P_y) := by rw [one_mul]; exact hnum_le
      exact (div_le_iff₀ hden_pos).2 h'

/-- Identity: 1 - C = Deficit when P_xy ≥ P_x P_y. -/
theorem WESH_Renyi2_Deficit_Identity (P_xy P_x P_y : ℝ)
    (h_cond : P_xy ≥ P_x * P_y) (h_denom : 1 - P_x * P_y ≠ 0) :
    1 - WESH_Renyi2_Correlator P_xy P_x P_y = WESH_Renyi2_Deficit P_xy P_x P_y := by
  have hprod_ne : P_x * P_y ≠ 1 := by intro hEq; apply h_denom; rw [hEq]; exact sub_self 1
  unfold WESH_Renyi2_Correlator; rw [if_neg hprod_ne]; unfold WESH_Renyi2_Deficit
  have h_nonneg : 0 ≤ P_xy - P_x * P_y := sub_nonneg.mpr h_cond
  have h_max : max 0 (P_xy - P_x * P_y) = P_xy - P_x * P_y := max_eq_right h_nonneg
  rw [h_max]; field_simp [h_denom]; ring

end Renyi2

section MasterEquation
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- Master equation generator (Eq 2.11): dρ/ds = -i[H_eff, ρ] + local + bilocal. -/
noncomputable def WESH_MasterEquation (ρ H_eff : A) (T : WESH_SpacetimePoint → A) (nu : ℝ)
    (gamma : WESH_SpacetimePoint → WESH_SpacetimePoint → ℝ)
    (C : WESH_SpacetimePoint → WESH_SpacetimePoint → ℝ)
    (points : Finset WESH_SpacetimePoint) : A :=
  let hamiltonianTerm : A := (-Complex.I : ℂ) • (H_eff * ρ - ρ * H_eff)
  let localDissipatorTerm : A := (nu : ℂ) • (points.sum (fun x => WESH_Lindblad (T x ^ 2) ρ))
  let bilocalDissipatorTerm : A := points.sum (fun x => points.sum (fun y =>
    ((gamma x y * C x y : ℝ) : ℂ) • WESH_Lindblad ((T x ^ 2) - (T y ^ 2)) ρ))
  hamiltonianTerm + localDissipatorTerm + bilocalDissipatorTerm

/-- Spacelike bilocal terms vanish (causality). -/
theorem WESH_MasterEquation_spacelike_terms_vanish (ρ : A) (T : WESH_SpacetimePoint → A)
    (gamma_0 N xi : ℝ) (C : WESH_SpacetimePoint → WESH_SpacetimePoint → ℝ)
    (x y : WESH_SpacetimePoint) (h_spacelike : ¬ WESH_is_causal x y) :
    (WESH_gamma_kernel gamma_0 N xi x y * C x y : ℝ) • WESH_Lindblad (A := A) ((T x ^ 2) - (T y ^ 2)) ρ = 0 := by
  have hγ : WESH_gamma_kernel gamma_0 N xi x y = 0 := WESH_gamma_spacelike_vanishing gamma_0 N xi x y h_spacelike
  rw [hγ, zero_mul, zero_smul]

/-- Adjoint generator L†[Q] for Heisenberg picture. -/
noncomputable def WESH_Adjoint_Generator (Q H_eff : A) (T : WESH_SpacetimePoint → A) (nu : ℝ)
    (gamma : WESH_SpacetimePoint → WESH_SpacetimePoint → ℝ)
    (C : WESH_SpacetimePoint → WESH_SpacetimePoint → ℝ)
    (points : Finset WESH_SpacetimePoint) : A :=
  let hamiltonianTerm : A := (-Complex.I : ℂ) • (H_eff * Q - Q * H_eff)
  let localDissipatorTerm : A := (nu : ℂ) • (points.sum (fun x => WESH_Lindblad_Adjoint (T x ^ 2) Q))
  let bilocalDissipatorTerm : A := points.sum (fun x => points.sum (fun y =>
    ((gamma x y * C x y : ℝ) : ℂ) • WESH_Lindblad_Adjoint ((T x ^ 2) - (T y ^ 2)) Q))
  hamiltonianTerm + localDissipatorTerm + bilocalDissipatorTerm

/-- Noether conservation: if Q commutes with H_eff and all T(x)², then L†[Q] = 0. -/
theorem WESH_Noether_Conservation (Q H_eff : A) (T : WESH_SpacetimePoint → A) (nu : ℝ)
    (gamma C : WESH_SpacetimePoint → WESH_SpacetimePoint → ℝ) (points : Finset WESH_SpacetimePoint)
    (h_comm_H : H_eff * Q = Q * H_eff)
    (h_comm_T : ∀ x : WESH_SpacetimePoint, (T x ^ 2) * Q = Q * (T x ^ 2))
    (h_herm_T : ∀ x : WESH_SpacetimePoint, star (T x) = T x) :
    WESH_Adjoint_Generator Q H_eff T nu gamma C points = 0 := by
  classical
  unfold WESH_Adjoint_Generator
  have hHam : (-Complex.I : ℂ) • (H_eff * Q - Q * H_eff) = 0 := by
    have : H_eff * Q - Q * H_eff = 0 := sub_eq_zero.mpr h_comm_H; rw [this, smul_zero]
  have hLocalPoint : ∀ x : WESH_SpacetimePoint, WESH_Lindblad_Adjoint (T x ^ 2) Q = 0 := by
    intro x
    have h_self : star (T x ^ 2) = (T x ^ 2) := by rw [star_pow, h_herm_T x]
    have h_comm : (T x ^ 2) * Q = Q * (T x ^ 2) := h_comm_T x
    exact WESH_Lindblad_Adjoint_eq_zero_of_selfAdjoint_of_comm (T x ^ 2) Q h_self h_comm
  have hLocalSum : points.sum (fun x => WESH_Lindblad_Adjoint (T x ^ 2) Q) = 0 :=
    Finset.sum_eq_zero fun x _ => hLocalPoint x
  have hLocal : (nu : ℂ) • points.sum (fun x => WESH_Lindblad_Adjoint (T x ^ 2) Q) = 0 := by
    rw [hLocalSum, smul_zero]
  have hBilocalPoint : ∀ x y : WESH_SpacetimePoint, WESH_Lindblad_Adjoint ((T x ^ 2) - (T y ^ 2)) Q = 0 := by
    intro x y
    have h_self_x : star (T x ^ 2) = (T x ^ 2) := by rw [star_pow, h_herm_T x]
    have h_self_y : star (T y ^ 2) = (T y ^ 2) := by rw [star_pow, h_herm_T y]
    have h_self : star ((T x ^ 2) - (T y ^ 2)) = (T x ^ 2) - (T y ^ 2) := by rw [star_sub, h_self_x, h_self_y]
    have hx : (T x ^ 2) * Q = Q * (T x ^ 2) := h_comm_T x
    have hy : (T y ^ 2) * Q = Q * (T y ^ 2) := h_comm_T y
    have h_comm : ((T x ^ 2) - (T y ^ 2)) * Q = Q * ((T x ^ 2) - (T y ^ 2)) := by rw [sub_mul, mul_sub, hx, hy]
    exact WESH_Lindblad_Adjoint_eq_zero_of_selfAdjoint_of_comm ((T x ^ 2) - (T y ^ 2)) Q h_self h_comm
  have hBilocalSumInner : ∀ x : WESH_SpacetimePoint,
      points.sum (fun y => ((gamma x y * C x y : ℝ) : ℂ) • WESH_Lindblad_Adjoint ((T x ^ 2) - (T y ^ 2)) Q) = 0 :=
    fun x => Finset.sum_eq_zero fun y _ => by rw [hBilocalPoint x y, smul_zero]
  have hBilocalSum : points.sum (fun x => points.sum (fun y =>
      ((gamma x y * C x y : ℝ) : ℂ) • WESH_Lindblad_Adjoint ((T x ^ 2) - (T y ^ 2)) Q)) = 0 :=
    Finset.sum_eq_zero fun x _ => hBilocalSumInner x
  rw [hHam, hLocal, hBilocalSum]; simp only [add_zero]

end MasterEquation

section NoSignaling
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- Observable O commutes with local clock T at w. -/
def WESH_CommutesWithTAt (O : A) (T : WESH_SpacetimePoint → A) (w : WESH_SpacetimePoint) : Prop :=
  O * T w = T w * O ∧ O * (T w ^ 2) = (T w ^ 2) * O

/-- No-signaling: bilocal dissipator vanishes for spacelike-supported observables. -/
theorem WESH_NoSignaling_Heisenberg (O : A) (T : WESH_SpacetimePoint → A) (z : WESH_SpacetimePoint)
    (h_herm_T : ∀ w : WESH_SpacetimePoint, star (T w) = T w)
    (h_comm_spacelike : ∀ w : WESH_SpacetimePoint, ¬ WESH_is_causal z w → ¬ WESH_is_causal w z → WESH_CommutesWithTAt O T w)
    (x y : WESH_SpacetimePoint)
    (h_x_spacelike : ¬ WESH_is_causal z x ∧ ¬ WESH_is_causal x z)
    (h_y_spacelike : ¬ WESH_is_causal z y ∧ ¬ WESH_is_causal y z) :
    WESH_Lindblad_Adjoint ((T x ^ 2) - (T y ^ 2)) O = 0 := by
  have hx : WESH_CommutesWithTAt O T x := h_comm_spacelike x h_x_spacelike.1 h_x_spacelike.2
  have hy : WESH_CommutesWithTAt O T y := h_comm_spacelike y h_y_spacelike.1 h_y_spacelike.2
  have hx2 : (T x ^ 2) * O = O * (T x ^ 2) := Eq.symm hx.2
  have hy2 : (T y ^ 2) * O = O * (T y ^ 2) := Eq.symm hy.2
  have hcomm : ((T x ^ 2) - (T y ^ 2)) * O = O * ((T x ^ 2) - (T y ^ 2)) := by rw [sub_mul, mul_sub, hx2, hy2]
  have h_self_x : star (T x ^ 2) = (T x ^ 2) := by rw [star_pow, h_herm_T x]
  have h_self_y : star (T y ^ 2) = (T y ^ 2) := by rw [star_pow, h_herm_T y]
  have hself : star ((T x ^ 2) - (T y ^ 2)) = (T x ^ 2) - (T y ^ 2) := by rw [star_sub, h_self_x, h_self_y]
  exact WESH_Lindblad_Adjoint_eq_zero_of_selfAdjoint_of_comm ((T x ^ 2) - (T y ^ 2)) O hself hcomm

end NoSignaling

section CCR
variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Minisuperspace CCR: [T, P_T] = iħ·1. -/
def WESH_Minisuperspace_CCR (T P_T : A) (hbar : ℝ) : Prop :=
  T * P_T - P_T * T = (Complex.I * (hbar : ℂ)) • (1 : A)

/-- Minisuperspace total Hamiltonian H_tot = H_universe + P_T. -/
def WESH_Minisuperspace_H_tot (H_universe P_T : A) : A := H_universe + P_T

/-- If [T, H_universe] = 0, then [T, H_tot] = iħ. -/
theorem WESH_Minisuperspace_Time_Commutator (T P_T H_universe : A) (hbar : ℝ)
    (h_ccr : WESH_Minisuperspace_CCR T P_T hbar)
    (h_comm : T * H_universe = H_universe * T) :
    let H_tot := WESH_Minisuperspace_H_tot H_universe P_T
    T * H_tot - H_tot * T = (Complex.I * (hbar : ℂ)) • (1 : A) := by
  dsimp [WESH_Minisuperspace_H_tot]
  have hsplit : T * (H_universe + P_T) - (H_universe + P_T) * T = (T * H_universe - H_universe * T) + (T * P_T - P_T * T) := by
    rw [mul_add, add_mul]; exact add_sub_add_comm (T * H_universe) (T * P_T) (H_universe * T) (P_T * T)
  rw [hsplit]
  have hH : T * H_universe - H_universe * T = 0 := sub_eq_zero.mpr h_comm
  rw [hH, zero_add]; exact h_ccr

/-- Local CCR: [T(x), Π_T(y)] = iħ δ_{xy}. -/
def WESH_Local_CCR (T Pi_T : WESH_SpacetimePoint → A) (hbar : ℝ) : Prop :=
  ∀ x y, T x * Pi_T y - Pi_T y * T x = if x = y then (Complex.I * (hbar : ℂ)) • (1 : A) else 0

/-- Momentum identification Π_T(x) = -H_cal(x). -/
def WESH_Local_Momentum_Identification (Pi_T H_cal : WESH_SpacetimePoint → A) : Prop :=
  ∀ x, Pi_T x = - H_cal x

/-- Then [T(x), H_cal(y)] = -iħ δ_{xy}. -/
theorem WESH_Local_Time_Translation_Generator (T Pi_T H_cal : WESH_SpacetimePoint → A) (hbar : ℝ)
    (h_ccr : WESH_Local_CCR T Pi_T hbar)
    (h_ident : WESH_Local_Momentum_Identification Pi_T H_cal) :
    ∀ x y, T x * H_cal y - H_cal y * T x = if x = y then -((Complex.I * (hbar : ℂ)) • (1 : A)) else 0 := by
  intro x y
  have h0 : T x * Pi_T y - Pi_T y * T x = if x = y then (Complex.I * (hbar : ℂ)) • (1 : A) else 0 := h_ccr x y
  have hy : Pi_T y = -H_cal y := h_ident y
  have h1 : T x * (-H_cal y) - (-H_cal y) * T x = if x = y then (Complex.I * (hbar : ℂ)) • (1 : A) else 0 := by rw [hy] at h0; exact h0
  have h2 : T x * (-H_cal y) - (-H_cal y) * T x = - (T x * H_cal y - H_cal y * T x) := by rw [mul_neg, neg_mul, sub_eq_add_neg, neg_neg, sub_eq_add_neg, neg_add, neg_neg]
  have h3 : - (T x * H_cal y - H_cal y * T x) = if x = y then (Complex.I * (hbar : ℂ)) • (1 : A) else 0 := by rw [← h2]; exact h1
  have h4 : (T x * H_cal y - H_cal y * T x) = - (if x = y then (Complex.I * (hbar : ℂ)) • (1 : A) else 0) := (neg_eq_iff_eq_neg).1 h3
  by_cases hxy : x = y
  · rw [if_pos hxy] at h4; rw [if_pos hxy]; exact h4
  · rw [if_neg hxy] at h4; rw [neg_zero] at h4; rw [if_neg hxy]; exact h4

end CCR

/-!
## PART V: Bootstrap and Eigentimes — Time-production functional Γ, monotonicity

The bootstrap mechanism is constitutive rather than tautological when dealing with
chronogenesis. Eigentimes emerge as discrete events marking the arrow of time.
The time-production functional Γ[Ψ] measures the rate of eigentime activation.
-/

open Matrix Complex BigOperators

variable {n : Type} [Fintype n] [DecidableEq n]
variable {Site : Type} [Fintype Site] [DecidableEq Site]

/-- Dimensionless time field T̃(x) = T(x)/τ_s. -/
noncomputable def T_tilde (T : Site → Matrix n n ℂ) (tau_s : ℝ) (x : Site) : Matrix n n ℂ :=
  (1 / tau_s) • T x

/-- Local jump operator L_x = T̃(x)². -/
noncomputable def L_local (T : Site → Matrix n n ℂ) (tau_s : ℝ) (x : Site) : Matrix n n ℂ :=
  (T_tilde T tau_s x) ^ 2

/-- Bilocal jump operator L_{xy} = T̃(x)² - T̃(y)². -/
noncomputable def L_bilocal (T : Site → Matrix n n ℂ) (tau_s : ℝ) (x y : Site) : Matrix n n ℂ :=
  (T_tilde T tau_s x) ^ 2 - (T_tilde T tau_s y) ^ 2

set_option linter.unusedSectionVars false in
/-- L_bilocal vanishes on diagonal: L_{xx} = 0. No self-interaction. -/
theorem L_bilocal_self (T : Site → Matrix n n ℂ) (tau_s : ℝ) (x : Site) :
    L_bilocal T tau_s x x = 0 := by
  unfold L_bilocal
  simp only [sub_self]

set_option linter.unusedSectionVars false in
/-- L_bilocal is antisymmetric: L_{xy} = -L_{yx}. Conservation of redistributed time. -/
theorem L_bilocal_swap (T : Site → Matrix n n ℂ) (tau_s : ℝ) (x y : Site) :
    L_bilocal T tau_s x y = -L_bilocal T tau_s y x := by
  unfold L_bilocal
  simp only [neg_sub]

/-- Normalized Rényi-2 correlator value (Matrix version). -/
noncomputable def renyi2_val (P_xy P_x P_y : ℝ) : ℝ :=
  if 1 - P_x * P_y = 0 then 0 else max (P_xy - P_x * P_y) 0 / (1 - P_x * P_y)

/-- WESH generator (Eq 2.11) instantaneous form. -/
noncomputable def wesh_generator_instantaneous
  (T : Site → Matrix n n ℂ) (tau_s : ℝ)
  (H_eff : Matrix n n ℂ)
  (nu : ℝ)
  (gamma : Site → Site → ℝ)
  (C_vals : Site → Site → ℝ)
  (rho : Matrix n n ℂ) : Matrix n n ℂ :=
  let term_H := (-Complex.I) • (H_eff * rho - rho * H_eff)
  let term_local := (nu : ℂ) • (Finset.univ.sum fun x => lindbladAdjoint (L_local T tau_s x) rho)
  let term_bilocal := Finset.univ.sum fun x => Finset.univ.sum fun y =>
    (gamma x y * C_vals x y : ℂ) • lindbladAdjoint (L_bilocal T tau_s x y) rho
  term_H + term_local + term_bilocal

/-- Positive semidefinite for complex matrices. -/
def IsPSD (M : Matrix n n ℂ) : Prop :=
  M.IsHermitian ∧ ∀ x : n → ℂ, 0 ≤ (dotProduct (star x) (M *ᵥ x)).re

/-- Time-production functional Γ[Ψ] (Eq 2.27).
    
    NOTE: The full development of physical time emergence t(s) = ∫₀ˢ Γ[Ψ(s')] ds',
    the Law of Large Numbers for eigentime counts, and the survival probability
    formalism are developed in AppendixB.lean. -/
noncomputable def Gamma_functional (T : Site → Matrix n n ℂ) (tau_s : ℝ) (rho : Matrix n n ℂ)
    (nu : ℝ) (gamma : Site → Site → ℝ) (C_vals : Site → Site → ℝ) (tau_Eig : ℝ) : ℝ :=
  let term_local := nu * (Finset.univ.sum fun x => (Matrix.trace ((L_local T tau_s x) * rho * (L_local T tau_s x))).re)
  let term_bilocal := Finset.univ.sum fun x => Finset.univ.sum fun y =>
    gamma x y * C_vals x y * (Matrix.trace ((L_bilocal T tau_s x y) ^ 2 * rho)).re
  tau_Eig * (term_local + term_bilocal)

omit [DecidableEq Site] in
/-- Lemma 2.7: Monotonicity of t (Γ ≥ 0). -/
theorem Gamma_nonneg (T : Site → Matrix n n ℂ) (tau_s : ℝ) (rho : Matrix n n ℂ) (h_rho : IsPSD rho)
    (nu : ℝ) (h_nu : 0 ≤ nu) (gamma : Site → Site → ℝ) (h_gamma : ∀ x y, 0 ≤ gamma x y)
    (C_vals : Site → Site → ℝ) (h_C : ∀ x y, 0 ≤ C_vals x y)
    (tau_Eig : ℝ) (h_tau : 0 ≤ tau_Eig) (hT : ∀ x, (T x).IsHermitian) :
    0 ≤ Gamma_functional T tau_s rho nu gamma C_vals tau_Eig := by
  have h_trace_nonneg : ∀ (L : Matrix n n ℂ), L.IsHermitian → 0 ≤ (L * rho * L).trace.re := by
    intro L hL
    have h_pos_semidef : IsPSD (L * rho * L) := by
      constructor
      · simp_all +decide [Matrix.IsHermitian, Matrix.mul_assoc]; rw [h_rho.1]
      · intro x; have := h_rho.2 (L.mulVec x); simp_all +decide [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
        simp_all +decide [Matrix.mul_assoc, Matrix.star_mulVec]; rwa [hL.eq] at this
    have h_trace_nonneg : ∀ (A : Matrix n n ℂ), IsPSD A → 0 ≤ A.trace.re := by
      intros A hA; exact (by
        have := hA.2
        convert Finset.sum_nonneg fun i _ => this (Pi.single i 1) using 1
        simp +decide [Matrix.trace, dotProduct]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_eq_single i] <;> aesop)
    exact h_trace_nonneg _ h_pos_semidef
  refine' mul_nonneg h_tau _
  refine' add_nonneg (mul_nonneg h_nu (Finset.sum_nonneg fun x _ => h_trace_nonneg _ _)) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (h_gamma x y) (h_C x y)) _)
  · unfold L_local; simp_all +decide [Matrix.IsHermitian]; unfold T_tilde; aesop
  · convert h_trace_nonneg (L_bilocal T tau_s x y) _ using 1
    · rw [sq, mul_assoc, Matrix.trace_mul_comm]
    · unfold L_bilocal; simp_all +decide [Matrix.IsHermitian, Matrix.mul_assoc]; unfold T_tilde; simp +decide [hT]

open MeasureTheory intervalIntegral Real

/-- Lemma 2.6: Eigentime activation on chronogenetic segments. -/
theorem eigentime_activation (Gamma : ℝ → ℝ) (h_cont : Continuous Gamma) (h_pos : ∀ s, 0 < Gamma s)
    (s0 delta : ℝ) (h_delta : 0 < delta) :
    Real.exp (- intervalIntegral Gamma s0 (s0 + delta) MeasureTheory.volume) < 1 := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  norm_num +zetaDelta at *
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · simp +decide [Function.support, ne_of_gt (h_pos _)]; bound
  · exact Filter.Eventually.of_forall fun x => le_of_lt (h_pos x)
  · exact h_cont.integrableOn_Ioc

/-!
## PART VI: Foundational consistency — α=2 selection, N² scaling, G→0 decoupling

The framework's consistency requires: (1) selection of α=2 via collective coherence
scaling, (2) compatibility with N² stability, and (3) smooth decoupling in the G→0
limit where ξ → 0 and the theory reduces to standard quantum mechanics.
-/

open Real

/-- Lemma 2.8 (Part 2): Selection of α=2 via scaling balance. -/
theorem alpha_selection_scaling (gamma_0 tau_corr V_xi : ℝ) (_h_pos : 0 < gamma_0 ∧ 0 < tau_corr ∧ 0 < V_xi)
    (alpha : ℝ) (C : ℝ) (hC : 0 < C)
    (h_balance : ∀ N : ℝ, 1 < N →
      let nu := gamma_0 * V_xi / N^2
      let tau_Eig := 1 / nu
      let mu := tau_corr / tau_Eig
      let tau_coh := N ^ alpha
      mu * tau_coh = C) : alpha = 2 := by
  have := h_balance 2 (by norm_num); have := h_balance 4 (by norm_num); norm_num at *
  have h_alpha : (2 : ℝ) ^ (alpha - 2) = 1 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]; norm_num
    rw [show (4 : ℝ) ^ alpha = 2 ^ alpha * 2 ^ alpha by rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num] at this
    ring_nf at *; nlinarith [mul_pos _h_pos.1 _h_pos.2.2]
  norm_num [Real.rpow_def_of_pos] at h_alpha; linarith

open Real Filter Topology

/-- Proposition 2.9: Decoupling in the G → 0 limit (ν → 0). -/
theorem decoupling_limit (xi : ℝ → ℝ) (gamma_0 : ℝ → ℝ) (V_xi : ℝ → ℝ) (nu : ℝ → ℝ)
    (h_xi : ∃ c1 > 0, ∀ G > 0, xi G = c1 * sqrt G)
    (h_gamma : ∃ c2 > 0, ∀ G > 0, gamma_0 G = c2 / sqrt G)
    (h_V : ∃ c3 > 0, ∀ G > 0, V_xi G = c3 * (xi G) ^ 4)
    (h_nu : ∃ c4 > 0, ∀ G > 0, nu G = c4 * gamma_0 G * V_xi G) :
    Tendsto nu (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨c3, hc3, hV_xi⟩ := h_V; have := h_nu; obtain ⟨c4, hc4, hn⟩ := this
  simp_all +decide [mul_assoc, mul_left_comm, div_eq_mul_inv]
  have h_nu_simplified : ∀ G > 0, nu G = c3 * c4 * h_gamma.choose * h_xi.choose ^ 4 * G ^ (3 / 2 : ℝ) := by
    intro G hG; rw [hn G hG, h_gamma.choose_spec.2 G hG, h_xi.choose_spec.2 G hG]; ring_nf
    rw [show (Real.sqrt G) ^ 4 = (Real.sqrt G ^ 2) ^ 2 by ring, Real.sq_sqrt hG.le]; ring_nf
    rw [show (3 / 2 : ℝ) = 2 - 1 / 2 by norm_num, Real.sqrt_eq_rpow, Real.rpow_sub hG]; norm_num; ring_nf
  rw [Filter.tendsto_congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [h_nu_simplified x hx])]
  exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by exact Continuous.mul continuous_const (continuous_id'.rpow_const <| by norm_num)) _ _ <| by norm_num)

/-- Fundamental parameters and scales (Table 1). -/
structure WESHParameters where
  (hbar c G : ℝ)
  (m_T : ℝ)
  (xi : ℝ)
  (gamma_0 : ℝ)
  (N : ℝ)
  (nu : ℝ)
  (tau_Eig : ℝ)
  (tau_corr : ℝ)
  (tau_coh : ℝ)
  (alpha : ℝ)
  (k : ℝ)

/-- Consistency relations for WESH parameters. -/
def WESH_consistent (p : WESHParameters) : Prop :=
  p.xi = p.hbar / (p.m_T * p.c) ∧
  p.tau_Eig = 1 / p.nu ∧
  p.tau_corr = p.xi / p.c ∧
  p.tau_coh = p.N ^ p.alpha ∧
  p.alpha = 2

/-- Existence of consistent parameters with non-degenerate witness.
    All physical parameters set to 1, demonstrating non-trivial consistency. -/
theorem wesh_parameters_exist : ∃ p : WESHParameters, WESH_consistent p := by
  refine ⟨⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1⟩, ?_⟩
  unfold WESH_consistent
  norm_num


end
